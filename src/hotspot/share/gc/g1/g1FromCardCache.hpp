/*
 * Copyright (c) 2013, 2026, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#ifndef SHARE_GC_G1_G1FROMCARDCACHE_HPP
#define SHARE_GC_G1_G1FROMCARDCACHE_HPP

#include "utilities/debug.hpp"
#include "utilities/globalDefinitions.hpp"

// G1FromCardCache remembers which destination cardsets have been
// encountered while a worker scans the current source card.
//
// Lookup is split into three tiers: a single-id fast path for the common case of
// a source card referencing only one cardset, a direct-mapped table, and one
// overflow slot for ids colliding in that table. Ids that collide beyond the
// overflow slot are reported as not present, so the cache is not an exact filter.
// That is always safe: the pair is simply handed to the cardset again, which
// dedups on its own. In exchange, lookup is constant time and the footprint is
// independent of the maximum number of references per card.
class G1FromCardCache {
public:
  // Cardset ids are never zero, so zero marks an unused entry. This is asserted
  // against the actual cardset id space in G1HeapRegionRemSet::add_reference.
  static constexpr uint EmptyId = 0;

private:
  static constexpr uint IndexShift = 5;
  static constexpr uint NumEntries = 1u << IndexShift;

  uintptr_t _source_card;
  // Tier 1: the sole cardset id seen for _source_card, or EmptyId.
  uint _single_cardset_id;
  // Tier 3: one cardset id that collided in _cardset_ids, or EmptyId.
  uint _overflow_cardset_id;
  // Tier 2: direct-mapped table of seen cardset ids. Occupancy is tracked in a
  // separate bitmask rather than with an EmptyId marker per entry so that
  // reset() stays constant time.
  uint _cardset_ids[NumEntries];
  uint _occupied_bits;

  static_assert(sizeof(_occupied_bits) * BitsPerByte >= NumEntries,
                "_occupied_bits must have one bit per entry");

  NONCOPYABLE(G1FromCardCache);

  static uint slot_index_for(uint cardset_id) {
    uint hash = cardset_id ^ (cardset_id >> IndexShift);
    return hash & (NumEntries - 1);
  }

  // Tier 1 is filled first, so an unused tier 1 means nothing is recorded at all.
  bool is_empty() const {
    return _single_cardset_id == EmptyId;
  }

  void start_card(uintptr_t source_card) {
    _source_card = source_card;
    reset();
  }

  bool contains_or_add(uint cardset_id) {
    if (_single_cardset_id == cardset_id) {
      return true;
    }
    if (is_empty()) {
      _single_cardset_id = cardset_id;
      return false;
    }

    uint slot = slot_index_for(cardset_id);
    uint slot_bit = 1u << slot;
    if ((_occupied_bits & slot_bit) == 0) {
      _cardset_ids[slot] = cardset_id;
      _occupied_bits |= slot_bit;
      return false;
    }
    if (_cardset_ids[slot] == cardset_id) {
      return true;
    }

    if (_overflow_cardset_id == cardset_id) {
      return true;
    }
    _overflow_cardset_id = cardset_id;
    return false;
  }

public:
  G1FromCardCache() {
    start_card(0);
  }

  // Discard the state associated with the _source_card. This must be called before
  // a worker begins a new refinement or rebuild scan and after a rebuild yield.
  void reset() {
    _single_cardset_id = EmptyId;
    _overflow_cardset_id = EmptyId;
    _occupied_bits = 0;
  }

  // Returns true if cardset_id has already been encountered while
  // scanning source_card. Otherwise, records the id and returns false.
  bool contains_or_add(uintptr_t source_card, uint cardset_id) {
    assert(cardset_id != EmptyId, "must be a valid cardset id");

    if (is_empty() || _source_card != source_card) {
      start_card(source_card);
    }
    return contains_or_add(cardset_id);
  }
};

#endif // SHARE_GC_G1_G1FROMCARDCACHE_HPP
