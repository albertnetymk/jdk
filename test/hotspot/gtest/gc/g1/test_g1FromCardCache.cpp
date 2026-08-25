/*
 * Copyright (c) 2026, Oracle and/or its affiliates. All rights reserved.
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
 */

#include "gc/g1/g1FromCardCache.hpp"
#include "unittest.hpp"

TEST(G1FromCardCache, hit_and_miss) {
  const uintptr_t source_card = 64;
  const uint cardset_a = 3;
  const uint cardset_b = 13;
  const uint cardset_high = 1024;

  G1FromCardCache cache;

  EXPECT_FALSE(cache.contains_or_add(source_card, cardset_a));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_a));

  // Retain multiple cardsets for the same source_card.
  EXPECT_FALSE(cache.contains_or_add(source_card, cardset_b));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_a));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_b));

  // A group id is not an array index.
  EXPECT_FALSE(cache.contains_or_add(source_card, cardset_high));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_high));
}

TEST(G1FromCardCache, source_card_transition) {
  const uintptr_t source_card_a = 2;
  const uintptr_t source_card_b = 3;
  const uint cardset_id = 17;

  G1FromCardCache cache;

  EXPECT_FALSE(cache.contains_or_add(source_card_a, cardset_id));
  EXPECT_TRUE(cache.contains_or_add(source_card_a, cardset_id));

  // Discard previous source_card data.
  EXPECT_FALSE(cache.contains_or_add(source_card_b, cardset_id));
  EXPECT_TRUE(cache.contains_or_add(source_card_b, cardset_id));

  // Verify that it was discarded before.
  EXPECT_FALSE(cache.contains_or_add(source_card_a, cardset_id));
}

TEST(G1FromCardCache, cache_reset) {
  const uintptr_t source_card = 17;
  const uint cardset_id = 17;

  G1FromCardCache cache;

  EXPECT_FALSE(cache.contains_or_add(source_card, cardset_id));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_id));

  cache.reset();

  EXPECT_FALSE(cache.contains_or_add(source_card, cardset_id));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_id));
}

TEST(G1FromCardCache, colliding_cardsets) {
  const uintptr_t source_card = 8;
  const uint cardset_single = 2;
  // These all map to the same entry of the direct-mapped table.
  const uint cardset_a = 1;
  const uint cardset_b = 32;
  const uint cardset_c = 67;

  G1FromCardCache cache;

  EXPECT_FALSE(cache.contains_or_add(source_card, cardset_single));
  EXPECT_FALSE(cache.contains_or_add(source_card, cardset_a));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_a));

  // Collides with cardset_a, so it lands in the overflow slot.
  EXPECT_FALSE(cache.contains_or_add(source_card, cardset_b));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_b));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_a));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_single));

  // A third colliding id evicts the overflow slot. The evicted id is then
  // reported as absent again, which only costs a redundant insertion.
  EXPECT_FALSE(cache.contains_or_add(source_card, cardset_c));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_c));
  EXPECT_FALSE(cache.contains_or_add(source_card, cardset_b));

  // Eviction must not disturb the other tiers.
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_a));
  EXPECT_TRUE(cache.contains_or_add(source_card, cardset_single));
}

TEST(G1FromCardCache, more_cardsets_than_entries) {
  const uintptr_t source_card = 4096;
  const uint num_cardsets = 128;

  G1FromCardCache cache;

  for (uint cardset_id = 1; cardset_id <= num_cardsets; cardset_id++) {
    // An id that has not been seen yet must never be reported as present.
    EXPECT_FALSE(cache.contains_or_add(source_card, cardset_id));
    // Consecutive references to the same cardset are always deduped, no matter
    // which tier ended up holding the id.
    EXPECT_TRUE(cache.contains_or_add(source_card, cardset_id));
  }
}

#ifdef ASSERT

TEST_VM_ASSERT_MSG(G1FromCardCache, empty_id,
                   ".*must be a valid cardset id") {
  G1FromCardCache cache;
  cache.contains_or_add(1, G1FromCardCache::EmptyId);
}

#endif // ASSERT
