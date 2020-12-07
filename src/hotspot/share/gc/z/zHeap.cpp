/*
 * Copyright (c) 2015, 2021, Oracle and/or its affiliates. All rights reserved.
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

#include "precompiled.hpp"
#include "gc/shared/locationPrinter.hpp"
#include "gc/shared/tlab_globals.hpp"
#include "gc/z/zAddress.inline.hpp"
#include "gc/z/zArray.inline.hpp"
#include "gc/z/zGlobals.hpp"
#include "gc/z/zHeap.inline.hpp"
#include "gc/z/zHeapIterator.hpp"
#include "gc/z/zHeuristics.hpp"
#include "gc/z/zMark.inline.hpp"
#include "gc/z/zPage.inline.hpp"
#include "gc/z/zPageTable.inline.hpp"
#include "gc/z/zRelocationSet.inline.hpp"
#include "gc/z/zRelocationSetSelector.inline.hpp"
#include "gc/z/zResurrection.hpp"
#include "gc/z/zStat.hpp"
#include "gc/z/zThread.inline.hpp"
#include "gc/z/zVerify.hpp"
#include "gc/z/zWorkers.inline.hpp"
#include "logging/log.hpp"
#include "memory/iterator.hpp"
#include "memory/metaspaceUtils.hpp"
#include "memory/resourceArea.hpp"
#include "prims/jvmtiTagMap.hpp"
#include "runtime/handshake.hpp"
#include "runtime/safepoint.hpp"
#include "runtime/thread.hpp"
#include "utilities/debug.hpp"

static const ZStatCounter ZCounterUndoPageAllocation("Memory", "Undo Page Allocation", ZStatUnitOpsPerSecond);
static const ZStatCounter ZCounterOutOfMemory("Memory", "Out Of Memory", ZStatUnitOpsPerSecond);

ZHeap* ZHeap::_heap = NULL;

ZHeap::ZHeap() :
    _workers(),
    _object_allocator(),
    _page_allocator(&_workers, MinHeapSize, InitialHeapSize, MaxHeapSize),
    _page_table(),
    _forwarding_table(),
    _mark(&_workers, &_page_table),
    _reference_processor(&_workers),
    _weak_roots_processor(&_workers),
    _relocate(&_workers),
    _relocation_set(&_workers),
    _unload(&_workers),
    _serviceability(min_capacity(), max_capacity()) {
  // Install global heap instance
  assert(_heap == NULL, "Already initialized");
  _heap = this;

  // Update statistics
  ZStatHeap::set_at_initialize(_page_allocator.stats());
}

bool ZHeap::is_initialized() const {
  return _page_allocator.is_initialized() && _mark.is_initialized();
}

size_t ZHeap::min_capacity() const {
  return _page_allocator.min_capacity();
}

size_t ZHeap::max_capacity() const {
  return _page_allocator.max_capacity();
}

size_t ZHeap::soft_max_capacity() const {
  return _page_allocator.soft_max_capacity();
}

size_t ZHeap::capacity() const {
  return _page_allocator.capacity();
}

size_t ZHeap::used() const {
  return _page_allocator.used();
}

size_t ZHeap::used_high() const {
  return _page_allocator.used_high();
}

size_t ZHeap::unused() const {
  return _page_allocator.unused();
}

size_t ZHeap::tlab_capacity() const {
  return capacity();
}

size_t ZHeap::tlab_used() const {
  return _object_allocator.used();
}

size_t ZHeap::max_tlab_size() const {
  return ZObjectSizeLimitSmall;
}

size_t ZHeap::unsafe_max_tlab_alloc() const {
  size_t size = _object_allocator.remaining();

  if (size < MinTLABSize) {
    // The remaining space in the allocator is not enough to
    // fit the smallest possible TLAB. This means that the next
    // TLAB allocation will force the allocator to get a new
    // backing page anyway, which in turn means that we can then
    // fit the largest possible TLAB.
    size = max_tlab_size();
  }

  return MIN2(size, max_tlab_size());
}

bool ZHeap::is_in(uintptr_t addr) const {
  // An address is considered to be "in the heap" if it points into
  // the allocated part of a page, regardless of which heap view is
  // used. Note that an address with the finalizable metadata bit set
  // is not pointing into a heap view, and therefore not considered
  // to be "in the heap".

  if (ZAddress::is_in(addr)) {
    const ZPage* const page = _page_table.get(addr);
    if (page != NULL) {
      return page->is_in(addr);
    }
  }

  return false;
}

double ZHeap::boost_factor() const {
  return _workers.boost_factor();
}

uint ZHeap::nconcurrent() const {
  return _workers.nconcurrent();
}

void ZHeap::set_nconcurrent(uint n) {
  _workers.set_nconcurrent(n);
}

uint ZHeap::nconcurrent_no_boost() const {
  return _workers.nconcurrent_no_boost();
}

void ZHeap::set_boost_worker_threads(bool boost) {
  _workers.set_boost(boost);
}

bool ZHeap::should_start_gc_now(bool print_log) {
  // on alloc stall, the alloc rate metric becomes unreliable. using a few
  // consecutive full-speed gc cycles to regain more accurate alloc rate
  constexpr static uint32_t alloc_stall_effect = 3;
  static uint32_t last_alloc_stall_seq_num = (uint32_t)-alloc_stall_effect;

  bool ret;
  uint suggested_n;
  double n_ideal = 0.0;
  double n_dec_ideal = 0.0;

  const bool is_stalled = used_high() >= soft_max_capacity();

  // 0.1%
  constexpr double sd_factor = 3.290527;
  const double alloc_rate = ZStatAllocRate::avg()    * ZAllocationSpikeTolerance
                          + ZStatAllocRate::avg_sd() * sd_factor
                          + 1.0; // avoid division by zero

  const size_t mutator_max = soft_max_capacity() - ZHeuristics::relocation_headroom();

  // `margin` measures the closest distance to oom since previous stw1 in
  // seconds, negative value means potential alloc stall.
  const double watermark = (double)used_high() / mutator_max;
  const double margin = mutator_max * (1-watermark) / alloc_rate;

  const double alloc_rate_sd_percent = ZStatAllocRate::avg_sd() / (ZStatAllocRate::avg() + 1.0);

  constexpr double sample_interval = 1.0 / ZStatAllocRate::sample_hz;

  const size_t used_bytes = used();
  const double used_percent = (double) used_bytes / ZStatHeap::max_capacity();
  const size_t free_bytes = mutator_max > used_bytes ? mutator_max - used_bytes
                                                     : 0;

  // Calculate how much time left before hitting oom giving the current free
  // bytes and the predicted alloc rate. Bound by 1ms to avoid division by zero.
  const double time_till_oom = MAX2(free_bytes/alloc_rate - sample_interval, 0.001);

  auto normalize_factor = UseDynamicNumberOfGCThreads ? ConcGCThreads : boost_factor();
  const AbsSeq& duration = ZStatCycle::normalized_duration();
  const double gc_duration_avg = duration.davg();
  const double gc_duration_sd = duration.dsd();
  const double norm_gc_duration = (gc_duration_avg + gc_duration_sd * sd_factor) / normalize_factor;

  // avoiding boost
  const uint previous_n_bounded = MIN2(nconcurrent(), ConcGCThreads);

  // No adaptation once a gc cycle is initiated, so each cycle needs to be
  // short enough to handle emergencies.
  // TODO: not sure about absolute number or sth depending on norm_gc_duration
  constexpr double max_gc_duration = 10;

  uint min_n = clamp((uint) ceil(norm_gc_duration * ConcGCThreads / max_gc_duration),
                     1u, ConcGCThreads);

  // It seems in steady state, the sd is < 5%, using the following magic threshold.
  constexpr double alloc_rate_sd_threshold = 0.15;

  // An accurate prediction requires steady alloc rate and gc duration (heap usage as the predicator)
  const bool is_env_steady = true
    && alloc_rate_sd_percent                         <= alloc_rate_sd_threshold
    && used_percent - ZStatCycle::prev_used_percent  <=  0.10
    ;

  constexpr bool at_least_half_ConcGCThreads = false;
  if (!is_env_steady || at_least_half_ConcGCThreads) {
    min_n = MAX2(min_n, (uint) ceil(ConcGCThreads / 2.0));
  }

  do {

  // (almost) alloc/relocation stall; full-speed gc right away
  if (false
      || is_stalled
      || (last_alloc_stall_seq_num + alloc_stall_effect >= ZGlobalSeqNum) // alloc stall after-effect
      ) {
    suggested_n = ConcGCThreads;
    ret = true;
    break;
  }

  // startup; always ConcGCThreads
  if (!ZStatCycle::is_warm()) {
    suggested_n = ConcGCThreads;
    ret = norm_gc_duration + sample_interval >= time_till_oom;
    break;
  }

  uint n;
  if (alloc_rate_sd_percent >= alloc_rate_sd_threshold) {
    // Since time_till_oom is calculated based on the currently observed
    // alloc rate, when the alloc rate is volatile (reflected as large sd),
    // such calculation could be unreliable. In order to incorporate such
    // volatility, we artificially deflate the oom time to react promptly for
    // the potential imminent high alloc rate.
    const double deflated_time_till_oom = time_till_oom / (1.0 + alloc_rate_sd_percent);
    n_ideal = norm_gc_duration * ConcGCThreads / deflated_time_till_oom;
    // not reducing n when alloc rate is too volatile
    n = clamp((uint) ceil(n_ideal), previous_n_bounded, ConcGCThreads);
  } else {
    n_ideal = norm_gc_duration * ConcGCThreads / time_till_oom;
    n = clamp((uint) ceil(n_ideal), min_n, ConcGCThreads);
    // more stringent calculation on trying to reduce n
    if (n < previous_n_bounded) {
      // after reducing n, gc duration will increase, affecting the
      // calculation for next gc cycle. Therefore, we use the next
      // time_till_oom (deducting the gc duration delta) to derive n
      const double gc_duration_delta = norm_gc_duration * ConcGCThreads * (1.0/n - 1.0/previous_n_bounded);
      const double next_time_till_oom = ZStatCycle::time_since_last()
                                      - sample_interval
                                      - gc_duration_delta
                                      + time_till_oom;
      n_dec_ideal = norm_gc_duration * ConcGCThreads / MAX2(next_time_till_oom, 0.001); // in case it's negative
      // some friction on reducing n
      n = clamp((uint) ceil(n_dec_ideal + 0.50), min_n, previous_n_bounded);
    }
  }

  suggested_n = n;
  // some head start for not running at full-speed and some negative feedback for too small margin
  const double  extra = sample_interval
                      + (ConcGCThreads - n) * sample_interval
                      + MAX2(2*sample_interval - margin, 0.0) * 10
                      ;
  ret = n > previous_n_bounded || (norm_gc_duration * ConcGCThreads / n + extra >= time_till_oom);

  } while (false);

  if (print_log) {
    log_info(gc)(
        "high: %.1f%%; "
        "min_n: %d; "
        "gc: %.3f (%.1f%%), "
        "oom: %.3f, "
        "margin: %.3f, "
        "rate: %.3f + %.3f M/s (%.1f%%), "
        "n: %d -> %d (%.3f, %.3f), "
        "",
        watermark * 100,
        min_n,
        norm_gc_duration * ConcGCThreads, gc_duration_sd / gc_duration_avg * 100,
        time_till_oom,
        margin,
        (ZStatAllocRate::avg())/(1024*1024), (ZStatAllocRate::avg_sd() * 1)/(1024*1024),
        (alloc_rate_sd_percent * 100),
        nconcurrent(),
        suggested_n,
        n_ideal,
        n_dec_ideal
        );
    if (is_stalled) {
      last_alloc_stall_seq_num = ZGlobalSeqNum;
    }
    if (UseDynamicNumberOfGCThreads) {
      assert(min_n <= suggested_n && suggested_n <= ConcGCThreads, "");
      set_nconcurrent(suggested_n);
    }
  }

  return ret;
}

void ZHeap::dynamic_adjust_nconcurrent() {
  if (!ZStatCycle::is_normalized_duration_trustable()) {
    return;
  }

  should_start_gc_now(true);
}

void ZHeap::threads_do(ThreadClosure* tc) const {
  _page_allocator.threads_do(tc);
  _workers.threads_do(tc);
}

void ZHeap::out_of_memory() {
  ResourceMark rm;

  ZStatInc(ZCounterOutOfMemory);
  log_info(gc)("Out Of Memory (%s)", Thread::current()->name());
}

ZPage* ZHeap::alloc_page(uint8_t type, size_t size, ZAllocationFlags flags) {
  ZPage* const page = _page_allocator.alloc_page(type, size, flags);
  if (page != NULL) {
    // Insert page table entry
    _page_table.insert(page);
  }

  return page;
}

void ZHeap::undo_alloc_page(ZPage* page) {
  assert(page->is_allocating(), "Invalid page state");

  ZStatInc(ZCounterUndoPageAllocation);
  log_trace(gc)("Undo page allocation, thread: " PTR_FORMAT " (%s), page: " PTR_FORMAT ", size: " SIZE_FORMAT,
                ZThread::id(), ZThread::name(), p2i(page), page->size());

  free_page(page, false /* reclaimed */);
}

void ZHeap::free_page(ZPage* page, bool reclaimed) {
  // Remove page table entry
  _page_table.remove(page);

  // Free page
  _page_allocator.free_page(page, reclaimed);
}

void ZHeap::free_pages(const ZArray<ZPage*>* pages, bool reclaimed) {
  // Remove page table entries
  ZArrayIterator<ZPage*> iter(pages);
  for (ZPage* page; iter.next(&page);) {
    _page_table.remove(page);
  }

  // Free pages
  _page_allocator.free_pages(pages, reclaimed);
}

void ZHeap::flip_to_marked() {
  ZVerifyViewsFlip flip(&_page_allocator);
  ZAddress::flip_to_marked();
}

void ZHeap::flip_to_remapped() {
  ZVerifyViewsFlip flip(&_page_allocator);
  ZAddress::flip_to_remapped();
}

void ZHeap::mark_start() {
  assert(SafepointSynchronize::is_at_safepoint(), "Should be at safepoint");

  // Flip address view
  flip_to_marked();

  // Retire allocating pages
  _object_allocator.retire_pages();

  // Reset allocated/reclaimed/used statistics
  _page_allocator.reset_statistics();

  // Reset encountered/dropped/enqueued statistics
  _reference_processor.reset_statistics();

  // Enter mark phase
  ZGlobalPhase = ZPhaseMark;

  // Reset marking information and mark roots
  _mark.start();

  // Update statistics
  ZStatHeap::set_at_mark_start(_page_allocator.stats());
}

void ZHeap::mark(bool initial) {
  _mark.mark(initial);
}

void ZHeap::mark_flush_and_free(Thread* thread) {
  _mark.flush_and_free(thread);
}

bool ZHeap::mark_end() {
  assert(SafepointSynchronize::is_at_safepoint(), "Should be at safepoint");

  // Try end marking
  if (!_mark.end()) {
    // Marking not completed, continue concurrent mark
    return false;
  }

  // Enter mark completed phase
  ZGlobalPhase = ZPhaseMarkCompleted;

  // Verify after mark
  ZVerify::after_mark();

  // Update statistics
  ZStatHeap::set_at_mark_end(_page_allocator.stats());

  // Block resurrection of weak/phantom references
  ZResurrection::block();

  // Prepare to unload stale metadata and nmethods
  _unload.prepare();

  // Notify JVMTI that some tagmap entry objects may have died.
  JvmtiTagMap::set_needs_cleaning();

  return true;
}

void ZHeap::keep_alive(oop obj) {
  ZBarrier::keep_alive_barrier_on_oop(obj);
}

void ZHeap::set_soft_reference_policy(bool clear) {
  _reference_processor.set_soft_reference_policy(clear);
}

class ZRendezvousClosure : public HandshakeClosure {
public:
  ZRendezvousClosure() :
      HandshakeClosure("ZRendezvous") {}

  void do_thread(Thread* thread) {}
};

void ZHeap::process_non_strong_references() {
  // Process Soft/Weak/Final/PhantomReferences
  _reference_processor.process_references();

  // Process weak roots
  _weak_roots_processor.process_weak_roots();

  // Unlink stale metadata and nmethods
  _unload.unlink();

  // Perform a handshake. This is needed 1) to make sure that stale
  // metadata and nmethods are no longer observable. And 2), to
  // prevent the race where a mutator first loads an oop, which is
  // logically null but not yet cleared. Then this oop gets cleared
  // by the reference processor and resurrection is unblocked. At
  // this point the mutator could see the unblocked state and pass
  // this invalid oop through the normal barrier path, which would
  // incorrectly try to mark the oop.
  ZRendezvousClosure cl;
  Handshake::execute(&cl);

  // Unblock resurrection of weak/phantom references
  ZResurrection::unblock();

  // Purge stale metadata and nmethods that were unlinked
  _unload.purge();

  // Enqueue Soft/Weak/Final/PhantomReferences. Note that this
  // must be done after unblocking resurrection. Otherwise the
  // Finalizer thread could call Reference.get() on the Finalizers
  // that were just enqueued, which would incorrectly return null
  // during the resurrection block window, since such referents
  // are only Finalizable marked.
  _reference_processor.enqueue_references();
}

void ZHeap::free_empty_pages(ZRelocationSetSelector* selector, int bulk) {
  // Freeing empty pages in bulk is an optimization to avoid grabbing
  // the page allocator lock, and trying to satisfy stalled allocations
  // too frequently.
  if (selector->should_free_empty_pages(bulk)) {
    free_pages(selector->empty_pages(), true /* reclaimed */);
    selector->clear_empty_pages();
  }
}

void ZHeap::select_relocation_set() {
  // Do not allow pages to be deleted
  _page_allocator.enable_deferred_delete();

  // Register relocatable pages with selector
  ZRelocationSetSelector selector;
  ZPageTableIterator pt_iter(&_page_table);
  for (ZPage* page; pt_iter.next(&page);) {
    if (!page->is_relocatable()) {
      // Not relocatable, don't register
      continue;
    }

    if (page->is_marked()) {
      // Register live page
      selector.register_live_page(page);
    } else {
      // Register empty page
      selector.register_empty_page(page);

      // Reclaim empty pages in bulk
      free_empty_pages(&selector, 64 /* bulk */);
    }
  }

  // Reclaim remaining empty pages
  free_empty_pages(&selector, 0 /* bulk */);

  // Allow pages to be deleted
  _page_allocator.disable_deferred_delete();

  // Select relocation set
  selector.select();

  // Install relocation set
  _relocation_set.install(&selector);

  // Setup forwarding table
  ZRelocationSetIterator rs_iter(&_relocation_set);
  for (ZForwarding* forwarding; rs_iter.next(&forwarding);) {
    _forwarding_table.insert(forwarding);
  }

  // Update statistics
  ZStatRelocation::set_at_select_relocation_set(selector.stats());
  ZStatHeap::set_at_select_relocation_set(selector.stats());
}

void ZHeap::reset_relocation_set() {
  // Reset forwarding table
  ZRelocationSetIterator iter(&_relocation_set);
  for (ZForwarding* forwarding; iter.next(&forwarding);) {
    _forwarding_table.remove(forwarding);
  }

  // Reset relocation set
  _relocation_set.reset();
}

void ZHeap::relocate_start() {
  assert(SafepointSynchronize::is_at_safepoint(), "Should be at safepoint");

  // Finish unloading stale metadata and nmethods
  _unload.finish();

  // Flip address view
  flip_to_remapped();

  // Enter relocate phase
  ZGlobalPhase = ZPhaseRelocate;

  // Update statistics
  ZStatHeap::set_at_relocate_start(_page_allocator.stats());

  // Notify JVMTI
  JvmtiTagMap::set_needs_rehashing();
}

void ZHeap::relocate() {
  // Relocate relocation set
  _relocate.relocate(&_relocation_set);

  // Update statistics
  ZStatHeap::set_at_relocate_end(_page_allocator.stats(), _object_allocator.relocated());
}

void ZHeap::object_iterate(ObjectClosure* cl, bool visit_weaks) {
  assert(SafepointSynchronize::is_at_safepoint(), "Should be at safepoint");
  ZHeapIterator iter(1 /* nworkers */, visit_weaks);
  iter.object_iterate(cl, 0 /* worker_id */);
}

ParallelObjectIterator* ZHeap::parallel_object_iterator(uint nworkers, bool visit_weaks) {
  assert(SafepointSynchronize::is_at_safepoint(), "Should be at safepoint");
  return new ZHeapIterator(nworkers, visit_weaks);
}

void ZHeap::pages_do(ZPageClosure* cl) {
  ZPageTableIterator iter(&_page_table);
  for (ZPage* page; iter.next(&page);) {
    cl->do_page(page);
  }
  _page_allocator.pages_do(cl);
}

void ZHeap::serviceability_initialize() {
  _serviceability.initialize();
}

GCMemoryManager* ZHeap::serviceability_cycle_memory_manager() {
  return _serviceability.cycle_memory_manager();
}

GCMemoryManager* ZHeap::serviceability_pause_memory_manager() {
  return _serviceability.pause_memory_manager();
}

MemoryPool* ZHeap::serviceability_memory_pool() {
  return _serviceability.memory_pool();
}

ZServiceabilityCounters* ZHeap::serviceability_counters() {
  return _serviceability.counters();
}

void ZHeap::print_on(outputStream* st) const {
  st->print_cr(" ZHeap           used " SIZE_FORMAT "M, capacity " SIZE_FORMAT "M, max capacity " SIZE_FORMAT "M",
               used() / M,
               capacity() / M,
               max_capacity() / M);
  MetaspaceUtils::print_on(st);
}

void ZHeap::print_extended_on(outputStream* st) const {
  print_on(st);
  st->cr();

  // Do not allow pages to be deleted
  _page_allocator.enable_deferred_delete();

  // Print all pages
  st->print_cr("ZGC Page Table:");
  ZPageTableIterator iter(&_page_table);
  for (ZPage* page; iter.next(&page);) {
    page->print_on(st);
  }

  // Allow pages to be deleted
  _page_allocator.enable_deferred_delete();
}

bool ZHeap::print_location(outputStream* st, uintptr_t addr) const {
  if (LocationPrinter::is_valid_obj((void*)addr)) {
    st->print(PTR_FORMAT " is a %s oop: ", addr, ZAddress::is_good(addr) ? "good" : "bad");
    ZOop::from_address(addr)->print_on(st);
    return true;
  }

  return false;
}

void ZHeap::verify() {
  // Heap verification can only be done between mark end and
  // relocate start. This is the only window where all oop are
  // good and the whole heap is in a consistent state.
  guarantee(ZGlobalPhase == ZPhaseMarkCompleted, "Invalid phase");

  ZVerify::after_weak_processing();
}
