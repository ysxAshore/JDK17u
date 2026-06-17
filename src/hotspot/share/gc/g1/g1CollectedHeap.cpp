/*
 * Copyright (c) 2001, 2021, Oracle and/or its affiliates. All rights reserved.
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
#include <linux/ioctl.h>
#include <sys/ioctl.h>
#include "precompiled.hpp"
#include "classfile/classLoaderDataGraph.hpp"
#include "classfile/metadataOnStackMark.hpp"
#include "classfile/stringTable.hpp"
#include "code/codeCache.hpp"
#include "code/icBuffer.hpp"
#include "compiler/oopMap.hpp"
#include "gc/g1/g1Allocator.inline.hpp"
#include "gc/g1/g1Arguments.hpp"
#include "gc/g1/g1BarrierSet.hpp"
#include "gc/g1/g1CollectedHeap.inline.hpp"
#include "gc/g1/g1CollectionSet.hpp"
#include "gc/g1/g1CollectorState.hpp"
#include "gc/g1/g1ConcurrentRefine.hpp"
#include "gc/g1/g1ConcurrentRefineThread.hpp"
#include "gc/g1/g1ConcurrentMarkThread.inline.hpp"
#include "gc/g1/g1DirtyCardQueue.hpp"
#include "gc/g1/g1EvacStats.inline.hpp"
#include "gc/g1/g1FullCollector.hpp"
#include "gc/g1/g1GCParPhaseTimesTracker.hpp"
#include "gc/g1/g1GCPhaseTimes.hpp"
#include "gc/g1/g1GCPauseType.hpp"
#include "gc/g1/g1HeapSizingPolicy.hpp"
#include "gc/g1/g1HeapTransition.hpp"
#include "gc/g1/g1HeapVerifier.hpp"
#include "gc/g1/g1HotCardCache.hpp"
#include "gc/g1/g1InitLogger.hpp"
#include "gc/g1/g1MemoryPool.hpp"
#include "gc/g1/g1OopClosures.inline.hpp"
#include "gc/g1/g1ParallelCleaning.hpp"
#include "gc/g1/g1ParScanThreadState.inline.hpp"
#include "gc/g1/g1PeriodicGCTask.hpp"
#include "gc/g1/g1Policy.hpp"
#include "gc/g1/g1RedirtyCardsQueue.hpp"
#include "gc/g1/g1RegionToSpaceMapper.hpp"
#include "gc/g1/g1RemSet.hpp"
#include "gc/g1/g1RootClosures.hpp"
#include "gc/g1/g1RootProcessor.hpp"
#include "gc/g1/g1SATBMarkQueueSet.hpp"
#include "gc/g1/g1ThreadLocalData.hpp"
#include "gc/g1/g1Trace.hpp"
#include "gc/g1/g1ServiceThread.hpp"
#include "gc/g1/g1UncommitRegionTask.hpp"
#include "gc/g1/g1VMOperations.hpp"
#include "gc/g1/g1YoungGCPostEvacuateTasks.hpp"
#include "gc/g1/heapRegion.inline.hpp"
#include "gc/g1/heapRegionRemSet.hpp"
#include "gc/g1/heapRegionSet.inline.hpp"
#include "gc/shared/concurrentGCBreakpoints.hpp"
#include "gc/shared/gcBehaviours.hpp"
#include "gc/shared/gcHeapSummary.hpp"
#include "gc/shared/gcId.hpp"
#include "gc/shared/gcLocker.hpp"
#include "gc/shared/gcTimer.hpp"
#include "gc/shared/gcTraceTime.inline.hpp"
#include "gc/shared/generationSpec.hpp"
#include "gc/shared/isGCActiveMark.hpp"
#include "gc/shared/locationPrinter.inline.hpp"
#include "gc/shared/oopStorageParState.hpp"
#include "gc/shared/preservedMarks.inline.hpp"
#include "gc/shared/suspendibleThreadSet.hpp"
#include "gc/shared/referenceProcessor.inline.hpp"
#include "gc/shared/taskTerminator.hpp"
#include "gc/shared/taskqueue.inline.hpp"
#include "gc/shared/tlab_globals.hpp"
#include "gc/shared/weakProcessor.inline.hpp"
#include "gc/shared/workerPolicy.hpp"
#include "logging/log.hpp"
#include "memory/allocation.hpp"
#include "memory/iterator.hpp"
#include "memory/heapInspection.hpp"
#include "memory/metaspaceUtils.hpp"
#include "memory/resourceArea.hpp"
#include "memory/universe.hpp"
#include "oops/access.inline.hpp"
#include "oops/compressedOops.inline.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/atomic.hpp"
#include "runtime/handles.inline.hpp"
#include "runtime/init.hpp"
#include "runtime/java.hpp"
#include "runtime/orderAccess.hpp"
#include "runtime/threadSMR.hpp"
#include "runtime/vmThread.hpp"
#include "utilities/align.hpp"
#include "utilities/autoRestore.hpp"
#include "utilities/bitMap.inline.hpp"
#include "utilities/globalDefinitions.hpp"
#include "utilities/stack.inline.hpp"

size_t G1CollectedHeap::_humongous_object_threshold_in_words = 0;

// INVARIANTS/NOTES
//
// All allocation activity covered by the G1CollectedHeap interface is
// serialized by acquiring the HeapLock.  This happens in mem_allocate
// and allocate_new_tlab, which are the "entry" points to the
// allocation code from the rest of the JVM.  (Note that this does not
// apply to TLAB allocation, which is not part of this interface: it
// is done by clients of this interface.)

void G1RegionMappingChangedListener::reset_from_card_cache(uint start_idx, size_t num_regions)
{
  HeapRegionRemSet::invalidate_from_card_cache(start_idx, num_regions);
}

void G1RegionMappingChangedListener::on_commit(uint start_idx, size_t num_regions, bool zero_filled)
{
  // The from card cache is not the memory that is actually committed. So we cannot
  // take advantage of the zero_filled parameter.
  reset_from_card_cache(start_idx, num_regions);
}

Tickspan G1CollectedHeap::run_task_timed(AbstractGangTask *task)
{
  Ticks start = Ticks::now();
  workers()->run_task(task);
  return Ticks::now() - start;
}

void G1CollectedHeap::run_batch_task(G1BatchedGangTask *cl)
{
  uint num_workers = MAX2(1u, MIN2(cl->num_workers_estimate(), workers()->active_workers()));
  cl->set_max_workers(num_workers);
  workers()->run_task(cl, num_workers);
}

HeapRegion *G1CollectedHeap::new_heap_region(uint hrs_index,
                                             MemRegion mr)
{
  return new HeapRegion(hrs_index, bot(), mr);
}

// Private methods.

HeapRegion *G1CollectedHeap::new_region(size_t word_size,
                                        HeapRegionType type,
                                        bool do_expand,
                                        uint node_index)
{
  assert(!is_humongous(word_size) || word_size <= HeapRegion::GrainWords,
         "the only time we use this to allocate a humongous region is "
         "when we are allocating a single humongous region");

  HeapRegion *res = _hrm.allocate_free_region(type, node_index);

  if (res == NULL && do_expand && _expand_heap_after_alloc_failure)
  {
    // Currently, only attempts to allocate GC alloc regions set
    // do_expand to true. So, we should only reach here during a
    // safepoint. If this assumption changes we might have to
    // reconsider the use of _expand_heap_after_alloc_failure.
    assert(SafepointSynchronize::is_at_safepoint(), "invariant");

    log_debug(gc, ergo, heap)("Attempt heap expansion (region allocation request failed). Allocation request: " SIZE_FORMAT "B",
                              word_size * HeapWordSize);

    assert(word_size * HeapWordSize < HeapRegion::GrainBytes,
           "This kind of expansion should never be more than one region. Size: " SIZE_FORMAT,
           word_size * HeapWordSize);
    if (expand_single_region(node_index))
    {
      // Given that expand_single_region() succeeded in expanding the heap, and we
      // always expand the heap by an amount aligned to the heap
      // region size, the free list should in theory not be empty.
      // In either case allocate_free_region() will check for NULL.
      res = _hrm.allocate_free_region(type, node_index);
    }
    else
    {
      _expand_heap_after_alloc_failure = false;
    }
  }
  return res;
}

HeapWord *
G1CollectedHeap::humongous_obj_allocate_initialize_regions(HeapRegion *first_hr,
                                                           uint num_regions,
                                                           size_t word_size)
{
  assert(first_hr != NULL, "pre-condition");
  assert(is_humongous(word_size), "word_size should be humongous");
  assert(num_regions * HeapRegion::GrainWords >= word_size, "pre-condition");

  // Index of last region in the series.
  uint first = first_hr->hrm_index();
  uint last = first + num_regions - 1;

  // We need to initialize the region(s) we just discovered. This is
  // a bit tricky given that it can happen concurrently with
  // refinement threads refining cards on these regions and
  // potentially wanting to refine the BOT as they are scanning
  // those cards (this can happen shortly after a cleanup; see CR
  // 6991377). So we have to set up the region(s) carefully and in
  // a specific order.

  // The word size sum of all the regions we will allocate.
  size_t word_size_sum = (size_t)num_regions * HeapRegion::GrainWords;
  assert(word_size <= word_size_sum, "sanity");

  // The passed in hr will be the "starts humongous" region. The header
  // of the new object will be placed at the bottom of this region.
  HeapWord *new_obj = first_hr->bottom();
  // This will be the new top of the new object.
  HeapWord *obj_top = new_obj + word_size;

  // First, we need to zero the header of the space that we will be
  // allocating. When we update top further down, some refinement
  // threads might try to scan the region. By zeroing the header we
  // ensure that any thread that will try to scan the region will
  // come across the zero klass word and bail out.
  //
  // NOTE: It would not have been correct to have used
  // CollectedHeap::fill_with_object() and make the space look like
  // an int array. The thread that is doing the allocation will
  // later update the object header to a potentially different array
  // type and, for a very short period of time, the klass and length
  // fields will be inconsistent. This could cause a refinement
  // thread to calculate the object size incorrectly.
  Copy::fill_to_words(new_obj, oopDesc::header_size(), 0);

  // Next, pad out the unused tail of the last region with filler
  // objects, for improved usage accounting.
  // How many words we use for filler objects.
  size_t word_fill_size = word_size_sum - word_size;

  // How many words memory we "waste" which cannot hold a filler object.
  size_t words_not_fillable = 0;

  if (word_fill_size >= min_fill_size())
  {
    fill_with_objects(obj_top, word_fill_size);
  }
  else if (word_fill_size > 0)
  {
    // We have space to fill, but we cannot fit an object there.
    words_not_fillable = word_fill_size;
    word_fill_size = 0;
  }

  // We will set up the first region as "starts humongous". This
  // will also update the BOT covering all the regions to reflect
  // that there is a single object that starts at the bottom of the
  // first region.
  first_hr->set_starts_humongous(obj_top, word_fill_size);
  _policy->remset_tracker()->update_at_allocate(first_hr);
  // Then, if there are any, we will set up the "continues
  // humongous" regions.
  HeapRegion *hr = NULL;
  for (uint i = first + 1; i <= last; ++i)
  {
    hr = region_at(i);
    hr->set_continues_humongous(first_hr);
    _policy->remset_tracker()->update_at_allocate(hr);
  }

  // Up to this point no concurrent thread would have been able to
  // do any scanning on any region in this series. All the top
  // fields still point to bottom, so the intersection between
  // [bottom,top] and [card_start,card_end] will be empty. Before we
  // update the top fields, we'll do a storestore to make sure that
  // no thread sees the update to top before the zeroing of the
  // object header and the BOT initialization.
  OrderAccess::storestore();

  // Now, we will update the top fields of the "continues humongous"
  // regions except the last one.
  for (uint i = first; i < last; ++i)
  {
    hr = region_at(i);
    hr->set_top(hr->end());
  }

  hr = region_at(last);
  // If we cannot fit a filler object, we must set top to the end
  // of the humongous object, otherwise we cannot iterate the heap
  // and the BOT will not be complete.
  hr->set_top(hr->end() - words_not_fillable);

  assert(hr->bottom() < obj_top && obj_top <= hr->end(),
         "obj_top should be in last region");

  _verifier->check_bitmaps("Humongous Region Allocation", first_hr);

  assert(words_not_fillable == 0 ||
             first_hr->bottom() + word_size_sum - words_not_fillable == hr->top(),
         "Miscalculation in humongous allocation");

  increase_used((word_size_sum - words_not_fillable) * HeapWordSize);

  for (uint i = first; i <= last; ++i)
  {
    hr = region_at(i);
    _humongous_set.add(hr);
    _hr_printer.alloc(hr);
  }

  return new_obj;
}

size_t G1CollectedHeap::humongous_obj_size_in_regions(size_t word_size)
{
  assert(is_humongous(word_size), "Object of size " SIZE_FORMAT " must be humongous here", word_size);
  return align_up(word_size, HeapRegion::GrainWords) / HeapRegion::GrainWords;
}

// If could fit into free regions w/o expansion, try.
// Otherwise, if can expand, do so.
// Otherwise, if using ex regions might help, try with ex given back.
HeapWord *G1CollectedHeap::humongous_obj_allocate(size_t word_size)
{
  assert_heap_locked_or_at_safepoint(true /* should_be_vm_thread */);

  _verifier->verify_region_sets_optional();

  uint obj_regions = (uint)humongous_obj_size_in_regions(word_size);

  // Policy: First try to allocate a humongous object in the free list.
  HeapRegion *humongous_start = _hrm.allocate_humongous(obj_regions);
  if (humongous_start == NULL)
  {
    // Policy: We could not find enough regions for the humongous object in the
    // free list. Look through the heap to find a mix of free and uncommitted regions.
    // If so, expand the heap and allocate the humongous object.
    humongous_start = _hrm.expand_and_allocate_humongous(obj_regions);
    if (humongous_start != NULL)
    {
      // We managed to find a region by expanding the heap.
      log_debug(gc, ergo, heap)("Heap expansion (humongous allocation request). Allocation request: " SIZE_FORMAT "B",
                                word_size * HeapWordSize);
      policy()->record_new_heap_size(num_regions());
    }
    else
    {
      // Policy: Potentially trigger a defragmentation GC.
    }
  }

  HeapWord *result = NULL;
  if (humongous_start != NULL)
  {
    result = humongous_obj_allocate_initialize_regions(humongous_start, obj_regions, word_size);
    assert(result != NULL, "it should always return a valid result");

    // A successful humongous object allocation changes the used space
    // information of the old generation so we need to recalculate the
    // sizes and update the jstat counters here.
    g1mm()->update_sizes();
  }

  _verifier->verify_region_sets_optional();

  return result;
}

HeapWord *G1CollectedHeap::allocate_new_tlab(size_t min_size,
                                             size_t requested_size,
                                             size_t *actual_size)
{
  assert_heap_not_locked_and_not_at_safepoint();
  assert(!is_humongous(requested_size), "we do not allow humongous TLABs");

  return attempt_allocation(min_size, requested_size, actual_size);
}

HeapWord *
G1CollectedHeap::mem_allocate(size_t word_size,
                              bool *gc_overhead_limit_was_exceeded)
{
  assert_heap_not_locked_and_not_at_safepoint();

  if (is_humongous(word_size))
  {
    return attempt_allocation_humongous(word_size);
  }
  size_t dummy = 0;
  return attempt_allocation(word_size, word_size, &dummy);
}

HeapWord *G1CollectedHeap::attempt_allocation_slow(size_t word_size)
{
  ResourceMark rm; // For retrieving the thread names in log messages.

  // Make sure you read the note in attempt_allocation_humongous().

  assert_heap_not_locked_and_not_at_safepoint();
  assert(!is_humongous(word_size), "attempt_allocation_slow() should not "
                                   "be called for humongous allocation requests");

  // We should only get here after the first-level allocation attempt
  // (attempt_allocation()) failed to allocate.

  // We will loop until a) we manage to successfully perform the
  // allocation or b) we successfully schedule a collection which
  // fails to perform the allocation. b) is the only case when we'll
  // return NULL.
  HeapWord *result = NULL;
  for (uint try_count = 1, gclocker_retry_count = 0; /* we'll return */; try_count += 1)
  {
    bool should_try_gc;
    bool preventive_collection_required = false;
    uint gc_count_before;

    {
      MutexLocker x(Heap_lock);

      // Now that we have the lock, we first retry the allocation in case another
      // thread changed the region while we were waiting to acquire the lock.
      size_t actual_size;
      result = _allocator->attempt_allocation(word_size, word_size, &actual_size);
      if (result != NULL)
      {
        return result;
      }

      preventive_collection_required = policy()->preventive_collection_required(1);
      if (!preventive_collection_required)
      {
        // We've already attempted a lock-free allocation above, so we don't want to
        // do it again. Let's jump straight to replacing the active region.
        result = _allocator->attempt_allocation_using_new_region(word_size);
        if (result != NULL)
        {
          return result;
        }

        // If the GCLocker is active and we are bound for a GC, try expanding young gen.
        // This is different to when only GCLocker::needs_gc() is set: try to avoid
        // waiting because the GCLocker is active to not wait too long.
        if (GCLocker::is_active_and_needs_gc() && policy()->can_expand_young_list())
        {
          // No need for an ergo message here, can_expand_young_list() does this when
          // it returns true.
          result = _allocator->attempt_allocation_force(word_size);
          if (result != NULL)
          {
            return result;
          }
        }
      }

      // Only try a GC if the GCLocker does not signal the need for a GC. Wait until
      // the GCLocker initiated GC has been performed and then retry. This includes
      // the case when the GC Locker is not active but has not been performed.
      should_try_gc = !GCLocker::needs_gc();
      // Read the GC count while still holding the Heap_lock.
      gc_count_before = total_collections();
    }

    if (should_try_gc)
    {
      GCCause::Cause gc_cause = preventive_collection_required ? GCCause::_g1_preventive_collection
                                                               : GCCause::_g1_inc_collection_pause;
      bool succeeded;
      result = do_collection_pause(word_size, gc_count_before, &succeeded, gc_cause);
      if (result != NULL)
      {
        assert(succeeded, "only way to get back a non-NULL result");
        log_trace(gc, alloc)("%s: Successfully scheduled collection returning " PTR_FORMAT,
                             Thread::current()->name(), p2i(result));
        return result;
      }

      if (succeeded)
      {
        // We successfully scheduled a collection which failed to allocate. No
        // point in trying to allocate further. We'll just return NULL.
        log_trace(gc, alloc)("%s: Successfully scheduled collection failing to allocate " SIZE_FORMAT " words", Thread::current()->name(), word_size);
        return NULL;
      }
      log_trace(gc, alloc)("%s: Unsuccessfully scheduled collection allocating " SIZE_FORMAT " words",
                           Thread::current()->name(), word_size);
    }
    else
    {
      // Failed to schedule a collection.
      if (gclocker_retry_count > GCLockerRetryAllocationCount)
      {
        log_warning(gc, alloc)("%s: Retried waiting for GCLocker too often allocating " SIZE_FORMAT " words", Thread::current()->name(), word_size);
        return NULL;
      }
      log_trace(gc, alloc)("%s: Stall until clear", Thread::current()->name());
      // The GCLocker is either active or the GCLocker initiated
      // GC has not yet been performed. Stall until it is and
      // then retry the allocation.
      GCLocker::stall_until_clear();
      gclocker_retry_count += 1;
    }

    // We can reach here if we were unsuccessful in scheduling a
    // collection (because another thread beat us to it) or if we were
    // stalled due to the GC locker. In either can we should retry the
    // allocation attempt in case another thread successfully
    // performed a collection and reclaimed enough space. We do the
    // first attempt (without holding the Heap_lock) here and the
    // follow-on attempt will be at the start of the next loop
    // iteration (after taking the Heap_lock).
    size_t dummy = 0;
    result = _allocator->attempt_allocation(word_size, word_size, &dummy);
    if (result != NULL)
    {
      return result;
    }

    // Give a warning if we seem to be looping forever.
    if ((QueuedAllocationWarningCount > 0) &&
        (try_count % QueuedAllocationWarningCount == 0))
    {
      log_warning(gc, alloc)("%s:  Retried allocation %u times for " SIZE_FORMAT " words",
                             Thread::current()->name(), try_count, word_size);
    }
  }

  ShouldNotReachHere();
  return NULL;
}

void G1CollectedHeap::begin_archive_alloc_range(bool open)
{
  assert_at_safepoint_on_vm_thread();
  if (_archive_allocator == NULL)
  {
    _archive_allocator = G1ArchiveAllocator::create_allocator(this, open);
  }
}

bool G1CollectedHeap::is_archive_alloc_too_large(size_t word_size)
{
  // Allocations in archive regions cannot be of a size that would be considered
  // humongous even for a minimum-sized region, because G1 region sizes/boundaries
  // may be different at archive-restore time.
  return word_size >= humongous_threshold_for(HeapRegion::min_region_size_in_words());
}

HeapWord *G1CollectedHeap::archive_mem_allocate(size_t word_size)
{
  assert_at_safepoint_on_vm_thread();
  assert(_archive_allocator != NULL, "_archive_allocator not initialized");
  if (is_archive_alloc_too_large(word_size))
  {
    return NULL;
  }
  return _archive_allocator->archive_mem_allocate(word_size);
}

void G1CollectedHeap::end_archive_alloc_range(GrowableArray<MemRegion> *ranges,
                                              size_t end_alignment_in_bytes)
{
  assert_at_safepoint_on_vm_thread();
  assert(_archive_allocator != NULL, "_archive_allocator not initialized");

  // Call complete_archive to do the real work, filling in the MemRegion
  // array with the archive regions.
  _archive_allocator->complete_archive(ranges, end_alignment_in_bytes);
  delete _archive_allocator;
  _archive_allocator = NULL;
}

bool G1CollectedHeap::check_archive_addresses(MemRegion *ranges, size_t count)
{
  assert(ranges != NULL, "MemRegion array NULL");
  assert(count != 0, "No MemRegions provided");
  MemRegion reserved = _hrm.reserved();
  for (size_t i = 0; i < count; i++)
  {
    if (!reserved.contains(ranges[i].start()) || !reserved.contains(ranges[i].last()))
    {
      return false;
    }
  }
  return true;
}

bool G1CollectedHeap::alloc_archive_regions(MemRegion *ranges,
                                            size_t count,
                                            bool open)
{
  assert(!is_init_completed(), "Expect to be called at JVM init time");
  assert(ranges != NULL, "MemRegion array NULL");
  assert(count != 0, "No MemRegions provided");
  MutexLocker x(Heap_lock);

  MemRegion reserved = _hrm.reserved();
  HeapWord *prev_last_addr = NULL;
  HeapRegion *prev_last_region = NULL;

  // Temporarily disable pretouching of heap pages. This interface is used
  // when mmap'ing archived heap data in, so pre-touching is wasted.
  FlagSetting fs(AlwaysPreTouch, false);

  // For each specified MemRegion range, allocate the corresponding G1
  // regions and mark them as archive regions. We expect the ranges
  // in ascending starting address order, without overlap.
  for (size_t i = 0; i < count; i++)
  {
    MemRegion curr_range = ranges[i];
    HeapWord *start_address = curr_range.start();
    size_t word_size = curr_range.word_size();
    HeapWord *last_address = curr_range.last();
    size_t commits = 0;

    guarantee(reserved.contains(start_address) && reserved.contains(last_address),
              "MemRegion outside of heap [" PTR_FORMAT ", " PTR_FORMAT "]",
              p2i(start_address), p2i(last_address));
    guarantee(start_address > prev_last_addr,
              "Ranges not in ascending order: " PTR_FORMAT " <= " PTR_FORMAT,
              p2i(start_address), p2i(prev_last_addr));
    prev_last_addr = last_address;

    // Check for ranges that start in the same G1 region in which the previous
    // range ended, and adjust the start address so we don't try to allocate
    // the same region again. If the current range is entirely within that
    // region, skip it, just adjusting the recorded top.
    HeapRegion *start_region = _hrm.addr_to_region(start_address);
    if ((prev_last_region != NULL) && (start_region == prev_last_region))
    {
      start_address = start_region->end();
      if (start_address > last_address)
      {
        increase_used(word_size * HeapWordSize);
        start_region->set_top(last_address + 1);
        continue;
      }
      start_region->set_top(start_address);
      curr_range = MemRegion(start_address, last_address + 1);
      start_region = _hrm.addr_to_region(start_address);
    }

    // Perform the actual region allocation, exiting if it fails.
    // Then note how much new space we have allocated.
    if (!_hrm.allocate_containing_regions(curr_range, &commits, workers()))
    {
      return false;
    }
    increase_used(word_size * HeapWordSize);
    if (commits != 0)
    {
      log_debug(gc, ergo, heap)("Attempt heap expansion (allocate archive regions). Total size: " SIZE_FORMAT "B",
                                HeapRegion::GrainWords * HeapWordSize * commits);
    }

    // Mark each G1 region touched by the range as archive, add it to
    // the old set, and set top.
    HeapRegion *curr_region = _hrm.addr_to_region(start_address);
    HeapRegion *last_region = _hrm.addr_to_region(last_address);
    prev_last_region = last_region;

    while (curr_region != NULL)
    {
      assert(curr_region->is_empty() && !curr_region->is_pinned(),
             "Region already in use (index %u)", curr_region->hrm_index());
      if (open)
      {
        curr_region->set_open_archive();
      }
      else
      {
        curr_region->set_closed_archive();
      }
      _hr_printer.alloc(curr_region);
      _archive_set.add(curr_region);
      HeapWord *top;
      HeapRegion *next_region;
      if (curr_region != last_region)
      {
        top = curr_region->end();
        next_region = _hrm.next_region_in_heap(curr_region);
      }
      else
      {
        top = last_address + 1;
        next_region = NULL;
      }
      curr_region->set_top(top);
      curr_region = next_region;
    }
  }
  return true;
}

void G1CollectedHeap::fill_archive_regions(MemRegion *ranges, size_t count)
{
  assert(!is_init_completed(), "Expect to be called at JVM init time");
  assert(ranges != NULL, "MemRegion array NULL");
  assert(count != 0, "No MemRegions provided");
  MemRegion reserved = _hrm.reserved();
  HeapWord *prev_last_addr = NULL;
  HeapRegion *prev_last_region = NULL;

  // For each MemRegion, create filler objects, if needed, in the G1 regions
  // that contain the address range. The address range actually within the
  // MemRegion will not be modified. That is assumed to have been initialized
  // elsewhere, probably via an mmap of archived heap data.
  MutexLocker x(Heap_lock);
  for (size_t i = 0; i < count; i++)
  {
    HeapWord *start_address = ranges[i].start();
    HeapWord *last_address = ranges[i].last();

    assert(reserved.contains(start_address) && reserved.contains(last_address),
           "MemRegion outside of heap [" PTR_FORMAT ", " PTR_FORMAT "]",
           p2i(start_address), p2i(last_address));
    assert(start_address > prev_last_addr,
           "Ranges not in ascending order: " PTR_FORMAT " <= " PTR_FORMAT,
           p2i(start_address), p2i(prev_last_addr));

    HeapRegion *start_region = _hrm.addr_to_region(start_address);
    HeapRegion *last_region = _hrm.addr_to_region(last_address);
    HeapWord *bottom_address = start_region->bottom();

    // Check for a range beginning in the same region in which the
    // previous one ended.
    if (start_region == prev_last_region)
    {
      bottom_address = prev_last_addr + 1;
    }

    // Verify that the regions were all marked as archive regions by
    // alloc_archive_regions.
    HeapRegion *curr_region = start_region;
    while (curr_region != NULL)
    {
      guarantee(curr_region->is_archive(),
                "Expected archive region at index %u", curr_region->hrm_index());
      if (curr_region != last_region)
      {
        curr_region = _hrm.next_region_in_heap(curr_region);
      }
      else
      {
        curr_region = NULL;
      }
    }

    prev_last_addr = last_address;
    prev_last_region = last_region;

    // Fill the memory below the allocated range with dummy object(s),
    // if the region bottom does not match the range start, or if the previous
    // range ended within the same G1 region, and there is a gap.
    assert(start_address >= bottom_address, "bottom address should not be greater than start address");
    if (start_address > bottom_address)
    {
      size_t fill_size = pointer_delta(start_address, bottom_address);
      G1CollectedHeap::fill_with_objects(bottom_address, fill_size);
      increase_used(fill_size * HeapWordSize);
    }
  }
}

inline HeapWord *G1CollectedHeap::attempt_allocation(size_t min_word_size,
                                                     size_t desired_word_size,
                                                     size_t *actual_word_size)
{
  assert_heap_not_locked_and_not_at_safepoint();
  assert(!is_humongous(desired_word_size), "attempt_allocation() should not "
                                           "be called for humongous allocation requests");

  HeapWord *result = _allocator->attempt_allocation(min_word_size, desired_word_size, actual_word_size);

  if (result == NULL)
  {
    *actual_word_size = desired_word_size;
    result = attempt_allocation_slow(desired_word_size);
  }

  assert_heap_not_locked();
  if (result != NULL)
  {
    assert(*actual_word_size != 0, "Actual size must have been set here");
    dirty_young_block(result, *actual_word_size);
  }
  else
  {
    *actual_word_size = 0;
  }

  return result;
}

void G1CollectedHeap::populate_archive_regions_bot_part(MemRegion *ranges, size_t count)
{
  assert(!is_init_completed(), "Expect to be called at JVM init time");
  assert(ranges != NULL, "MemRegion array NULL");
  assert(count != 0, "No MemRegions provided");

  HeapWord *st = ranges[0].start();
  HeapWord *last = ranges[count - 1].last();
  HeapRegion *hr_st = _hrm.addr_to_region(st);
  HeapRegion *hr_last = _hrm.addr_to_region(last);

  HeapRegion *hr_curr = hr_st;
  while (hr_curr != NULL)
  {
    hr_curr->update_bot();
    if (hr_curr != hr_last)
    {
      hr_curr = _hrm.next_region_in_heap(hr_curr);
    }
    else
    {
      hr_curr = NULL;
    }
  }
}

void G1CollectedHeap::dealloc_archive_regions(MemRegion *ranges, size_t count)
{
  assert(!is_init_completed(), "Expect to be called at JVM init time");
  assert(ranges != NULL, "MemRegion array NULL");
  assert(count != 0, "No MemRegions provided");
  MemRegion reserved = _hrm.reserved();
  HeapWord *prev_last_addr = NULL;
  HeapRegion *prev_last_region = NULL;
  size_t size_used = 0;
  uint shrink_count = 0;

  // For each Memregion, free the G1 regions that constitute it, and
  // notify mark-sweep that the range is no longer to be considered 'archive.'
  MutexLocker x(Heap_lock);
  for (size_t i = 0; i < count; i++)
  {
    HeapWord *start_address = ranges[i].start();
    HeapWord *last_address = ranges[i].last();

    assert(reserved.contains(start_address) && reserved.contains(last_address),
           "MemRegion outside of heap [" PTR_FORMAT ", " PTR_FORMAT "]",
           p2i(start_address), p2i(last_address));
    assert(start_address > prev_last_addr,
           "Ranges not in ascending order: " PTR_FORMAT " <= " PTR_FORMAT,
           p2i(start_address), p2i(prev_last_addr));
    size_used += ranges[i].byte_size();
    prev_last_addr = last_address;

    HeapRegion *start_region = _hrm.addr_to_region(start_address);
    HeapRegion *last_region = _hrm.addr_to_region(last_address);

    // Check for ranges that start in the same G1 region in which the previous
    // range ended, and adjust the start address so we don't try to free
    // the same region again. If the current range is entirely within that
    // region, skip it.
    if (start_region == prev_last_region)
    {
      start_address = start_region->end();
      if (start_address > last_address)
      {
        continue;
      }
      start_region = _hrm.addr_to_region(start_address);
    }
    prev_last_region = last_region;

    // After verifying that each region was marked as an archive region by
    // alloc_archive_regions, set it free and empty and uncommit it.
    HeapRegion *curr_region = start_region;
    while (curr_region != NULL)
    {
      guarantee(curr_region->is_archive(),
                "Expected archive region at index %u", curr_region->hrm_index());
      uint curr_index = curr_region->hrm_index();
      _archive_set.remove(curr_region);
      curr_region->set_free();
      curr_region->set_top(curr_region->bottom());
      if (curr_region != last_region)
      {
        curr_region = _hrm.next_region_in_heap(curr_region);
      }
      else
      {
        curr_region = NULL;
      }

      _hrm.shrink_at(curr_index, 1);
      shrink_count++;
    }
  }

  if (shrink_count != 0)
  {
    log_debug(gc, ergo, heap)("Attempt heap shrinking (archive regions). Total size: " SIZE_FORMAT "B",
                              HeapRegion::GrainWords * HeapWordSize * shrink_count);
    // Explicit uncommit.
    uncommit_regions(shrink_count);
  }
  decrease_used(size_used);
}

HeapWord *G1CollectedHeap::attempt_allocation_humongous(size_t word_size)
{
  ResourceMark rm; // For retrieving the thread names in log messages.

  // The structure of this method has a lot of similarities to
  // attempt_allocation_slow(). The reason these two were not merged
  // into a single one is that such a method would require several "if
  // allocation is not humongous do this, otherwise do that"
  // conditional paths which would obscure its flow. In fact, an early
  // version of this code did use a unified method which was harder to
  // follow and, as a result, it had subtle bugs that were hard to
  // track down. So keeping these two methods separate allows each to
  // be more readable. It will be good to keep these two in sync as
  // much as possible.

  assert_heap_not_locked_and_not_at_safepoint();
  assert(is_humongous(word_size), "attempt_allocation_humongous() "
                                  "should only be called for humongous allocations");

  // Humongous objects can exhaust the heap quickly, so we should check if we
  // need to start a marking cycle at each humongous object allocation. We do
  // the check before we do the actual allocation. The reason for doing it
  // before the allocation is that we avoid having to keep track of the newly
  // allocated memory while we do a GC.
  if (policy()->need_to_start_conc_mark("concurrent humongous allocation",
                                        word_size))
  {
    collect(GCCause::_g1_humongous_allocation);
  }

  // We will loop until a) we manage to successfully perform the
  // allocation or b) we successfully schedule a collection which
  // fails to perform the allocation. b) is the only case when we'll
  // return NULL.
  HeapWord *result = NULL;
  for (uint try_count = 1, gclocker_retry_count = 0; /* we'll return */; try_count += 1)
  {
    bool should_try_gc;
    bool preventive_collection_required = false;
    uint gc_count_before;

    {
      MutexLocker x(Heap_lock);

      size_t size_in_regions = humongous_obj_size_in_regions(word_size);
      preventive_collection_required = policy()->preventive_collection_required((uint)size_in_regions);
      if (!preventive_collection_required)
      {
        // Given that humongous objects are not allocated in young
        // regions, we'll first try to do the allocation without doing a
        // collection hoping that there's enough space in the heap.
        result = humongous_obj_allocate(word_size);
        if (result != NULL)
        {
          policy()->old_gen_alloc_tracker()->add_allocated_humongous_bytes_since_last_gc(size_in_regions * HeapRegion::GrainBytes);
          return result;
        }
      }

      // Only try a GC if the GCLocker does not signal the need for a GC. Wait until
      // the GCLocker initiated GC has been performed and then retry. This includes
      // the case when the GC Locker is not active but has not been performed.
      should_try_gc = !GCLocker::needs_gc();
      // Read the GC count while still holding the Heap_lock.
      gc_count_before = total_collections();
    }

    if (should_try_gc)
    {
      GCCause::Cause gc_cause = preventive_collection_required ? GCCause::_g1_preventive_collection
                                                               : GCCause::_g1_humongous_allocation;
      bool succeeded;
      result = do_collection_pause(word_size, gc_count_before, &succeeded, gc_cause);
      if (result != NULL)
      {
        assert(succeeded, "only way to get back a non-NULL result");
        log_trace(gc, alloc)("%s: Successfully scheduled collection returning " PTR_FORMAT,
                             Thread::current()->name(), p2i(result));
        size_t size_in_regions = humongous_obj_size_in_regions(word_size);
        policy()->old_gen_alloc_tracker()->record_collection_pause_humongous_allocation(size_in_regions * HeapRegion::GrainBytes);
        return result;
      }

      if (succeeded)
      {
        // We successfully scheduled a collection which failed to allocate. No
        // point in trying to allocate further. We'll just return NULL.
        log_trace(gc, alloc)("%s: Successfully scheduled collection failing to allocate " SIZE_FORMAT " words", Thread::current()->name(), word_size);
        return NULL;
      }
      log_trace(gc, alloc)("%s: Unsuccessfully scheduled collection allocating " SIZE_FORMAT "",
                           Thread::current()->name(), word_size);
    }
    else
    {
      // Failed to schedule a collection.
      if (gclocker_retry_count > GCLockerRetryAllocationCount)
      {
        log_warning(gc, alloc)("%s: Retried waiting for GCLocker too often allocating " SIZE_FORMAT " words", Thread::current()->name(), word_size);
        return NULL;
      }
      log_trace(gc, alloc)("%s: Stall until clear", Thread::current()->name());
      // The GCLocker is either active or the GCLocker initiated
      // GC has not yet been performed. Stall until it is and
      // then retry the allocation.
      GCLocker::stall_until_clear();
      gclocker_retry_count += 1;
    }

    // We can reach here if we were unsuccessful in scheduling a
    // collection (because another thread beat us to it) or if we were
    // stalled due to the GC locker. In either can we should retry the
    // allocation attempt in case another thread successfully
    // performed a collection and reclaimed enough space.
    // Humongous object allocation always needs a lock, so we wait for the retry
    // in the next iteration of the loop, unlike for the regular iteration case.
    // Give a warning if we seem to be looping forever.

    if ((QueuedAllocationWarningCount > 0) &&
        (try_count % QueuedAllocationWarningCount == 0))
    {
      log_warning(gc, alloc)("%s: Retried allocation %u times for " SIZE_FORMAT " words",
                             Thread::current()->name(), try_count, word_size);
    }
  }

  ShouldNotReachHere();
  return NULL;
}

HeapWord *G1CollectedHeap::attempt_allocation_at_safepoint(size_t word_size,
                                                           bool expect_null_mutator_alloc_region)
{
  assert_at_safepoint_on_vm_thread();
  assert(!_allocator->has_mutator_alloc_region() || !expect_null_mutator_alloc_region,
         "the current alloc region was unexpectedly found to be non-NULL");

  if (!is_humongous(word_size))
  {
    return _allocator->attempt_allocation_locked(word_size);
  }
  else
  {
    HeapWord *result = humongous_obj_allocate(word_size);
    if (result != NULL && policy()->need_to_start_conc_mark("STW humongous allocation"))
    {
      collector_state()->set_initiate_conc_mark_if_possible(true);
    }
    return result;
  }

  ShouldNotReachHere();
}

class PostCompactionPrinterClosure : public HeapRegionClosure
{
private:
  G1HRPrinter *_hr_printer;

public:
  bool do_heap_region(HeapRegion *hr)
  {
    assert(!hr->is_young(), "not expecting to find young regions");
    _hr_printer->post_compaction(hr);
    return false;
  }

  PostCompactionPrinterClosure(G1HRPrinter *hr_printer)
      : _hr_printer(hr_printer) {}
};

void G1CollectedHeap::print_heap_after_full_collection()
{
  // Post collection region logging.
  // We should do this after we potentially resize the heap so
  // that all the COMMIT / UNCOMMIT events are generated before
  // the compaction events.
  if (_hr_printer.is_active())
  {
    PostCompactionPrinterClosure cl(hr_printer());
    heap_region_iterate(&cl);
  }
}

void G1CollectedHeap::abort_concurrent_cycle()
{
  // If we start the compaction before the CM threads finish
  // scanning the root regions we might trip them over as we'll
  // be moving objects / updating references. So let's wait until
  // they are done. By telling them to abort, they should complete
  // early.
  _cm->root_regions()->abort();
  _cm->root_regions()->wait_until_scan_finished();

  // Disable discovery and empty the discovered lists
  // for the CM ref processor.
  _ref_processor_cm->disable_discovery();
  _ref_processor_cm->abandon_partial_discovery();
  _ref_processor_cm->verify_no_references_recorded();

  // Abandon current iterations of concurrent marking and concurrent
  // refinement, if any are in progress.
  concurrent_mark()->concurrent_cycle_abort();
}

void G1CollectedHeap::prepare_heap_for_full_collection()
{
  // Make sure we'll choose a new allocation region afterwards.
  _allocator->release_mutator_alloc_regions();
  _allocator->abandon_gc_alloc_regions();

  // We may have added regions to the current incremental collection
  // set between the last GC or pause and now. We need to clear the
  // incremental collection set and then start rebuilding it afresh
  // after this full GC.
  abandon_collection_set(collection_set());

  _hrm.remove_all_free_regions();
}

void G1CollectedHeap::verify_before_full_collection(bool explicit_gc)
{
  assert(!GCCause::is_user_requested_gc(gc_cause()) || explicit_gc, "invariant");
  assert_used_and_recalculate_used_equal(this);
  _verifier->verify_region_sets_optional();
  _verifier->verify_before_gc(G1HeapVerifier::G1VerifyFull);
  _verifier->check_bitmaps("Full GC Start");
}

void G1CollectedHeap::prepare_heap_for_mutators()
{
  // Delete metaspaces for unloaded class loaders and clean up loader_data graph
  ClassLoaderDataGraph::purge(/*at_safepoint*/ true);
  DEBUG_ONLY(MetaspaceUtils::verify();)

  // Prepare heap for normal collections.
  assert(num_free_regions() == 0, "we should not have added any free regions");
  rebuild_region_sets(false /* free_list_only */);
  abort_refinement();
  resize_heap_if_necessary();
  uncommit_regions_if_necessary();

  // Rebuild the strong code root lists for each region
  rebuild_strong_code_roots();

  // Purge code root memory
  purge_code_root_memory();

  // Start a new incremental collection set for the next pause
  start_new_collection_set();

  _allocator->init_mutator_alloc_regions();

  // Post collection state updates.
  MetaspaceGC::compute_new_size();
}

void G1CollectedHeap::abort_refinement()
{
  if (_hot_card_cache->use_cache())
  {
    _hot_card_cache->reset_hot_cache();
  }

  // Discard all remembered set updates and reset refinement statistics.
  G1BarrierSet::dirty_card_queue_set().abandon_logs();
  assert(G1BarrierSet::dirty_card_queue_set().num_cards() == 0,
         "DCQS should be empty");
  concurrent_refine()->get_and_reset_refinement_stats();
}

void G1CollectedHeap::verify_after_full_collection()
{
  _hrm.verify_optional();
  _verifier->verify_region_sets_optional();
  _verifier->verify_after_gc(G1HeapVerifier::G1VerifyFull);

  // This call implicitly verifies that the next bitmap is clear after Full GC.
  _verifier->check_bitmaps("Full GC End");

  // At this point there should be no regions in the
  // entire heap tagged as young.
  assert(check_young_list_empty(), "young list should be empty at this point");

  // Note: since we've just done a full GC, concurrent
  // marking is no longer active. Therefore we need not
  // re-enable reference discovery for the CM ref processor.
  // That will be done at the start of the next marking cycle.
  // We also know that the STW processor should no longer
  // discover any new references.
  assert(!_ref_processor_stw->discovery_enabled(), "Postcondition");
  assert(!_ref_processor_cm->discovery_enabled(), "Postcondition");
  _ref_processor_stw->verify_no_references_recorded();
  _ref_processor_cm->verify_no_references_recorded();
}

bool G1CollectedHeap::do_full_collection(bool explicit_gc,
                                         bool clear_all_soft_refs,
                                         bool do_maximum_compaction)
{
  assert_at_safepoint_on_vm_thread();

  if (GCLocker::check_active_before_gc())
  {
    // Full GC was not completed.
    return false;
  }

  const bool do_clear_all_soft_refs = clear_all_soft_refs ||
                                      soft_ref_policy()->should_clear_all_soft_refs();

  G1FullGCMark gc_mark;
  GCTraceTime(Info, gc) tm("Pause Full", NULL, gc_cause(), true);
  G1FullCollector collector(this, explicit_gc, do_clear_all_soft_refs, do_maximum_compaction, gc_mark.tracer());

  collector.prepare_collection();
  collector.collect();
  collector.complete_collection();

  // Full collection was successfully completed.
  return true;
}

void G1CollectedHeap::do_full_collection(bool clear_all_soft_refs)
{
  // Currently, there is no facility in the do_full_collection(bool) API to notify
  // the caller that the collection did not succeed (e.g., because it was locked
  // out by the GC locker). So, right now, we'll ignore the return value.
  // When clear_all_soft_refs is set we want to do a maximum compaction
  // not leaving any dead wood.
  bool do_maximum_compaction = clear_all_soft_refs;
  bool dummy = do_full_collection(true, /* explicit_gc */
                                  clear_all_soft_refs,
                                  do_maximum_compaction);
}

bool G1CollectedHeap::upgrade_to_full_collection()
{
  GCCauseSetter compaction(this, GCCause::_g1_compaction_pause);
  log_info(gc, ergo)("Attempting full compaction clearing soft references");
  bool success = do_full_collection(false /* explicit gc */,
                                    true /* clear_all_soft_refs */,
                                    false /* do_maximum_compaction */);
  // do_full_collection only fails if blocked by GC locker and that can't
  // be the case here since we only call this when already completed one gc.
  assert(success, "invariant");
  return success;
}

void G1CollectedHeap::resize_heap_if_necessary()
{
  assert_at_safepoint_on_vm_thread();

  bool should_expand;
  size_t resize_amount = _heap_sizing_policy->full_collection_resize_amount(should_expand);

  if (resize_amount == 0)
  {
    return;
  }
  else if (should_expand)
  {
    expand(resize_amount, _workers);
  }
  else
  {
    shrink(resize_amount);
  }
}

HeapWord *G1CollectedHeap::satisfy_failed_allocation_helper(size_t word_size,
                                                            bool do_gc,
                                                            bool maximum_compaction,
                                                            bool expect_null_mutator_alloc_region,
                                                            bool *gc_succeeded)
{
  *gc_succeeded = true;
  // Let's attempt the allocation first.
  HeapWord *result =
      attempt_allocation_at_safepoint(word_size,
                                      expect_null_mutator_alloc_region);
  if (result != NULL)
  {
    return result;
  }

  // In a G1 heap, we're supposed to keep allocation from failing by
  // incremental pauses.  Therefore, at least for now, we'll favor
  // expansion over collection.  (This might change in the future if we can
  // do something smarter than full collection to satisfy a failed alloc.)
  result = expand_and_allocate(word_size);
  if (result != NULL)
  {
    return result;
  }

  if (do_gc)
  {
    GCCauseSetter compaction(this, GCCause::_g1_compaction_pause);
    // Expansion didn't work, we'll try to do a Full GC.
    // If maximum_compaction is set we clear all soft references and don't
    // allow any dead wood to be left on the heap.
    if (maximum_compaction)
    {
      log_info(gc, ergo)("Attempting maximum full compaction clearing soft references");
    }
    else
    {
      log_info(gc, ergo)("Attempting full compaction");
    }
    *gc_succeeded = do_full_collection(false, /* explicit_gc */
                                       maximum_compaction /* clear_all_soft_refs */,
                                       maximum_compaction /* do_maximum_compaction */);
  }

  return NULL;
}

HeapWord *G1CollectedHeap::satisfy_failed_allocation(size_t word_size,
                                                     bool *succeeded)
{
  assert_at_safepoint_on_vm_thread();

  // Attempts to allocate followed by Full GC.
  HeapWord *result =
      satisfy_failed_allocation_helper(word_size,
                                       true,  /* do_gc */
                                       false, /* maximum_collection */
                                       false, /* expect_null_mutator_alloc_region */
                                       succeeded);

  if (result != NULL || !*succeeded)
  {
    return result;
  }

  // Attempts to allocate followed by Full GC that will collect all soft references.
  result = satisfy_failed_allocation_helper(word_size,
                                            true, /* do_gc */
                                            true, /* maximum_collection */
                                            true, /* expect_null_mutator_alloc_region */
                                            succeeded);

  if (result != NULL || !*succeeded)
  {
    return result;
  }

  // Attempts to allocate, no GC
  result = satisfy_failed_allocation_helper(word_size,
                                            false, /* do_gc */
                                            false, /* maximum_collection */
                                            true,  /* expect_null_mutator_alloc_region */
                                            succeeded);

  if (result != NULL)
  {
    return result;
  }

  assert(!soft_ref_policy()->should_clear_all_soft_refs(),
         "Flag should have been handled and cleared prior to this point");

  // What else?  We might try synchronous finalization later.  If the total
  // space available is large enough for the allocation, then a more
  // complete compaction phase than we've tried so far might be
  // appropriate.
  return NULL;
}

// Attempting to expand the heap sufficiently
// to support an allocation of the given "word_size".  If
// successful, perform the allocation and return the address of the
// allocated block, or else "NULL".

HeapWord *G1CollectedHeap::expand_and_allocate(size_t word_size)
{
  assert_at_safepoint_on_vm_thread();

  _verifier->verify_region_sets_optional();

  size_t expand_bytes = MAX2(word_size * HeapWordSize, MinHeapDeltaBytes);
  log_debug(gc, ergo, heap)("Attempt heap expansion (allocation request failed). Allocation request: " SIZE_FORMAT "B",
                            word_size * HeapWordSize);

  if (expand(expand_bytes, _workers))
  {
    _hrm.verify_optional();
    _verifier->verify_region_sets_optional();
    return attempt_allocation_at_safepoint(word_size,
                                           false /* expect_null_mutator_alloc_region */);
  }
  return NULL;
}

bool G1CollectedHeap::expand(size_t expand_bytes, WorkGang *pretouch_workers, double *expand_time_ms)
{
  size_t aligned_expand_bytes = ReservedSpace::page_align_size_up(expand_bytes);
  aligned_expand_bytes = align_up(aligned_expand_bytes,
                                  HeapRegion::GrainBytes);

  log_debug(gc, ergo, heap)("Expand the heap. requested expansion amount: " SIZE_FORMAT "B expansion amount: " SIZE_FORMAT "B",
                            expand_bytes, aligned_expand_bytes);

  if (is_maximal_no_gc())
  {
    log_debug(gc, ergo, heap)("Did not expand the heap (heap already fully expanded)");
    return false;
  }

  double expand_heap_start_time_sec = os::elapsedTime();
  uint regions_to_expand = (uint)(aligned_expand_bytes / HeapRegion::GrainBytes);
  assert(regions_to_expand > 0, "Must expand by at least one region");

  uint expanded_by = _hrm.expand_by(regions_to_expand, pretouch_workers);
  if (expand_time_ms != NULL)
  {
    *expand_time_ms = (os::elapsedTime() - expand_heap_start_time_sec) * MILLIUNITS;
  }

  if (expanded_by > 0)
  {
    size_t actual_expand_bytes = expanded_by * HeapRegion::GrainBytes;
    assert(actual_expand_bytes <= aligned_expand_bytes, "post-condition");
    policy()->record_new_heap_size(num_regions());
  }
  else
  {
    log_debug(gc, ergo, heap)("Did not expand the heap (heap expansion operation failed)");

    // The expansion of the virtual storage space was unsuccessful.
    // Let's see if it was because we ran out of swap.
    if (G1ExitOnExpansionFailure &&
        _hrm.available() >= regions_to_expand)
    {
      // We had head room...
      vm_exit_out_of_memory(aligned_expand_bytes, OOM_MMAP_ERROR, "G1 heap expansion");
    }
  }
  return regions_to_expand > 0;
}

bool G1CollectedHeap::expand_single_region(uint node_index)
{
  uint expanded_by = _hrm.expand_on_preferred_node(node_index);

  if (expanded_by == 0)
  {
    assert(is_maximal_no_gc(), "Should be no regions left, available: %u", _hrm.available());
    log_debug(gc, ergo, heap)("Did not expand the heap (heap already fully expanded)");
    return false;
  }

  policy()->record_new_heap_size(num_regions());
  return true;
}

void G1CollectedHeap::shrink_helper(size_t shrink_bytes)
{
  size_t aligned_shrink_bytes =
      ReservedSpace::page_align_size_down(shrink_bytes);
  aligned_shrink_bytes = align_down(aligned_shrink_bytes,
                                    HeapRegion::GrainBytes);
  uint num_regions_to_remove = (uint)(shrink_bytes / HeapRegion::GrainBytes);

  uint num_regions_removed = _hrm.shrink_by(num_regions_to_remove);
  size_t shrunk_bytes = num_regions_removed * HeapRegion::GrainBytes;

  log_debug(gc, ergo, heap)("Shrink the heap. requested shrinking amount: " SIZE_FORMAT "B aligned shrinking amount: " SIZE_FORMAT "B attempted shrinking amount: " SIZE_FORMAT "B",
                            shrink_bytes, aligned_shrink_bytes, shrunk_bytes);
  if (num_regions_removed > 0)
  {
    log_debug(gc, heap)("Uncommittable regions after shrink: %u", num_regions_removed);
    policy()->record_new_heap_size(num_regions());
  }
  else
  {
    log_debug(gc, ergo, heap)("Did not expand the heap (heap shrinking operation failed)");
  }
}

void G1CollectedHeap::shrink(size_t shrink_bytes)
{
  _verifier->verify_region_sets_optional();

  // We should only reach here at the end of a Full GC or during Remark which
  // means we should not not be holding to any GC alloc regions. The method
  // below will make sure of that and do any remaining clean up.
  _allocator->abandon_gc_alloc_regions();

  // Instead of tearing down / rebuilding the free lists here, we
  // could instead use the remove_all_pending() method on free_list to
  // remove only the ones that we need to remove.
  _hrm.remove_all_free_regions();
  shrink_helper(shrink_bytes);
  rebuild_region_sets(true /* free_list_only */);

  _hrm.verify_optional();
  _verifier->verify_region_sets_optional();
}

class OldRegionSetChecker : public HeapRegionSetChecker
{
public:
  void check_mt_safety()
  {
    // Master Old Set MT safety protocol:
    // (a) If we're at a safepoint, operations on the master old set
    // should be invoked:
    // - by the VM thread (which will serialize them), or
    // - by the GC workers while holding the FreeList_lock, if we're
    //   at a safepoint for an evacuation pause (this lock is taken
    //   anyway when an GC alloc region is retired so that a new one
    //   is allocated from the free list), or
    // - by the GC workers while holding the OldSets_lock, if we're at a
    //   safepoint for a cleanup pause.
    // (b) If we're not at a safepoint, operations on the master old set
    // should be invoked while holding the Heap_lock.

    if (SafepointSynchronize::is_at_safepoint())
    {
      guarantee(Thread::current()->is_VM_thread() ||
                    FreeList_lock->owned_by_self() || OldSets_lock->owned_by_self(),
                "master old set MT safety protocol at a safepoint");
    }
    else
    {
      guarantee(Heap_lock->owned_by_self(), "master old set MT safety protocol outside a safepoint");
    }
  }
  bool is_correct_type(HeapRegion *hr) { return hr->is_old(); }
  const char *get_description() { return "Old Regions"; }
};

class ArchiveRegionSetChecker : public HeapRegionSetChecker
{
public:
  void check_mt_safety()
  {
    guarantee(!Universe::is_fully_initialized() || SafepointSynchronize::is_at_safepoint(),
              "May only change archive regions during initialization or safepoint.");
  }
  bool is_correct_type(HeapRegion *hr) { return hr->is_archive(); }
  const char *get_description() { return "Archive Regions"; }
};

class HumongousRegionSetChecker : public HeapRegionSetChecker
{
public:
  void check_mt_safety()
  {
    // Humongous Set MT safety protocol:
    // (a) If we're at a safepoint, operations on the master humongous
    // set should be invoked by either the VM thread (which will
    // serialize them) or by the GC workers while holding the
    // OldSets_lock.
    // (b) If we're not at a safepoint, operations on the master
    // humongous set should be invoked while holding the Heap_lock.

    if (SafepointSynchronize::is_at_safepoint())
    {
      guarantee(Thread::current()->is_VM_thread() ||
                    OldSets_lock->owned_by_self(),
                "master humongous set MT safety protocol at a safepoint");
    }
    else
    {
      guarantee(Heap_lock->owned_by_self(),
                "master humongous set MT safety protocol outside a safepoint");
    }
  }
  bool is_correct_type(HeapRegion *hr) { return hr->is_humongous(); }
  const char *get_description() { return "Humongous Regions"; }
};

G1CollectedHeap::G1CollectedHeap() : CollectedHeap(),
                                     _service_thread(NULL),
                                     _periodic_gc_task(NULL),
                                     _workers(NULL),
                                     _card_table(NULL),
                                     _collection_pause_end(Ticks::now()),
                                     _soft_ref_policy(),
                                     _old_set("Old Region Set", new OldRegionSetChecker()),
                                     _archive_set("Archive Region Set", new ArchiveRegionSetChecker()),
                                     _humongous_set("Humongous Region Set", new HumongousRegionSetChecker()),
                                     _bot(NULL),
                                     _listener(),
                                     _numa(G1NUMA::create()),
                                     _hrm(),
                                     _allocator(NULL),
                                     _verifier(NULL),
                                     _summary_bytes_used(0),
                                     _bytes_used_during_gc(0),
                                     _archive_allocator(NULL),
                                     _survivor_evac_stats("Young", YoungPLABSize, PLABWeight),
                                     _old_evac_stats("Old", OldPLABSize, PLABWeight),
                                     _expand_heap_after_alloc_failure(true),
                                     _g1mm(NULL),
                                     _humongous_reclaim_candidates(),
                                     _num_humongous_objects(0),
                                     _num_humongous_reclaim_candidates(0),
                                     _hr_printer(),
                                     _collector_state(),
                                     _old_marking_cycles_started(0),
                                     _old_marking_cycles_completed(0),
                                     _eden(),
                                     _survivor(),
                                     _gc_timer_stw(new (ResourceObj::C_HEAP, mtGC) STWGCTimer()),
                                     _gc_tracer_stw(new (ResourceObj::C_HEAP, mtGC) G1NewTracer()),
                                     _policy(new G1Policy(_gc_timer_stw)),
                                     _heap_sizing_policy(NULL),
                                     _collection_set(this, _policy),
                                     _hot_card_cache(NULL),
                                     _rem_set(NULL),
                                     _cm(NULL),
                                     _cm_thread(NULL),
                                     _cr(NULL),
                                     _task_queues(NULL),
                                     _num_regions_failed_evacuation(0),
                                     _regions_failed_evacuation(NULL),
                                     _evacuation_failed_info_array(NULL),
                                     _preserved_marks_set(true /* in_c_heap */),
#ifndef PRODUCT
                                     _evacuation_failure_alot_for_current_gc(false),
                                     _evacuation_failure_alot_gc_number(0),
                                     _evacuation_failure_alot_count(0),
#endif
                                     _ref_processor_stw(NULL),
                                     _is_alive_closure_stw(this),
                                     _is_subject_to_discovery_stw(this),
                                     _ref_processor_cm(NULL),
                                     _is_alive_closure_cm(this),
                                     _is_subject_to_discovery_cm(this),
                                     _region_attr()
{

  _verifier = new G1HeapVerifier(this);

  _allocator = new G1Allocator(this);

  _heap_sizing_policy = G1HeapSizingPolicy::create(this, _policy->analytics());

  _humongous_object_threshold_in_words = humongous_threshold_for(HeapRegion::GrainWords);

  // Override the default _filler_array_max_size so that no humongous filler
  // objects are created.
  _filler_array_max_size = _humongous_object_threshold_in_words;

  uint n_queues = ParallelGCThreads;
  _task_queues = new G1ScannerTasksQueueSet(n_queues);

  _evacuation_failed_info_array = NEW_C_HEAP_ARRAY(EvacuationFailedInfo, n_queues, mtGC);

  for (uint i = 0; i < n_queues; i++)
  {
    G1ScannerTasksQueue *q = new G1ScannerTasksQueue();
    q->initialize();
    _task_queues->register_queue(i, q);
    ::new (&_evacuation_failed_info_array[i]) EvacuationFailedInfo();
  }

  // Initialize the G1EvacuationFailureALot counters and flags.
  NOT_PRODUCT(reset_evacuation_should_fail();)
  _gc_tracer_stw->initialize();

  guarantee(_task_queues != NULL, "task_queues allocation failure.");
}

G1RegionToSpaceMapper *G1CollectedHeap::create_aux_memory_mapper(const char *description,
                                                                 size_t size,
                                                                 size_t translation_factor)
{
  size_t preferred_page_size = os::page_size_for_region_unaligned(size, 1);
  // Allocate a new reserved space, preferring to use large pages.
  ReservedSpace rs(size, preferred_page_size);
  size_t page_size = rs.page_size();
  G1RegionToSpaceMapper *result =
      G1RegionToSpaceMapper::create_mapper(rs,
                                           size,
                                           page_size,
                                           HeapRegion::GrainBytes,
                                           translation_factor,
                                           mtGC);

  os::trace_page_sizes_for_requested_size(description,
                                          size,
                                          page_size,
                                          preferred_page_size,
                                          rs.base(),
                                          rs.size());

  return result;
}

jint G1CollectedHeap::initialize_concurrent_refinement()
{
  jint ecode = JNI_OK;
  _cr = G1ConcurrentRefine::create(&ecode);
  return ecode;
}

jint G1CollectedHeap::initialize_service_thread()
{
  _service_thread = new G1ServiceThread();
  if (_service_thread->osthread() == NULL)
  {
    vm_shutdown_during_initialization("Could not create G1ServiceThread");
    return JNI_ENOMEM;
  }
  return JNI_OK;
}

jint G1CollectedHeap::initialize()
{

  // Necessary to satisfy locking discipline assertions.

  MutexLocker x(Heap_lock);

  // While there are no constraints in the GC code that HeapWordSize
  // be any particular value, there are multiple other areas in the
  // system which believe this to be true (e.g. oop->object_size in some
  // cases incorrectly returns the size in wordSize units rather than
  // HeapWordSize).
  guarantee(HeapWordSize == wordSize, "HeapWordSize must equal wordSize");

  size_t init_byte_size = InitialHeapSize;
  size_t reserved_byte_size = G1Arguments::heap_reserved_size_bytes();

  // Ensure that the sizes are properly aligned.
  Universe::check_alignment(init_byte_size, HeapRegion::GrainBytes, "g1 heap");
  Universe::check_alignment(reserved_byte_size, HeapRegion::GrainBytes, "g1 heap");
  Universe::check_alignment(reserved_byte_size, HeapAlignment, "g1 heap");

  // Reserve the maximum.

  // When compressed oops are enabled, the preferred heap base
  // is calculated by subtracting the requested size from the
  // 32Gb boundary and using the result as the base address for
  // heap reservation. If the requested size is not aligned to
  // HeapRegion::GrainBytes (i.e. the alignment that is passed
  // into the ReservedHeapSpace constructor) then the actual
  // base of the reserved heap may end up differing from the
  // address that was requested (i.e. the preferred heap base).
  // If this happens then we could end up using a non-optimal
  // compressed oops mode.

  ReservedHeapSpace heap_rs = Universe::reserve_heap(reserved_byte_size,
                                                     HeapAlignment);

  initialize_reserved_region(heap_rs);

  // Create the barrier set for the entire reserved region.
  G1CardTable *ct = new G1CardTable(heap_rs.region());
  ct->initialize();
  G1BarrierSet *bs = new G1BarrierSet(ct);
  bs->initialize();
  assert(bs->is_a(BarrierSet::G1BarrierSet), "sanity");
  BarrierSet::set_barrier_set(bs);
  _card_table = ct;

  {
    G1SATBMarkQueueSet &satbqs = bs->satb_mark_queue_set();
    satbqs.set_process_completed_buffers_threshold(G1SATBProcessCompletedThreshold);
    satbqs.set_buffer_enqueue_threshold_percentage(G1SATBBufferEnqueueingThresholdPercent);
  }

  // Create the hot card cache.
  _hot_card_cache = new G1HotCardCache(this);

  // Create space mappers.
  size_t page_size = heap_rs.page_size();
  G1RegionToSpaceMapper *heap_storage =
      G1RegionToSpaceMapper::create_mapper(heap_rs,
                                           heap_rs.size(),
                                           page_size,
                                           HeapRegion::GrainBytes,
                                           1,
                                           mtJavaHeap);
  if (heap_storage == NULL)
  {
    vm_shutdown_during_initialization("Could not initialize G1 heap");
    return JNI_ERR;
  }

  os::trace_page_sizes("Heap",
                       MinHeapSize,
                       reserved_byte_size,
                       page_size,
                       heap_rs.base(),
                       heap_rs.size());
  heap_storage->set_mapping_changed_listener(&_listener);

  // Create storage for the BOT, card table, card counts table (hot card cache) and the bitmaps.
  G1RegionToSpaceMapper *bot_storage =
      create_aux_memory_mapper("Block Offset Table",
                               G1BlockOffsetTable::compute_size(heap_rs.size() / HeapWordSize),
                               G1BlockOffsetTable::heap_map_factor());

  G1RegionToSpaceMapper *cardtable_storage =
      create_aux_memory_mapper("Card Table",
                               G1CardTable::compute_size(heap_rs.size() / HeapWordSize),
                               G1CardTable::heap_map_factor());

  G1RegionToSpaceMapper *card_counts_storage =
      create_aux_memory_mapper("Card Counts Table",
                               G1CardCounts::compute_size(heap_rs.size() / HeapWordSize),
                               G1CardCounts::heap_map_factor());

  size_t bitmap_size = G1CMBitMap::compute_size(heap_rs.size());
  G1RegionToSpaceMapper *prev_bitmap_storage =
      create_aux_memory_mapper("Prev Bitmap", bitmap_size, G1CMBitMap::heap_map_factor());
  G1RegionToSpaceMapper *next_bitmap_storage =
      create_aux_memory_mapper("Next Bitmap", bitmap_size, G1CMBitMap::heap_map_factor());

  _hrm.initialize(heap_storage, prev_bitmap_storage, next_bitmap_storage, bot_storage, cardtable_storage, card_counts_storage);
  _card_table->initialize(cardtable_storage);

  // Do later initialization work for concurrent refinement.
  _hot_card_cache->initialize(card_counts_storage);

  // 6843694 - ensure that the maximum region index can fit
  // in the remembered set structures.
  const uint max_region_idx = (1U << (sizeof(RegionIdx_t) * BitsPerByte - 1)) - 1;
  guarantee((max_reserved_regions() - 1) <= max_region_idx, "too many regions");

  // The G1FromCardCache reserves card with value 0 as "invalid", so the heap must not
  // start within the first card.
  guarantee(heap_rs.base() >= (char *)G1CardTable::card_size, "Java heap must not start within the first card.");
  G1FromCardCache::initialize(max_reserved_regions());
  // Also create a G1 rem set.
  _rem_set = new G1RemSet(this, _card_table, _hot_card_cache);
  _rem_set->initialize(max_reserved_regions());

  size_t max_cards_per_region = ((size_t)1 << (sizeof(CardIdx_t) * BitsPerByte - 1)) - 1;
  guarantee(HeapRegion::CardsPerRegion > 0, "make sure it's initialized");
  guarantee(HeapRegion::CardsPerRegion < max_cards_per_region,
            "too many cards per region");

  FreeRegionList::set_unrealistically_long_length(max_regions() + 1);

  _bot = new G1BlockOffsetTable(reserved(), bot_storage);

  {
    size_t granularity = HeapRegion::GrainBytes;

    _region_attr.initialize(reserved(), granularity);
    _humongous_reclaim_candidates.initialize(reserved(), granularity);
  }

  _workers = new WorkGang("GC Thread", ParallelGCThreads,
                          true /* are_GC_task_threads */,
                          false /* are_ConcurrentGC_threads */);
  if (_workers == NULL)
  {
    return JNI_ENOMEM;
  }
  _workers->initialize_workers();

  _numa->set_region_info(HeapRegion::GrainBytes, page_size);

  // Create the G1ConcurrentMark data structure and thread.
  // (Must do this late, so that "max_[reserved_]regions" is defined.)
  _cm = new G1ConcurrentMark(this, prev_bitmap_storage, next_bitmap_storage);
  _cm_thread = _cm->cm_thread();

  // Now expand into the initial heap size.
  if (!expand(init_byte_size, _workers))
  {
    vm_shutdown_during_initialization("Failed to allocate initial heap.");
    return JNI_ENOMEM;
  }

  // Perform any initialization actions delegated to the policy.
  policy()->init(this, &_collection_set);

  jint ecode = initialize_concurrent_refinement();
  if (ecode != JNI_OK)
  {
    return ecode;
  }

  ecode = initialize_service_thread();
  if (ecode != JNI_OK)
  {
    return ecode;
  }

  // Initialize and schedule sampling task on service thread.
  _rem_set->initialize_sampling_task(service_thread());

  // Create and schedule the periodic gc task on the service thread.
  _periodic_gc_task = new G1PeriodicGCTask("Periodic GC Task");
  _service_thread->register_task(_periodic_gc_task);

  {
    G1DirtyCardQueueSet &dcqs = G1BarrierSet::dirty_card_queue_set();
    dcqs.set_process_cards_threshold(concurrent_refine()->yellow_zone());
    dcqs.set_max_cards(concurrent_refine()->red_zone());
  }

  // Here we allocate the dummy HeapRegion that is required by the
  // G1AllocRegion class.
  HeapRegion *dummy_region = _hrm.get_dummy_region();

  // We'll re-use the same region whether the alloc region will
  // require BOT updates or not and, if it doesn't, then a non-young
  // region will complain that it cannot support allocations without
  // BOT updates. So we'll tag the dummy region as eden to avoid that.
  dummy_region->set_eden();
  // Make sure it's full.
  dummy_region->set_top(dummy_region->end());
  G1AllocRegion::setup(this, dummy_region);

  _allocator->init_mutator_alloc_regions();

  // Do create of the monitoring and management support so that
  // values in the heap have been properly initialized.
  _g1mm = new G1MonitoringSupport(this);

  _preserved_marks_set.init(ParallelGCThreads);

  _collection_set.initialize(max_reserved_regions());

  _regions_failed_evacuation = NEW_C_HEAP_ARRAY(volatile bool, max_regions(), mtGC);

  G1InitLogger::print();

  return JNI_OK;
}

void G1CollectedHeap::stop()
{
  // Stop all concurrent threads. We do this to make sure these threads
  // do not continue to execute and access resources (e.g. logging)
  // that are destroyed during shutdown.
  _cr->stop();
  _service_thread->stop();
  _cm_thread->stop();
}

void G1CollectedHeap::safepoint_synchronize_begin()
{
  SuspendibleThreadSet::synchronize();
}

void G1CollectedHeap::safepoint_synchronize_end()
{
  SuspendibleThreadSet::desynchronize();
}

void G1CollectedHeap::post_initialize()
{
  CollectedHeap::post_initialize();
  ref_processing_init();
}

void G1CollectedHeap::ref_processing_init()
{
  // Reference processing in G1 currently works as follows:
  //
  // * There are two reference processor instances. One is
  //   used to record and process discovered references
  //   during concurrent marking; the other is used to
  //   record and process references during STW pauses
  //   (both full and incremental).
  // * Both ref processors need to 'span' the entire heap as
  //   the regions in the collection set may be dotted around.
  //
  // * For the concurrent marking ref processor:
  //   * Reference discovery is enabled at concurrent start.
  //   * Reference discovery is disabled and the discovered
  //     references processed etc during remarking.
  //   * Reference discovery is MT (see below).
  //   * Reference discovery requires a barrier (see below).
  //   * Reference processing may or may not be MT
  //     (depending on the value of ParallelRefProcEnabled
  //     and ParallelGCThreads).
  //   * A full GC disables reference discovery by the CM
  //     ref processor and abandons any entries on it's
  //     discovered lists.
  //
  // * For the STW processor:
  //   * Non MT discovery is enabled at the start of a full GC.
  //   * Processing and enqueueing during a full GC is non-MT.
  //   * During a full GC, references are processed after marking.
  //
  //   * Discovery (may or may not be MT) is enabled at the start
  //     of an incremental evacuation pause.
  //   * References are processed near the end of a STW evacuation pause.
  //   * For both types of GC:
  //     * Discovery is atomic - i.e. not concurrent.
  //     * Reference discovery will not need a barrier.

  // Concurrent Mark ref processor
  _ref_processor_cm =
      new ReferenceProcessor(&_is_subject_to_discovery_cm,
                             ParallelGCThreads,                              // degree of mt processing
                             (ParallelGCThreads > 1) || (ConcGCThreads > 1), // mt discovery
                             MAX2(ParallelGCThreads, ConcGCThreads),         // degree of mt discovery
                             false,                                          // Reference discovery is not atomic
                             &_is_alive_closure_cm);                         // is alive closure

  // STW ref processor
  _ref_processor_stw =
      new ReferenceProcessor(&_is_subject_to_discovery_stw,
                             ParallelGCThreads,       // degree of mt processing
                             (ParallelGCThreads > 1), // mt discovery
                             ParallelGCThreads,       // degree of mt discovery
                             true,                    // Reference discovery is atomic
                             &_is_alive_closure_stw); // is alive closure
}

SoftRefPolicy *G1CollectedHeap::soft_ref_policy()
{
  return &_soft_ref_policy;
}

size_t G1CollectedHeap::capacity() const
{
  return _hrm.length() * HeapRegion::GrainBytes;
}

size_t G1CollectedHeap::unused_committed_regions_in_bytes() const
{
  return _hrm.total_free_bytes();
}

void G1CollectedHeap::iterate_hcc_closure(G1CardTableEntryClosure *cl, uint worker_id)
{
  _hot_card_cache->drain(cl, worker_id);
}

// Computes the sum of the storage used by the various regions.
size_t G1CollectedHeap::used() const
{
  size_t result = _summary_bytes_used + _allocator->used_in_alloc_regions();
  if (_archive_allocator != NULL)
  {
    result += _archive_allocator->used();
  }
  return result;
}

size_t G1CollectedHeap::used_unlocked() const
{
  return _summary_bytes_used;
}

class SumUsedClosure : public HeapRegionClosure
{
  size_t _used;

public:
  SumUsedClosure() : _used(0) {}
  bool do_heap_region(HeapRegion *r)
  {
    _used += r->used();
    return false;
  }
  size_t result() { return _used; }
};

size_t G1CollectedHeap::recalculate_used() const
{
  SumUsedClosure blk;
  heap_region_iterate(&blk);
  return blk.result();
}

bool G1CollectedHeap::is_user_requested_concurrent_full_gc(GCCause::Cause cause)
{
  switch (cause)
  {
  case GCCause::_java_lang_system_gc:
    return ExplicitGCInvokesConcurrent;
  case GCCause::_dcmd_gc_run:
    return ExplicitGCInvokesConcurrent;
  case GCCause::_wb_conc_mark:
    return true;
  default:
    return false;
  }
}

bool G1CollectedHeap::should_do_concurrent_full_gc(GCCause::Cause cause)
{
  switch (cause)
  {
  case GCCause::_g1_humongous_allocation:
    return true;
  case GCCause::_g1_periodic_collection:
    return G1PeriodicGCInvokesConcurrent;
  case GCCause::_wb_breakpoint:
    return true;
  default:
    return is_user_requested_concurrent_full_gc(cause);
  }
}

#ifndef PRODUCT
void G1CollectedHeap::allocate_dummy_regions()
{
  // Let's fill up most of the region
  size_t word_size = HeapRegion::GrainWords - 1024;
  // And as a result the region we'll allocate will be humongous.
  guarantee(is_humongous(word_size), "sanity");

  // _filler_array_max_size is set to humongous object threshold
  // but temporarily change it to use CollectedHeap::fill_with_object().
  AutoModifyRestore<size_t> temporarily(_filler_array_max_size, word_size);

  for (uintx i = 0; i < G1DummyRegionsPerGC; ++i)
  {
    // Let's use the existing mechanism for the allocation
    HeapWord *dummy_obj = humongous_obj_allocate(word_size);
    if (dummy_obj != NULL)
    {
      MemRegion mr(dummy_obj, word_size);
      CollectedHeap::fill_with_object(mr);
    }
    else
    {
      // If we can't allocate once, we probably cannot allocate
      // again. Let's get out of the loop.
      break;
    }
  }
}
#endif // !PRODUCT

void G1CollectedHeap::increment_old_marking_cycles_started()
{
  assert(_old_marking_cycles_started == _old_marking_cycles_completed ||
             _old_marking_cycles_started == _old_marking_cycles_completed + 1,
         "Wrong marking cycle count (started: %d, completed: %d)",
         _old_marking_cycles_started, _old_marking_cycles_completed);

  _old_marking_cycles_started++;
}

void G1CollectedHeap::increment_old_marking_cycles_completed(bool concurrent,
                                                             bool whole_heap_examined)
{
  MonitorLocker ml(G1OldGCCount_lock, Mutex::_no_safepoint_check_flag);

  // We assume that if concurrent == true, then the caller is a
  // concurrent thread that was joined the Suspendible Thread
  // Set. If there's ever a cheap way to check this, we should add an
  // assert here.

  // Given that this method is called at the end of a Full GC or of a
  // concurrent cycle, and those can be nested (i.e., a Full GC can
  // interrupt a concurrent cycle), the number of full collections
  // completed should be either one (in the case where there was no
  // nesting) or two (when a Full GC interrupted a concurrent cycle)
  // behind the number of full collections started.

  // This is the case for the inner caller, i.e. a Full GC.
  assert(concurrent ||
             (_old_marking_cycles_started == _old_marking_cycles_completed + 1) ||
             (_old_marking_cycles_started == _old_marking_cycles_completed + 2),
         "for inner caller (Full GC): _old_marking_cycles_started = %u "
         "is inconsistent with _old_marking_cycles_completed = %u",
         _old_marking_cycles_started, _old_marking_cycles_completed);

  // This is the case for the outer caller, i.e. the concurrent cycle.
  assert(!concurrent ||
             (_old_marking_cycles_started == _old_marking_cycles_completed + 1),
         "for outer caller (concurrent cycle): "
         "_old_marking_cycles_started = %u "
         "is inconsistent with _old_marking_cycles_completed = %u",
         _old_marking_cycles_started, _old_marking_cycles_completed);

  _old_marking_cycles_completed += 1;
  if (whole_heap_examined)
  {
    // Signal that we have completed a visit to all live objects.
    record_whole_heap_examined_timestamp();
  }

  // We need to clear the "in_progress" flag in the CM thread before
  // we wake up any waiters (especially when ExplicitInvokesConcurrent
  // is set) so that if a waiter requests another System.gc() it doesn't
  // incorrectly see that a marking cycle is still in progress.
  if (concurrent)
  {
    _cm_thread->set_idle();
  }

  // Notify threads waiting in System.gc() (with ExplicitGCInvokesConcurrent)
  // for a full GC to finish that their wait is over.
  ml.notify_all();
}

void G1CollectedHeap::collect(GCCause::Cause cause)
{
  try_collect(cause);
}

// Return true if (x < y) with allowance for wraparound.
static bool gc_counter_less_than(uint x, uint y)
{
  return (x - y) > (UINT_MAX / 2);
}

// LOG_COLLECT_CONCURRENTLY(cause, msg, args...)
// Macro so msg printing is format-checked.
#define LOG_COLLECT_CONCURRENTLY(cause, ...)                                  \
  do                                                                          \
  {                                                                           \
    LogTarget(Trace, gc) LOG_COLLECT_CONCURRENTLY_lt;                         \
    if (LOG_COLLECT_CONCURRENTLY_lt.is_enabled())                             \
    {                                                                         \
      ResourceMark rm; /* For thread name. */                                 \
      LogStream LOG_COLLECT_CONCURRENTLY_s(&LOG_COLLECT_CONCURRENTLY_lt);     \
      LOG_COLLECT_CONCURRENTLY_s.print("%s: Try Collect Concurrently (%s): ", \
                                       Thread::current()->name(),             \
                                       GCCause::to_string(cause));            \
      LOG_COLLECT_CONCURRENTLY_s.print(__VA_ARGS__);                          \
    }                                                                         \
  } while (0)

#define LOG_COLLECT_CONCURRENTLY_COMPLETE(cause, result) \
  LOG_COLLECT_CONCURRENTLY(cause, "complete %s", BOOL_TO_STR(result))

bool G1CollectedHeap::try_collect_concurrently(GCCause::Cause cause,
                                               uint gc_counter,
                                               uint old_marking_started_before)
{
  assert_heap_not_locked();
  assert(should_do_concurrent_full_gc(cause),
         "Non-concurrent cause %s", GCCause::to_string(cause));

  for (uint i = 1; true; ++i)
  {
    // Try to schedule concurrent start evacuation pause that will
    // start a concurrent cycle.
    LOG_COLLECT_CONCURRENTLY(cause, "attempt %u", i);
    VM_G1TryInitiateConcMark op(gc_counter,
                                cause,
                                policy()->max_pause_time_ms());
    VMThread::execute(&op);

    // Request is trivially finished.
    if (cause == GCCause::_g1_periodic_collection)
    {
      LOG_COLLECT_CONCURRENTLY_COMPLETE(cause, op.gc_succeeded());
      return op.gc_succeeded();
    }

    // If VMOp skipped initiating concurrent marking cycle because
    // we're terminating, then we're done.
    if (op.terminating())
    {
      LOG_COLLECT_CONCURRENTLY(cause, "skipped: terminating");
      return false;
    }

    // Lock to get consistent set of values.
    uint old_marking_started_after;
    uint old_marking_completed_after;
    {
      MutexLocker ml(Heap_lock);
      // Update gc_counter for retrying VMOp if needed. Captured here to be
      // consistent with the values we use below for termination tests.  If
      // a retry is needed after a possible wait, and another collection
      // occurs in the meantime, it will cause our retry to be skipped and
      // we'll recheck for termination with updated conditions from that
      // more recent collection.  That's what we want, rather than having
      // our retry possibly perform an unnecessary collection.
      gc_counter = total_collections();
      old_marking_started_after = _old_marking_cycles_started;
      old_marking_completed_after = _old_marking_cycles_completed;
    }

    if (cause == GCCause::_wb_breakpoint)
    {
      if (op.gc_succeeded())
      {
        LOG_COLLECT_CONCURRENTLY_COMPLETE(cause, true);
        return true;
      }
      // When _wb_breakpoint there can't be another cycle or deferred.
      assert(!op.cycle_already_in_progress(), "invariant");
      assert(!op.whitebox_attached(), "invariant");
      // Concurrent cycle attempt might have been cancelled by some other
      // collection, so retry.  Unlike other cases below, we want to retry
      // even if cancelled by a STW full collection, because we really want
      // to start a concurrent cycle.
      if (old_marking_started_before != old_marking_started_after)
      {
        LOG_COLLECT_CONCURRENTLY(cause, "ignoring STW full GC");
        old_marking_started_before = old_marking_started_after;
      }
    }
    else if (!GCCause::is_user_requested_gc(cause))
    {
      // For an "automatic" (not user-requested) collection, we just need to
      // ensure that progress is made.
      //
      // Request is finished if any of
      // (1) the VMOp successfully performed a GC,
      // (2) a concurrent cycle was already in progress,
      // (3) whitebox is controlling concurrent cycles,
      // (4) a new cycle was started (by this thread or some other), or
      // (5) a Full GC was performed.
      // Cases (4) and (5) are detected together by a change to
      // _old_marking_cycles_started.
      //
      // Note that (1) does not imply (4).  If we're still in the mixed
      // phase of an earlier concurrent collection, the request to make the
      // collection a concurrent start won't be honored.  If we don't check for
      // both conditions we'll spin doing back-to-back collections.
      if (op.gc_succeeded() ||
          op.cycle_already_in_progress() ||
          op.whitebox_attached() ||
          (old_marking_started_before != old_marking_started_after))
      {
        LOG_COLLECT_CONCURRENTLY_COMPLETE(cause, true);
        return true;
      }
    }
    else
    { // User-requested GC.
      // For a user-requested collection, we want to ensure that a complete
      // full collection has been performed before returning, but without
      // waiting for more than needed.

      // For user-requested GCs (unlike non-UR), a successful VMOp implies a
      // new cycle was started.  That's good, because it's not clear what we
      // should do otherwise.  Trying again just does back to back GCs.
      // Can't wait for someone else to start a cycle.  And returning fails
      // to meet the goal of ensuring a full collection was performed.
      assert(!op.gc_succeeded() ||
                 (old_marking_started_before != old_marking_started_after),
             "invariant: succeeded %s, started before %u, started after %u",
             BOOL_TO_STR(op.gc_succeeded()),
             old_marking_started_before, old_marking_started_after);

      // Request is finished if a full collection (concurrent or stw)
      // was started after this request and has completed, e.g.
      // started_before < completed_after.
      if (gc_counter_less_than(old_marking_started_before,
                               old_marking_completed_after))
      {
        LOG_COLLECT_CONCURRENTLY_COMPLETE(cause, true);
        return true;
      }

      if (old_marking_started_after != old_marking_completed_after)
      {
        // If there is an in-progress cycle (possibly started by us), then
        // wait for that cycle to complete, e.g.
        // while completed_now < started_after.
        LOG_COLLECT_CONCURRENTLY(cause, "wait");
        MonitorLocker ml(G1OldGCCount_lock);
        while (gc_counter_less_than(_old_marking_cycles_completed,
                                    old_marking_started_after))
        {
          ml.wait();
        }
        // Request is finished if the collection we just waited for was
        // started after this request.
        if (old_marking_started_before != old_marking_started_after)
        {
          LOG_COLLECT_CONCURRENTLY(cause, "complete after wait");
          return true;
        }
      }

      // If VMOp was successful then it started a new cycle that the above
      // wait &etc should have recognized as finishing this request.  This
      // differs from a non-user-request, where gc_succeeded does not imply
      // a new cycle was started.
      assert(!op.gc_succeeded(), "invariant");

      if (op.cycle_already_in_progress())
      {
        // If VMOp failed because a cycle was already in progress, it
        // is now complete.  But it didn't finish this user-requested
        // GC, so try again.
        LOG_COLLECT_CONCURRENTLY(cause, "retry after in-progress");
        continue;
      }
      else if (op.whitebox_attached())
      {
        // If WhiteBox wants control, wait for notification of a state
        // change in the controller, then try again.  Don't wait for
        // release of control, since collections may complete while in
        // control.  Note: This won't recognize a STW full collection
        // while waiting; we can't wait on multiple monitors.
        LOG_COLLECT_CONCURRENTLY(cause, "whitebox control stall");
        MonitorLocker ml(ConcurrentGCBreakpoints::monitor());
        if (ConcurrentGCBreakpoints::is_controlled())
        {
          ml.wait();
        }
        continue;
      }
    }

    // Collection failed and should be retried.
    assert(op.transient_failure(), "invariant");

    if (GCLocker::is_active_and_needs_gc())
    {
      // If GCLocker is active, wait until clear before retrying.
      LOG_COLLECT_CONCURRENTLY(cause, "gc-locker stall");
      GCLocker::stall_until_clear();
    }

    LOG_COLLECT_CONCURRENTLY(cause, "retry");
  }
}

bool G1CollectedHeap::try_collect(GCCause::Cause cause)
{
  assert_heap_not_locked();

  // Lock to get consistent set of values.
  uint gc_count_before;
  uint full_gc_count_before;
  uint old_marking_started_before;
  {
    MutexLocker ml(Heap_lock);
    gc_count_before = total_collections();
    full_gc_count_before = total_full_collections();
    old_marking_started_before = _old_marking_cycles_started;
  }

  if (should_do_concurrent_full_gc(cause))
  {
    return try_collect_concurrently(cause,
                                    gc_count_before,
                                    old_marking_started_before);
  }
  else if (GCLocker::should_discard(cause, gc_count_before))
  {
    // Indicate failure to be consistent with VMOp failure due to
    // another collection slipping in after our gc_count but before
    // our request is processed.
    return false;
  }
  else if (cause == GCCause::_gc_locker || cause == GCCause::_wb_young_gc
                                                        DEBUG_ONLY(|| cause == GCCause::_scavenge_alot))
  {

    // Schedule a standard evacuation pause. We're setting word_size
    // to 0 which means that we are not requesting a post-GC allocation.
    VM_G1CollectForAllocation op(0, /* word_size */
                                 gc_count_before,
                                 cause,
                                 policy()->max_pause_time_ms());
    VMThread::execute(&op);
    return op.gc_succeeded();
  }
  else
  {
    // Schedule a Full GC.
    VM_G1CollectFull op(gc_count_before, full_gc_count_before, cause);
    VMThread::execute(&op);
    return op.gc_succeeded();
  }
}

bool G1CollectedHeap::is_in(const void *p) const
{
  return is_in_reserved(p) && _hrm.is_available(addr_to_region((HeapWord *)p));
}

// Iteration functions.

// Iterates an ObjectClosure over all objects within a HeapRegion.

class IterateObjectClosureRegionClosure : public HeapRegionClosure
{
  ObjectClosure *_cl;

public:
  IterateObjectClosureRegionClosure(ObjectClosure *cl) : _cl(cl) {}
  bool do_heap_region(HeapRegion *r)
  {
    if (!r->is_continues_humongous())
    {
      r->object_iterate(_cl);
    }
    return false;
  }
};

void G1CollectedHeap::object_iterate(ObjectClosure *cl)
{
  IterateObjectClosureRegionClosure blk(cl);
  heap_region_iterate(&blk);
}

class G1ParallelObjectIterator : public ParallelObjectIteratorImpl
{
private:
  G1CollectedHeap *_heap;
  HeapRegionClaimer _claimer;

public:
  G1ParallelObjectIterator(uint thread_num) : _heap(G1CollectedHeap::heap()),
                                              _claimer(thread_num == 0 ? G1CollectedHeap::heap()->workers()->active_workers() : thread_num) {}

  virtual void object_iterate(ObjectClosure *cl, uint worker_id)
  {
    _heap->object_iterate_parallel(cl, worker_id, &_claimer);
  }
};

ParallelObjectIteratorImpl *G1CollectedHeap::parallel_object_iterator(uint thread_num)
{
  return new G1ParallelObjectIterator(thread_num);
}

void G1CollectedHeap::object_iterate_parallel(ObjectClosure *cl, uint worker_id, HeapRegionClaimer *claimer)
{
  IterateObjectClosureRegionClosure blk(cl);
  heap_region_par_iterate_from_worker_offset(&blk, claimer, worker_id);
}

void G1CollectedHeap::keep_alive(oop obj)
{
  G1BarrierSet::enqueue_preloaded(obj);
}

void G1CollectedHeap::heap_region_iterate(HeapRegionClosure *cl) const
{
  _hrm.iterate(cl);
}

void G1CollectedHeap::heap_region_par_iterate_from_worker_offset(HeapRegionClosure *cl,
                                                                 HeapRegionClaimer *hrclaimer,
                                                                 uint worker_id) const
{
  _hrm.par_iterate(cl, hrclaimer, hrclaimer->offset_for_worker(worker_id));
}

void G1CollectedHeap::heap_region_par_iterate_from_start(HeapRegionClosure *cl,
                                                         HeapRegionClaimer *hrclaimer) const
{
  _hrm.par_iterate(cl, hrclaimer, 0);
}

void G1CollectedHeap::collection_set_iterate_all(HeapRegionClosure *cl)
{
  _collection_set.iterate(cl);
}

void G1CollectedHeap::collection_set_par_iterate_all(HeapRegionClosure *cl, HeapRegionClaimer *hr_claimer, uint worker_id)
{
  _collection_set.par_iterate(cl, hr_claimer, worker_id, workers()->active_workers());
}

void G1CollectedHeap::collection_set_iterate_increment_from(HeapRegionClosure *cl, HeapRegionClaimer *hr_claimer, uint worker_id)
{
  _collection_set.iterate_incremental_part_from(cl, hr_claimer, worker_id, workers()->active_workers());
}

HeapWord *G1CollectedHeap::block_start(const void *addr) const
{
  HeapRegion *hr = heap_region_containing(addr);
  return hr->block_start(addr);
}

bool G1CollectedHeap::block_is_obj(const HeapWord *addr) const
{
  HeapRegion *hr = heap_region_containing(addr);
  return hr->block_is_obj(addr);
}

size_t G1CollectedHeap::tlab_capacity(Thread *ignored) const
{
  return (_policy->young_list_target_length() - _survivor.length()) * HeapRegion::GrainBytes;
}

size_t G1CollectedHeap::tlab_used(Thread *ignored) const
{
  return _eden.length() * HeapRegion::GrainBytes;
}

// For G1 TLABs should not contain humongous objects, so the maximum TLAB size
// must be equal to the humongous object limit.
size_t G1CollectedHeap::max_tlab_size() const
{
  return align_down(_humongous_object_threshold_in_words, MinObjAlignment);
}

size_t G1CollectedHeap::unsafe_max_tlab_alloc(Thread *ignored) const
{
  return _allocator->unsafe_max_tlab_alloc();
}

size_t G1CollectedHeap::max_capacity() const
{
  return max_regions() * HeapRegion::GrainBytes;
}

void G1CollectedHeap::prepare_for_verify()
{
  _verifier->prepare_for_verify();
}

void G1CollectedHeap::verify(VerifyOption vo)
{
  _verifier->verify(vo);
}

bool G1CollectedHeap::supports_concurrent_gc_breakpoints() const
{
  return true;
}

bool G1CollectedHeap::is_archived_object(oop object) const
{
  return object != NULL && heap_region_containing(object)->is_archive();
}

class PrintRegionClosure : public HeapRegionClosure
{
  outputStream *_st;

public:
  PrintRegionClosure(outputStream *st) : _st(st) {}
  bool do_heap_region(HeapRegion *r)
  {
    r->print_on(_st);
    return false;
  }
};

bool G1CollectedHeap::is_obj_dead_cond(const oop obj,
                                       const HeapRegion *hr,
                                       const VerifyOption vo) const
{
  switch (vo)
  {
  case VerifyOption_G1UsePrevMarking:
    return is_obj_dead(obj, hr);
  case VerifyOption_G1UseNextMarking:
    return is_obj_ill(obj, hr);
  case VerifyOption_G1UseFullMarking:
    return is_obj_dead_full(obj, hr);
  default:
    ShouldNotReachHere();
  }
  return false; // keep some compilers happy
}

bool G1CollectedHeap::is_obj_dead_cond(const oop obj,
                                       const VerifyOption vo) const
{
  switch (vo)
  {
  case VerifyOption_G1UsePrevMarking:
    return is_obj_dead(obj);
  case VerifyOption_G1UseNextMarking:
    return is_obj_ill(obj);
  case VerifyOption_G1UseFullMarking:
    return is_obj_dead_full(obj);
  default:
    ShouldNotReachHere();
  }
  return false; // keep some compilers happy
}

void G1CollectedHeap::print_heap_regions() const
{
  LogTarget(Trace, gc, heap, region) lt;
  if (lt.is_enabled())
  {
    LogStream ls(lt);
    print_regions_on(&ls);
  }
}

void G1CollectedHeap::print_on(outputStream *st) const
{
  size_t heap_used = Heap_lock->owned_by_self() ? used() : used_unlocked();
  st->print(" %-20s", "garbage-first heap");
  st->print(" total " SIZE_FORMAT "K, used " SIZE_FORMAT "K",
            capacity() / K, heap_used / K);
  st->print(" [" PTR_FORMAT ", " PTR_FORMAT ")",
            p2i(_hrm.reserved().start()),
            p2i(_hrm.reserved().end()));
  st->cr();
  st->print("  region size " SIZE_FORMAT "K, ", HeapRegion::GrainBytes / K);
  uint young_regions = young_regions_count();
  st->print("%u young (" SIZE_FORMAT "K), ", young_regions,
            (size_t)young_regions * HeapRegion::GrainBytes / K);
  uint survivor_regions = survivor_regions_count();
  st->print("%u survivors (" SIZE_FORMAT "K)", survivor_regions,
            (size_t)survivor_regions * HeapRegion::GrainBytes / K);
  st->cr();
  if (_numa->is_enabled())
  {
    uint num_nodes = _numa->num_active_nodes();
    st->print("  remaining free region(s) on each NUMA node: ");
    const int *node_ids = _numa->node_ids();
    for (uint node_index = 0; node_index < num_nodes; node_index++)
    {
      uint num_free_regions = _hrm.num_free_regions(node_index);
      st->print("%d=%u ", node_ids[node_index], num_free_regions);
    }
    st->cr();
  }
  MetaspaceUtils::print_on(st);
}

void G1CollectedHeap::print_regions_on(outputStream *st) const
{
  st->print_cr("Heap Regions: E=young(eden), S=young(survivor), O=old, "
               "HS=humongous(starts), HC=humongous(continues), "
               "CS=collection set, F=free, "
               "OA=open archive, CA=closed archive, "
               "TAMS=top-at-mark-start (previous, next)");
  PrintRegionClosure blk(st);
  heap_region_iterate(&blk);
}

void G1CollectedHeap::print_extended_on(outputStream *st) const
{
  print_on(st);

  // Print the per-region information.
  st->cr();
  print_regions_on(st);
}

void G1CollectedHeap::print_on_error(outputStream *st) const
{
  this->CollectedHeap::print_on_error(st);

  if (_cm != NULL)
  {
    st->cr();
    _cm->print_on_error(st);
  }
}

void G1CollectedHeap::gc_threads_do(ThreadClosure *tc) const
{
  workers()->threads_do(tc);
  tc->do_thread(_cm_thread);
  _cm->threads_do(tc);
  _cr->threads_do(tc);
  tc->do_thread(_service_thread);
}

void G1CollectedHeap::print_tracing_info() const
{
  rem_set()->print_summary_info();
  concurrent_mark()->print_summary_info();
}

#ifndef PRODUCT
// Helpful for debugging RSet issues.

class PrintRSetsClosure : public HeapRegionClosure
{
private:
  const char *_msg;
  size_t _occupied_sum;

public:
  bool do_heap_region(HeapRegion *r)
  {
    HeapRegionRemSet *hrrs = r->rem_set();
    size_t occupied = hrrs->occupied();
    _occupied_sum += occupied;

    tty->print_cr("Printing RSet for region " HR_FORMAT, HR_FORMAT_PARAMS(r));
    if (occupied == 0)
    {
      tty->print_cr("  RSet is empty");
    }
    else
    {
      hrrs->print();
    }
    tty->print_cr("----------");
    return false;
  }

  PrintRSetsClosure(const char *msg) : _msg(msg), _occupied_sum(0)
  {
    tty->cr();
    tty->print_cr("========================================");
    tty->print_cr("%s", msg);
    tty->cr();
  }

  ~PrintRSetsClosure()
  {
    tty->print_cr("Occupied Sum: " SIZE_FORMAT, _occupied_sum);
    tty->print_cr("========================================");
    tty->cr();
  }
};

void G1CollectedHeap::print_cset_rsets()
{
  PrintRSetsClosure cl("Printing CSet RSets");
  collection_set_iterate_all(&cl);
}

void G1CollectedHeap::print_all_rsets()
{
  PrintRSetsClosure cl("Printing All RSets");
  ;
  heap_region_iterate(&cl);
}
#endif // PRODUCT

bool G1CollectedHeap::print_location(outputStream *st, void *addr) const
{
  return BlockLocationPrinter<G1CollectedHeap>::print_location(st, addr);
}

G1HeapSummary G1CollectedHeap::create_g1_heap_summary()
{

  size_t eden_used_bytes = _eden.used_bytes();
  size_t survivor_used_bytes = _survivor.used_bytes();
  size_t heap_used = Heap_lock->owned_by_self() ? used() : used_unlocked();

  size_t eden_capacity_bytes =
      (policy()->young_list_target_length() * HeapRegion::GrainBytes) - survivor_used_bytes;

  VirtualSpaceSummary heap_summary = create_heap_space_summary();
  return G1HeapSummary(heap_summary, heap_used, eden_used_bytes,
                       eden_capacity_bytes, survivor_used_bytes, num_regions());
}

G1EvacSummary G1CollectedHeap::create_g1_evac_summary(G1EvacStats *stats)
{
  return G1EvacSummary(stats->allocated(), stats->wasted(), stats->undo_wasted(),
                       stats->unused(), stats->used(), stats->region_end_waste(),
                       stats->regions_filled(), stats->num_plab_filled(),
                       stats->direct_allocated(), stats->num_direct_allocated(),
                       stats->failure_used(), stats->failure_waste());
}

void G1CollectedHeap::trace_heap(GCWhen::Type when, const GCTracer *gc_tracer)
{
  const G1HeapSummary &heap_summary = create_g1_heap_summary();
  gc_tracer->report_gc_heap_summary(when, heap_summary);

  const MetaspaceSummary &metaspace_summary = create_metaspace_summary();
  gc_tracer->report_metaspace_summary(when, metaspace_summary);
}

void G1CollectedHeap::gc_prologue(bool full)
{
  assert(InlineCacheBuffer::is_empty(), "should have cleaned up ICBuffer");

  // Update common counters.
  increment_total_collections(full /* full gc */);
  if (full || collector_state()->in_concurrent_start_gc())
  {
    increment_old_marking_cycles_started();
  }

  // Fill TLAB's and such
  {
    Ticks start = Ticks::now();
    ensure_parsability(true);
    Tickspan dt = Ticks::now() - start;
    phase_times()->record_prepare_tlab_time_ms(dt.seconds() * MILLIUNITS);
  }

  if (!full)
  {
    // Flush dirty card queues to qset, so later phases don't need to account
    // for partially filled per-thread queues and such.  Not needed for full
    // collections, which ignore those logs.
    Ticks start = Ticks::now();
    G1BarrierSet::dirty_card_queue_set().concatenate_logs();
    Tickspan dt = Ticks::now() - start;
    phase_times()->record_concatenate_dirty_card_logs_time_ms(dt.seconds() * MILLIUNITS);
  }
}

void G1CollectedHeap::gc_epilogue(bool full)
{
  // Update common counters.
  if (full)
  {
    // Update the number of full collections that have been completed.
    increment_old_marking_cycles_completed(false /* concurrent */, true /* liveness_completed */);
  }

#if COMPILER2_OR_JVMCI
  assert(DerivedPointerTable::is_empty(), "derived pointer present");
#endif

  double start = os::elapsedTime();
  resize_all_tlabs();
  phase_times()->record_resize_tlab_time_ms((os::elapsedTime() - start) * 1000.0);

  MemoryService::track_memory_usage();
  // We have just completed a GC. Update the soft reference
  // policy with the new heap occupancy
  Universe::heap()->update_capacity_and_used_at_gc();

  _collection_pause_end = Ticks::now();
}

uint G1CollectedHeap::uncommit_regions(uint region_limit)
{
  return _hrm.uncommit_inactive_regions(region_limit);
}

bool G1CollectedHeap::has_uncommittable_regions()
{
  return _hrm.has_inactive_regions();
}

void G1CollectedHeap::uncommit_regions_if_necessary()
{
  if (has_uncommittable_regions())
  {
    G1UncommitRegionTask::enqueue();
  }
}

void G1CollectedHeap::verify_numa_regions(const char *desc)
{
  LogTarget(Trace, gc, heap, verify) lt;

  if (lt.is_enabled())
  {
    LogStream ls(lt);
    // Iterate all heap regions to print matching between preferred numa id and actual numa id.
    G1NodeIndexCheckClosure cl(desc, _numa, &ls);
    heap_region_iterate(&cl);
  }
}

HeapWord *G1CollectedHeap::do_collection_pause(size_t word_size,
                                               uint gc_count_before,
                                               bool *succeeded,
                                               GCCause::Cause gc_cause)
{
  assert_heap_not_locked_and_not_at_safepoint();
  VM_G1CollectForAllocation op(word_size,
                               gc_count_before,
                               gc_cause,
                               policy()->max_pause_time_ms());
  VMThread::execute(&op);

  HeapWord *result = op.result();
  bool ret_succeeded = op.prologue_succeeded() && op.gc_succeeded();
  assert(result == NULL || ret_succeeded,
         "the result should be NULL if the VM did not succeed");
  *succeeded = ret_succeeded;

  assert_heap_not_locked();
  return result;
}

void G1CollectedHeap::start_concurrent_cycle(bool concurrent_operation_is_full_mark)
{
  assert(!_cm_thread->in_progress(), "Can not start concurrent operation while in progress");

  MutexLocker x(CGC_lock, Mutex::_no_safepoint_check_flag);
  if (concurrent_operation_is_full_mark)
  {
    _cm->post_concurrent_mark_start();
    _cm_thread->start_full_mark();
  }
  else
  {
    _cm->post_concurrent_undo_start();
    _cm_thread->start_undo_mark();
  }
  CGC_lock->notify();
}

bool G1CollectedHeap::is_potential_eager_reclaim_candidate(HeapRegion *r) const
{
  // We don't nominate objects with many remembered set entries, on
  // the assumption that such objects are likely still live.
  HeapRegionRemSet *rem_set = r->rem_set();

  return G1EagerReclaimHumongousObjectsWithStaleRefs ? rem_set->occupancy_less_or_equal_than(G1EagerReclaimRemSetThreshold) : G1EagerReclaimHumongousObjects && rem_set->is_empty();
}

#ifndef PRODUCT
void G1CollectedHeap::verify_region_attr_remset_update()
{
  class VerifyRegionAttrRemSet : public HeapRegionClosure
  {
  public:
    virtual bool do_heap_region(HeapRegion *r)
    {
      G1CollectedHeap *g1h = G1CollectedHeap::heap();
      bool const needs_remset_update = g1h->region_attr(r->bottom()).needs_remset_update();
      assert(r->rem_set()->is_tracked() == needs_remset_update,
             "Region %u remset tracking status (%s) different to region attribute (%s)",
             r->hrm_index(), BOOL_TO_STR(r->rem_set()->is_tracked()), BOOL_TO_STR(needs_remset_update));
      return false;
    }
  } cl;
  heap_region_iterate(&cl);
}
#endif

class VerifyRegionRemSetClosure : public HeapRegionClosure
{
public:
  bool do_heap_region(HeapRegion *hr)
  {
    if (!hr->is_archive() && !hr->is_continues_humongous())
    {
      hr->verify_rem_set();
    }
    return false;
  }
};

uint G1CollectedHeap::num_task_queues() const
{
  return _task_queues->size();
}

#if TASKQUEUE_STATS
void G1CollectedHeap::print_taskqueue_stats_hdr(outputStream *const st)
{
  st->print_raw_cr("GC Task Stats");
  st->print_raw("thr ");
  TaskQueueStats::print_header(1, st);
  st->cr();
  st->print_raw("--- ");
  TaskQueueStats::print_header(2, st);
  st->cr();
}

void G1CollectedHeap::print_taskqueue_stats() const
{
  if (!log_is_enabled(Trace, gc, task, stats))
  {
    return;
  }
  Log(gc, task, stats) log;
  ResourceMark rm;
  LogStream ls(log.trace());
  outputStream *st = &ls;

  print_taskqueue_stats_hdr(st);

  TaskQueueStats totals;
  const uint n = num_task_queues();
  for (uint i = 0; i < n; ++i)
  {
    st->print("%3u ", i);
    task_queue(i)->stats.print(st);
    st->cr();
    totals += task_queue(i)->stats;
  }
  st->print_raw("tot ");
  totals.print(st);
  st->cr();

  DEBUG_ONLY(totals.verify());
}

void G1CollectedHeap::reset_taskqueue_stats()
{
  const uint n = num_task_queues();
  for (uint i = 0; i < n; ++i)
  {
    task_queue(i)->stats.reset();
  }
}
#endif // TASKQUEUE_STATS

void G1CollectedHeap::wait_for_root_region_scanning()
{
  double scan_wait_start = os::elapsedTime();
  // We have to wait until the CM threads finish scanning the
  // root regions as it's the only way to ensure that all the
  // objects on them have been correctly scanned before we start
  // moving them during the GC.
  bool waited = _cm->root_regions()->wait_until_scan_finished();
  double wait_time_ms = 0.0;
  if (waited)
  {
    double scan_wait_end = os::elapsedTime();
    wait_time_ms = (scan_wait_end - scan_wait_start) * 1000.0;
  }
  phase_times()->record_root_region_scan_wait_time(wait_time_ms);
}

class G1PrintCollectionSetClosure : public HeapRegionClosure
{
private:
  G1HRPrinter *_hr_printer;

public:
  G1PrintCollectionSetClosure(G1HRPrinter *hr_printer) : HeapRegionClosure(), _hr_printer(hr_printer) {}

  virtual bool do_heap_region(HeapRegion *r)
  {
    _hr_printer->cset(r);
    return false;
  }
};

void G1CollectedHeap::start_new_collection_set()
{
  double start = os::elapsedTime();

  collection_set()->start_incremental_building();

  clear_region_attr();

  guarantee(_eden.length() == 0, "eden should have been cleared");
  policy()->transfer_survivors_to_cset(survivor());

  // We redo the verification but now wrt to the new CSet which
  // has just got initialized after the previous CSet was freed.
  _cm->verify_no_collection_set_oops();

  phase_times()->record_start_new_cset_time_ms((os::elapsedTime() - start) * 1000.0);
}

void G1CollectedHeap::calculate_collection_set(G1EvacuationInfo *evacuation_info, double target_pause_time_ms)
{

  _collection_set.finalize_initial_collection_set(target_pause_time_ms, &_survivor);
  evacuation_info->set_collectionset_regions(collection_set()->region_length() +
                                             collection_set()->optional_region_length());

  _cm->verify_no_collection_set_oops();

  if (_hr_printer.is_active())
  {
    G1PrintCollectionSetClosure cl(&_hr_printer);
    _collection_set.iterate(&cl);
    _collection_set.iterate_optional(&cl);
  }
}

G1HeapVerifier::G1VerifyType G1CollectedHeap::young_collection_verify_type() const
{
  if (collector_state()->in_concurrent_start_gc())
  {
    return G1HeapVerifier::G1VerifyConcurrentStart;
  }
  else if (collector_state()->in_young_only_phase())
  {
    return G1HeapVerifier::G1VerifyYoungNormal;
  }
  else
  {
    return G1HeapVerifier::G1VerifyMixed;
  }
}

void G1CollectedHeap::verify_before_young_collection(G1HeapVerifier::G1VerifyType type)
{
  if (VerifyRememberedSets)
  {
    log_info(gc, verify)("[Verifying RemSets before GC]");
    VerifyRegionRemSetClosure v_cl;
    heap_region_iterate(&v_cl);
  }
  _verifier->verify_before_gc(type);
  _verifier->check_bitmaps("GC Start");
  verify_numa_regions("GC Start");
}

void G1CollectedHeap::verify_after_young_collection(G1HeapVerifier::G1VerifyType type)
{
  if (VerifyRememberedSets)
  {
    log_info(gc, verify)("[Verifying RemSets after GC]");
    VerifyRegionRemSetClosure v_cl;
    heap_region_iterate(&v_cl);
  }
  _verifier->verify_after_gc(type);
  _verifier->check_bitmaps("GC End");
  verify_numa_regions("GC End");
}

void G1CollectedHeap::expand_heap_after_young_collection()
{
  size_t expand_bytes = _heap_sizing_policy->young_collection_expansion_amount();
  if (expand_bytes > 0)
  {
    // No need for an ergo logging here,
    // expansion_amount() does this when it returns a value > 0.
    double expand_ms = 0.0;
    if (!expand(expand_bytes, _workers, &expand_ms))
    {
      // We failed to expand the heap. Cannot do anything about it.
    }
    phase_times()->record_expand_heap_time(expand_ms);
  }
}

void G1CollectedHeap::set_young_gc_name(char *young_gc_name)
{
  G1GCPauseType pause_type =
      // The strings for all Concurrent Start pauses are the same, so the parameter
      // does not matter here.
      collector_state()->young_gc_pause_type(false /* concurrent_operation_is_full_mark */);
  snprintf(young_gc_name,
           MaxYoungGCNameLength,
           "Pause Young (%s)",
           G1GCPauseTypeHelper::to_string(pause_type));
}

bool G1CollectedHeap::do_collection_pause_at_safepoint(double target_pause_time_ms)
{
  assert_at_safepoint_on_vm_thread();
  guarantee(!is_gc_active(), "collection is not reentrant");

  if (GCLocker::check_active_before_gc())
  {
    return false;
  }

  do_collection_pause_at_safepoint_helper(target_pause_time_ms);
  return true;
}

void G1CollectedHeap::gc_tracer_report_gc_start()
{
  _gc_timer_stw->register_gc_start();
  _gc_tracer_stw->report_gc_start(gc_cause(), _gc_timer_stw->gc_start());
}

void G1CollectedHeap::gc_tracer_report_gc_end(bool concurrent_operation_is_full_mark,
                                              G1EvacuationInfo &evacuation_info)
{
  _gc_tracer_stw->report_evacuation_info(&evacuation_info);
  _gc_tracer_stw->report_tenuring_threshold(_policy->tenuring_threshold());

  _gc_timer_stw->register_gc_end();
  _gc_tracer_stw->report_gc_end(_gc_timer_stw->gc_end(),
                                _gc_timer_stw->time_partitions());
}

G1HeapPrinterMark::G1HeapPrinterMark(G1CollectedHeap *g1h) : _g1h(g1h), _heap_transition(g1h)
{
  // This summary needs to be printed before incrementing total collections.
  _g1h->rem_set()->print_periodic_summary_info("Before GC RS summary", _g1h->total_collections());
  _g1h->print_heap_before_gc();
  _g1h->print_heap_regions();
}

G1HeapPrinterMark::~G1HeapPrinterMark()
{
  _g1h->policy()->print_age_table();
  // not (yet) in 17u: _g1h->rem_set()->print_coarsen_stats();
  // We are at the end of the GC. Total collections has already been increased.
  _g1h->rem_set()->print_periodic_summary_info("After GC RS summary", _g1h->total_collections() - 1);

  _heap_transition.print();
  _g1h->print_heap_regions();
  _g1h->print_heap_after_gc();
  // Print NUMA statistics.
  _g1h->numa()->print_statistics();
}

G1JFRTracerMark::G1JFRTracerMark(STWGCTimer *timer, GCTracer *tracer) : _timer(timer), _tracer(tracer)
{

  _timer->register_gc_start();
  _tracer->report_gc_start(G1CollectedHeap::heap()->gc_cause(), _timer->gc_start());
  G1CollectedHeap::heap()->trace_heap_before_gc(_tracer);
}

G1JFRTracerMark::~G1JFRTracerMark()
{
  G1CollectedHeap::heap()->trace_heap_after_gc(_tracer);
  _timer->register_gc_end();
  _tracer->report_gc_end(_timer->gc_end(), _timer->time_partitions());
}

class G1YoungGCJFRTracerMark : public G1JFRTracerMark
{
  G1EvacuationInfo _evacuation_info;

  G1NewTracer *tracer() const { return (G1NewTracer *)_tracer; }

public:
  G1EvacuationInfo *evacuation_info() { return &_evacuation_info; }

  G1YoungGCJFRTracerMark(STWGCTimer *gc_timer_stw, G1NewTracer *gc_tracer_stw, GCCause::Cause cause) : G1JFRTracerMark(gc_timer_stw, gc_tracer_stw), _evacuation_info() {}

  void report_pause_type(G1GCPauseType type)
  {
    tracer()->report_young_gc_pause(type);
  }

  ~G1YoungGCJFRTracerMark()
  {
    G1CollectedHeap *g1h = G1CollectedHeap::heap();

    tracer()->report_evacuation_info(&_evacuation_info);
    tracer()->report_tenuring_threshold(g1h->policy()->tenuring_threshold());
  }
};

void G1CollectedHeap::do_collection_pause_at_safepoint_helper(double target_pause_time_ms)
{
  GCIdMark gc_id_mark;

  SvcGCMarker sgcm(SvcGCMarker::MINOR);
  ResourceMark rm;

  policy()->note_gc_start();

  wait_for_root_region_scanning();

  _verifier->verify_region_sets_optional();
  _verifier->verify_dirty_young_regions();

  // We should not be doing concurrent start unless the concurrent mark thread is running
  if (!_cm_thread->should_terminate())
  {
    // This call will decide whether this pause is a concurrent start
    // pause. If it is, in_concurrent_start_gc() will return true
    // for the duration of this pause.
    policy()->decide_on_conc_mark_initiation();
  }

  // We do not allow concurrent start to be piggy-backed on a mixed GC.
  assert(!collector_state()->in_concurrent_start_gc() ||
             collector_state()->in_young_only_phase(),
         "sanity");
  // We also do not allow mixed GCs during marking.
  assert(!collector_state()->mark_or_rebuild_in_progress() || collector_state()->in_young_only_phase(), "sanity");

  // Record whether this pause may need to trigger a concurrent operation. Later,
  // when we signal the G1ConcurrentMarkThread, the collector state has already
  // been reset for the next pause.
  bool should_start_concurrent_mark_operation = collector_state()->in_concurrent_start_gc();
  bool concurrent_operation_is_full_mark = false;

  // Inner scope for scope based logging, timers, and stats collection
  {
    GCTraceCPUTime tcpu(_gc_tracer_stw);

    char young_gc_name[MaxYoungGCNameLength];
    set_young_gc_name(young_gc_name);

    GCTraceTime(Info, gc) tm(young_gc_name, NULL, gc_cause(), true);

    uint active_workers = WorkerPolicy::calc_active_workers(workers()->total_workers(),
                                                            workers()->active_workers(),
                                                            Threads::number_of_non_daemon_threads());
    active_workers = workers()->update_active_workers(active_workers);
    log_info(gc, task)("Using %u workers of %u for evacuation", active_workers, workers()->total_workers());

    // JFR
    G1YoungGCJFRTracerMark jtm(_gc_timer_stw, _gc_tracer_stw, gc_cause());
    G1MonitoringScope ms(g1mm(),
                         false /* full_gc */,
                         collector_state()->in_mixed_phase() /* all_memory_pools_affected */);
    // Create the heap printer before internal pause timing to have
    // heap information printed as last part of detailed GC log.
    G1HeapPrinterMark hpm(this);
    // Young GC internal pause timing
    // Not (yet) in 17: G1YoungGCNotifyPauseMark npm;

    // Verification may use the gang workers, so they must be set up before.
    // Individual parallel phases may override this.
    // Not (yet) in 17: set_young_collection_default_active_worker_threads();

    {
      IsGCActiveMark x;

      gc_prologue(false);

      G1HeapVerifier::G1VerifyType verify_type = young_collection_verify_type();
      verify_before_young_collection(verify_type);

      {
        // The elapsed time induced by the start time below deliberately elides
        // the possible verification above.
        double sample_start_time_sec = os::elapsedTime();

        // Please see comment in g1CollectedHeap.hpp and
        // G1CollectedHeap::ref_processing_init() to see how
        // reference processing currently works in G1.
        _ref_processor_stw->enable_discovery();

        // We want to temporarily turn off discovery by the
        // CM ref processor, if necessary, and turn it back on
        // on again later if we do. Using a scoped
        // NoRefDiscovery object will do this.
        NoRefDiscovery no_cm_discovery(_ref_processor_cm);

        policy()->record_collection_pause_start(sample_start_time_sec);

        // Forget the current allocation region (we might even choose it to be part
        // of the collection set!).
        _allocator->release_mutator_alloc_regions();

        calculate_collection_set(jtm.evacuation_info(), target_pause_time_ms);

        G1RedirtyCardsQueueSet rdcqs(G1BarrierSet::dirty_card_queue_set().allocator());
        G1ParScanThreadStateSet per_thread_states(this,
                                                  &rdcqs,
                                                  workers()->active_workers(),
                                                  collection_set()->young_region_length(),
                                                  collection_set()->optional_region_length());
        pre_evacuate_collection_set(jtm.evacuation_info(), &per_thread_states);

        bool may_do_optional_evacuation = _collection_set.optional_region_length() != 0;
        // Actually do the work...
        evacuate_initial_collection_set(&per_thread_states, may_do_optional_evacuation);

        if (may_do_optional_evacuation)
        {
          evacuate_optional_collection_set(&per_thread_states);
        }
        post_evacuate_collection_set(jtm.evacuation_info(), &rdcqs, &per_thread_states);

        start_new_collection_set();

        _survivor_evac_stats.adjust_desired_plab_sz();
        _old_evac_stats.adjust_desired_plab_sz();

        allocate_dummy_regions();

        _allocator->init_mutator_alloc_regions();

        expand_heap_after_young_collection();

        // Refine the type of a concurrent mark operation now that we did the
        // evacuation, eventually aborting it.
        concurrent_operation_is_full_mark = policy()->concurrent_operation_is_full_mark("Revise IHOP");

        // Need to report the collection pause now since record_collection_pause_end()
        // modifies it to the next state.
        jtm.report_pause_type(collector_state()->young_gc_pause_type(concurrent_operation_is_full_mark));

        double sample_end_time_sec = os::elapsedTime();
        double pause_time_ms = (sample_end_time_sec - sample_start_time_sec) * MILLIUNITS;
        policy()->record_collection_pause_end(pause_time_ms, concurrent_operation_is_full_mark);
      }

      verify_after_young_collection(verify_type);

      gc_epilogue(false);
    }

    // Print the remainder of the GC log output.
    if (evacuation_failed())
    {
      log_info(gc)("To-space exhausted");
    }

    policy()->print_phases();

    _hrm.verify_optional();
    _verifier->verify_region_sets_optional();

    TASKQUEUE_STATS_ONLY(print_taskqueue_stats());
    TASKQUEUE_STATS_ONLY(reset_taskqueue_stats());

    // We must call G1MonitoringSupport::update_sizes() in the same scoping level
    // as an active TraceMemoryManagerStats object (i.e. before the destructor for the
    // TraceMemoryManagerStats is called) so that the G1 memory pools are updated
    // before any GC notifications are raised.
    g1mm()->update_sizes();
  }
  // It should now be safe to tell the concurrent mark thread to start
  // without its logging output interfering with the logging output
  // that came from the pause.

  if (should_start_concurrent_mark_operation)
  {
    // CAUTION: after the start_concurrent_cycle() call below, the concurrent marking
    // thread(s) could be running concurrently with us. Make sure that anything
    // after this point does not assume that we are the only GC thread running.
    // Note: of course, the actual marking work will not start until the safepoint
    // itself is released in SuspendibleThreadSet::desynchronize().
    start_concurrent_cycle(concurrent_operation_is_full_mark);
    ConcurrentGCBreakpoints::notify_idle_to_active();
  }
}

void G1CollectedHeap::preserve_mark_during_evac_failure(uint worker_id, oop obj, markWord m)
{
  _evacuation_failed_info_array[worker_id].register_copy_failure(obj->size());
  _preserved_marks_set.get(worker_id)->push_if_necessary(obj, m);
}

bool G1ParEvacuateFollowersClosure::offer_termination()
{
  EventGCPhaseParallel event;
  G1ParScanThreadState *const pss = par_scan_state();
  start_term_time();
  const bool res = (terminator() == nullptr) ? true : terminator()->offer_termination();
  end_term_time();
  event.commit(GCId::current(), pss->worker_id(), G1GCPhaseTimes::phase_name(G1GCPhaseTimes::Termination));
  return res;
}

void G1ParEvacuateFollowersClosure::do_void()
{
  EventGCPhaseParallel event;
  G1ParScanThreadState *const pss = par_scan_state();
  pss->trim_queue();
  event.commit(GCId::current(), pss->worker_id(), G1GCPhaseTimes::phase_name(_phase));
  do
  {
    EventGCPhaseParallel event;
    event.commit(GCId::current(), pss->worker_id(), G1GCPhaseTimes::phase_name(_phase));
  } while (!offer_termination());
}

void G1CollectedHeap::complete_cleaning(BoolObjectClosure *is_alive,
                                        bool class_unloading_occurred)
{
  uint num_workers = workers()->active_workers();
  G1ParallelCleaningTask unlink_task(is_alive, num_workers, class_unloading_occurred);
  workers()->run_task(&unlink_task);
}

// Weak Reference Processing support

bool G1STWIsAliveClosure::do_object_b(oop p)
{
  // An object is reachable if it is outside the collection set,
  // or is inside and copied.
  return !_g1h->is_in_cset(p) || p->is_forwarded();
}

bool G1STWSubjectToDiscoveryClosure::do_object_b(oop obj)
{
  assert(obj != NULL, "must not be NULL");
  assert(_g1h->is_in_reserved(obj), "Trying to discover obj " PTR_FORMAT " not in heap", p2i(obj));
  // The areas the CM and STW ref processor manage must be disjoint. The is_in_cset() below
  // may falsely indicate that this is not the case here: however the collection set only
  // contains old regions when concurrent mark is not running.
  return _g1h->is_in_cset(obj) || _g1h->heap_region_containing(obj)->is_survivor();
}

// Non Copying Keep Alive closure
class G1KeepAliveClosure : public OopClosure
{
  G1CollectedHeap *_g1h;

public:
  G1KeepAliveClosure(G1CollectedHeap *g1h) : _g1h(g1h) {}
  void do_oop(narrowOop *p) { guarantee(false, "Not needed"); }
  void do_oop(oop *p)
  {
    oop obj = *p;
    assert(obj != NULL, "the caller should have filtered out NULL values");

    const G1HeapRegionAttr region_attr = _g1h->region_attr(obj);
    if (!region_attr.is_in_cset_or_humongous())
    {
      return;
    }
    if (region_attr.is_in_cset())
    {
      assert(obj->is_forwarded(), "invariant");
      *p = obj->forwardee();
    }
    else
    {
      assert(!obj->is_forwarded(), "invariant");
      assert(region_attr.is_humongous(),
             "Only allowed G1HeapRegionAttr state is IsHumongous, but is %d", region_attr.type());
      _g1h->set_humongous_is_live(obj);
    }
  }
};

// Copying Keep Alive closure - can be called from both
// serial and parallel code as long as different worker
// threads utilize different G1ParScanThreadState instances
// and different queues.

class G1CopyingKeepAliveClosure : public OopClosure
{
  G1CollectedHeap *_g1h;
  G1ParScanThreadState *_par_scan_state;

public:
  G1CopyingKeepAliveClosure(G1CollectedHeap *g1h,
                            G1ParScanThreadState *pss) : _g1h(g1h),
                                                         _par_scan_state(pss)
  {
  }

  virtual void do_oop(narrowOop *p) { do_oop_work(p); }
  virtual void do_oop(oop *p) { do_oop_work(p); }

  template <class T>
  void do_oop_work(T *p)
  {
    oop obj = RawAccess<>::oop_load(p);

    if (_g1h->is_in_cset_or_humongous(obj))
    {
      // If the referent object has been forwarded (either copied
      // to a new location or to itself in the event of an
      // evacuation failure) then we need to update the reference
      // field and, if both reference and referent are in the G1
      // heap, update the RSet for the referent.
      //
      // If the referent has not been forwarded then we have to keep
      // it alive by policy. Therefore we have copy the referent.
      //
      // When the queue is drained (after each phase of reference processing)
      // the object and it's followers will be copied, the reference field set
      // to point to the new location, and the RSet updated.
      _par_scan_state->push_on_queue(ScannerTask(p));
    }
  }
};

// Special closure for enqueuing discovered fields: during enqueue the card table
// may not be in shape to properly handle normal barrier calls (e.g. card marks
// in regions that failed evacuation, scribbling of various values by card table
// scan code). Additionally the regular barrier enqueues into the "global"
// DCQS, but during GC we need these to-be-refined entries in the GC local queue
// so that after clearing the card table, the redirty cards phase will properly
// mark all dirty cards to be picked up by refinement.
class G1EnqueueDiscoveredFieldClosure : public EnqueueDiscoveredFieldClosure
{
  G1CollectedHeap *_g1h;
  G1ParScanThreadState *_pss;

public:
  G1EnqueueDiscoveredFieldClosure(G1CollectedHeap *g1h, G1ParScanThreadState *pss) : _g1h(g1h), _pss(pss) {}

  virtual void enqueue(HeapWord *discovered_field_addr, oop value)
  {
    assert(_g1h->is_in(discovered_field_addr), PTR_FORMAT " is not in heap ", p2i(discovered_field_addr));
    // Store the value first, whatever it is.
    RawAccess<>::oop_store(discovered_field_addr, value);
    if (value == NULL)
    {
      return;
    }
    _pss->write_ref_field_post(discovered_field_addr, value);
  }
};

// Serial drain queue closure. Called as the 'complete_gc'
// closure for each discovered list in some of the
// reference processing phases.

class G1STWDrainQueueClosure : public VoidClosure
{
protected:
  G1CollectedHeap *_g1h;
  G1ParScanThreadState *_par_scan_state;

  G1ParScanThreadState *par_scan_state() { return _par_scan_state; }

public:
  G1STWDrainQueueClosure(G1CollectedHeap *g1h, G1ParScanThreadState *pss) : _g1h(g1h),
                                                                            _par_scan_state(pss)
  {
  }

  void do_void()
  {
    G1ParScanThreadState *const pss = par_scan_state();
    pss->trim_queue();
  }
};

class G1STWRefProcProxyTask : public RefProcProxyTask
{
  G1CollectedHeap &_g1h;
  G1ParScanThreadStateSet &_pss;
  TaskTerminator _terminator;
  G1ScannerTasksQueueSet &_task_queues;

public:
  G1STWRefProcProxyTask(uint max_workers, G1CollectedHeap &g1h, G1ParScanThreadStateSet &pss, G1ScannerTasksQueueSet &task_queues)
      : RefProcProxyTask("G1STWRefProcProxyTask", max_workers),
        _g1h(g1h),
        _pss(pss),
        _terminator(max_workers, &task_queues),
        _task_queues(task_queues) {}

  void work(uint worker_id) override
  {
    assert(worker_id < _max_workers, "sanity");
    uint index = (_tm == RefProcThreadModel::Single) ? 0 : worker_id;
    _pss.state_for_worker(index)->set_ref_discoverer(nullptr);
    G1STWIsAliveClosure is_alive(&_g1h);
    G1CopyingKeepAliveClosure keep_alive(&_g1h, _pss.state_for_worker(index));
    G1ParEvacuateFollowersClosure complete_gc(&_g1h, _pss.state_for_worker(index), &_task_queues, _tm == RefProcThreadModel::Single ? nullptr : &_terminator, G1GCPhaseTimes::ObjCopy);
    G1EnqueueDiscoveredFieldClosure enqueue(&_g1h, _pss.state_for_worker(index));
    _rp_task->rp_work(worker_id, &is_alive, &keep_alive, &enqueue, &complete_gc);
  }

  void prepare_run_task_hook() override
  {
    _terminator.reset_for_reuse(_queue_count);
  }
};

// End of weak reference support closures

void G1CollectedHeap::process_discovered_references(G1ParScanThreadStateSet *per_thread_states)
{
  double ref_proc_start = os::elapsedTime();

  ReferenceProcessor *rp = _ref_processor_stw;
  assert(rp->discovery_enabled(), "should have been enabled");

  // Use only a single queue for this PSS.
  G1ParScanThreadState *pss = per_thread_states->state_for_worker(0);
  pss->set_ref_discoverer(NULL);
  assert(pss->queue_is_empty(), "pre-condition");

  // Setup the soft refs policy...
  rp->setup_policy(false);

  ReferenceProcessorPhaseTimes &pt = *phase_times()->ref_phase_times();

  ReferenceProcessorStats stats;
  uint no_of_gc_workers = workers()->active_workers();

  // Parallel reference processing
  assert(no_of_gc_workers <= rp->max_num_queues(),
         "Mismatch between the number of GC workers %u and the maximum number of Reference process queues %u",
         no_of_gc_workers, rp->max_num_queues());

  rp->set_active_mt_degree(no_of_gc_workers);
  G1STWRefProcProxyTask task(rp->max_num_queues(), *this, *per_thread_states, *_task_queues);
  stats = rp->process_discovered_references(task, pt);

  _gc_tracer_stw->report_gc_reference_stats(stats);

  // We have completed copying any necessary live referent objects.
  assert(pss->queue_is_empty(), "both queue and overflow should be empty");

  make_pending_list_reachable();

  assert(!rp->discovery_enabled(), "Postcondition");
  rp->verify_no_references_recorded();

  double ref_proc_time = os::elapsedTime() - ref_proc_start;
  phase_times()->record_ref_proc_time(ref_proc_time * 1000.0);
}

void G1CollectedHeap::make_pending_list_reachable()
{
  if (collector_state()->in_concurrent_start_gc())
  {
    oop pll_head = Universe::reference_pending_list();
    if (pll_head != NULL)
    {
      // Any valid worker id is fine here as we are in the VM thread and single-threaded.
      _cm->mark_in_next_bitmap(0 /* worker_id */, pll_head);
    }
  }
}

static bool do_humongous_object_logging()
{
  return log_is_enabled(Debug, gc, humongous);
}

bool G1CollectedHeap::should_do_eager_reclaim() const
{
  // As eager reclaim logging also gives information about humongous objects in
  // the heap in general, always do the eager reclaim pass even without known
  // candidates.
  return (G1EagerReclaimHumongousObjects &&
          (has_humongous_reclaim_candidates() || do_humongous_object_logging()));
}

class G1PrepareEvacuationTask : public AbstractGangTask
{
  class G1PrepareRegionsClosure : public HeapRegionClosure
  {
    G1CollectedHeap *_g1h;
    G1PrepareEvacuationTask *_parent_task;
    uint _worker_humongous_total;
    uint _worker_humongous_candidates;

    bool humongous_region_is_candidate(HeapRegion *region) const
    {
      assert(region->is_starts_humongous(), "Must start a humongous object");

      oop obj = cast_to_oop(region->bottom());

      // Dead objects cannot be eager reclaim candidates. Due to class
      // unloading it is unsafe to query their classes so we return early.
      if (_g1h->is_obj_dead(obj, region))
      {
        return false;
      }

      // If we do not have a complete remembered set for the region, then we can
      // not be sure that we have all references to it.
      if (!region->rem_set()->is_complete())
      {
        return false;
      }
      // Candidate selection must satisfy the following constraints
      // while concurrent marking is in progress:
      //
      // * In order to maintain SATB invariants, an object must not be
      // reclaimed if it was allocated before the start of marking and
      // has not had its references scanned.  Such an object must have
      // its references (including type metadata) scanned to ensure no
      // live objects are missed by the marking process.  Objects
      // allocated after the start of concurrent marking don't need to
      // be scanned.
      //
      // * An object must not be reclaimed if it is on the concurrent
      // mark stack.  Objects allocated after the start of concurrent
      // marking are never pushed on the mark stack.
      //
      // Nominating only objects allocated after the start of concurrent
      // marking is sufficient to meet both constraints.  This may miss
      // some objects that satisfy the constraints, but the marking data
      // structures don't support efficiently performing the needed
      // additional tests or scrubbing of the mark stack.
      //
      // However, we presently only nominate is_typeArray() objects.
      // A humongous object containing references induces remembered
      // set entries on other regions.  In order to reclaim such an
      // object, those remembered sets would need to be cleaned up.
      //
      // We also treat is_typeArray() objects specially, allowing them
      // to be reclaimed even if allocated before the start of
      // concurrent mark.  For this we rely on mark stack insertion to
      // exclude is_typeArray() objects, preventing reclaiming an object
      // that is in the mark stack.  We also rely on the metadata for
      // such objects to be built-in and so ensured to be kept live.
      // Frequent allocation and drop of large binary blobs is an
      // important use case for eager reclaim, and this special handling
      // may reduce needed headroom.

      return obj->is_typeArray() &&
             _g1h->is_potential_eager_reclaim_candidate(region);
    }

  public:
    G1PrepareRegionsClosure(G1CollectedHeap *g1h, G1PrepareEvacuationTask *parent_task) : _g1h(g1h),
                                                                                          _parent_task(parent_task),
                                                                                          _worker_humongous_total(0),
                                                                                          _worker_humongous_candidates(0) {}

    ~G1PrepareRegionsClosure()
    {
      _parent_task->add_humongous_candidates(_worker_humongous_candidates);
      _parent_task->add_humongous_total(_worker_humongous_total);
    }

    virtual bool do_heap_region(HeapRegion *hr)
    {
      // First prepare the region for scanning
      _g1h->rem_set()->prepare_region_for_scan(hr);

      // Now check if region is a humongous candidate
      if (!hr->is_starts_humongous())
      {
        _g1h->register_region_with_region_attr(hr);
        return false;
      }

      uint index = hr->hrm_index();
      if (humongous_region_is_candidate(hr))
      {
        _g1h->set_humongous_reclaim_candidate(index, true);
        _g1h->register_humongous_region_with_region_attr(index);
        _worker_humongous_candidates++;
        // We will later handle the remembered sets of these regions.
      }
      else
      {
        _g1h->set_humongous_reclaim_candidate(index, false);
        _g1h->register_region_with_region_attr(hr);
      }
      log_debug(gc, humongous)("Humongous region %u (object size " SIZE_FORMAT " @ " PTR_FORMAT ") remset " SIZE_FORMAT " code roots " SIZE_FORMAT " marked %d reclaim candidate %d type array %d",
                               index,
                               (size_t)cast_to_oop(hr->bottom())->size() * HeapWordSize,
                               p2i(hr->bottom()),
                               hr->rem_set()->occupied(),
                               hr->rem_set()->strong_code_roots_list_length(),
                               _g1h->concurrent_mark()->next_mark_bitmap()->is_marked(hr->bottom()),
                               _g1h->is_humongous_reclaim_candidate(index),
                               cast_to_oop(hr->bottom())->is_typeArray());
      _worker_humongous_total++;

      return false;
    }
  };

  G1CollectedHeap *_g1h;
  HeapRegionClaimer _claimer;
  volatile uint _humongous_total;
  volatile uint _humongous_candidates;

public:
  G1PrepareEvacuationTask(G1CollectedHeap *g1h) : AbstractGangTask("Prepare Evacuation"),
                                                  _g1h(g1h),
                                                  _claimer(_g1h->workers()->active_workers()),
                                                  _humongous_total(0),
                                                  _humongous_candidates(0) {}

  void work(uint worker_id)
  {
    G1PrepareRegionsClosure cl(_g1h, this);
    _g1h->heap_region_par_iterate_from_worker_offset(&cl, &_claimer, worker_id);
  }

  void add_humongous_candidates(uint candidates)
  {
    Atomic::add(&_humongous_candidates, candidates);
  }

  void add_humongous_total(uint total)
  {
    Atomic::add(&_humongous_total, total);
  }

  uint humongous_candidates()
  {
    return _humongous_candidates;
  }

  uint humongous_total()
  {
    return _humongous_total;
  }
};

void G1CollectedHeap::pre_evacuate_collection_set(G1EvacuationInfo *evacuation_info, G1ParScanThreadStateSet *per_thread_states)
{
  _bytes_used_during_gc = 0;

  _expand_heap_after_alloc_failure = true;
  Atomic::store(&_num_regions_failed_evacuation, 0u);

  memset((void *)_regions_failed_evacuation, false, sizeof(bool) * max_regions());

  // Disable the hot card cache.
  _hot_card_cache->reset_hot_cache_claimed_index();
  _hot_card_cache->set_use_cache(false);

  // Initialize the GC alloc regions.
  _allocator->init_gc_alloc_regions(evacuation_info);

  {
    Ticks start = Ticks::now();
    rem_set()->prepare_for_scan_heap_roots();
    phase_times()->record_prepare_heap_roots_time_ms((Ticks::now() - start).seconds() * 1000.0);
  }

  {
    G1PrepareEvacuationTask g1_prep_task(this);
    Tickspan task_time = run_task_timed(&g1_prep_task);

    phase_times()->record_register_regions(task_time.seconds() * 1000.0);
    _num_humongous_objects = g1_prep_task.humongous_total();
    _num_humongous_reclaim_candidates = g1_prep_task.humongous_candidates();
  }

  assert(_verifier->check_region_attr_table(), "Inconsistency in the region attributes table.");
  _preserved_marks_set.assert_empty();

#if COMPILER2_OR_JVMCI
  DerivedPointerTable::clear();
#endif

  // Concurrent start needs claim bits to keep track of the marked-through CLDs.
  if (collector_state()->in_concurrent_start_gc())
  {
    concurrent_mark()->pre_concurrent_start(gc_cause());

    double start_clear_claimed_marks = os::elapsedTime();

    ClassLoaderDataGraph::clear_claimed_marks();

    double recorded_clear_claimed_marks_time_ms = (os::elapsedTime() - start_clear_claimed_marks) * 1000.0;
    phase_times()->record_clear_claimed_marks_time_ms(recorded_clear_claimed_marks_time_ms);
  }

  // Should G1EvacuationFailureALot be in effect for this GC?
  NOT_PRODUCT(set_evacuation_failure_alot_for_current_gc();)
}

class G1EvacuateRegionsBaseTask : public AbstractGangTask
{
protected:
  G1CollectedHeap *_g1h;
  G1ParScanThreadStateSet *_per_thread_states;
  G1ScannerTasksQueueSet *_task_queues;
  TaskTerminator _terminator;
  uint _num_workers;

  uint *do_oop_region_cache;

  uint *obj_shift_cache;
  int8_t *attr_type_cache;

  bool *byte_about_valid;
  uintptr_t *byte_map_cache;
  uintptr_t *byte_map_base_cache;
  bool *last_index_valid;
  uintptr_t *last_index_cache;
  bool *parScan_offset40_valid;
  bool *parScan_offset20_valid;
  uintptr_t *index_cache;
  uintptr_t *buffer_cache;
  uintptr_t *node_allocator_ptr_cache;
  uintptr_t *offset30_cache;
  uintptr_t *offset38_cache;

  uint list_length;
  uintptr_t list_head_ptr;
  uintptr_t list_end_ptr;
  uintptr_t list_last_ptr;

  bool expand_failure_valid;
  bool expand_failure_cache;

  bool region_attr_base_valid;
  uintptr_t region_attr_base_cache;

  bool grow_array_ptr_cache_valid;
  uintptr_t grow_array_ptr_cache;

  bool during_im_valid;
  bool during_im_cache;
  uintptr_t cm_cache;

  bool **region_ptr_valid;
  uintptr_t **region_ptr_cache;

  bool **alloc_region_valid;
  uintptr_t **alloc_region_cache;

  bool **plab_stats_valid;
  uintptr_t **plab_stats_cache;

  bool *dest_attr_valid;
  uint *dest_attr_cache;

  uint *heap_oop_shift_cache;
  bool *heap_type_is_young;

  bool **plab_buffer_valid;
  uintptr_t **plab_buffer_ptr_cache;
  bool **plab_top_end_valid;
  uintptr_t **plab_top_cache;
  uintptr_t **plab_end_cache;

  uintptr_t *src_region_ptr_cache;
  uint16_t *src_region_attr_cache;

  uint *heap_oop_shift_cache2;
  bool *heap_type_is_young2;

  uint *localBot;

  volatile uintptr_t par_allocate_owner = 0;

  void evacuate_live_objects(G1ParScanThreadState *pss,
                             uint worker_id,
                             G1GCPhaseTimes::GCParPhases objcopy_phase,
                             G1GCPhaseTimes::GCParPhases termination_phase)
  {
    G1GCPhaseTimes *p = _g1h->phase_times();

    Ticks start = Ticks::now();
    G1ParEvacuateFollowersClosure cl(_g1h, pss, _task_queues, &_terminator, objcopy_phase);
    cl.do_void();

    assert(pss->queue_is_empty(), "should be empty");

    Tickspan evac_time = (Ticks::now() - start);
    p->record_or_add_time_secs(objcopy_phase, worker_id, evac_time.seconds() - cl.term_time());

    if (termination_phase == G1GCPhaseTimes::Termination)
    {
      p->record_time_secs(termination_phase, worker_id, cl.term_time());
      p->record_thread_work_item(termination_phase, worker_id, cl.term_attempts());
    }
    else
    {
      p->record_or_add_time_secs(termination_phase, worker_id, cl.term_time());
      p->record_or_add_thread_work_item(termination_phase, worker_id, cl.term_attempts());
    }
    assert(pss->trim_ticks().value() == 0,
           "Unexpected partial trimming during evacuation value " JLONG_FORMAT,
           pss->trim_ticks().value());
  }

  virtual void start_work(uint worker_id) {}

  virtual void end_work(uint worker_id) {}

  virtual void scan_roots(G1ParScanThreadState *pss, uint worker_id) = 0;

  virtual void evacuate_live_objects(G1ParScanThreadState *pss, uint worker_id) = 0;

public:
  G1EvacuateRegionsBaseTask(const char *name,
                            G1ParScanThreadStateSet *per_thread_states,
                            G1ScannerTasksQueueSet *task_queues,
                            uint num_workers) : AbstractGangTask(name),
                                                _g1h(G1CollectedHeap::heap()),
                                                _per_thread_states(per_thread_states),
                                                _task_queues(task_queues),
                                                _terminator(num_workers, _task_queues),
                                                _num_workers(num_workers)
  {
    // initial cache variable
    do_oop_region_cache = (uint *)calloc(_num_workers, 4);

    obj_shift_cache = (uint *)calloc(_num_workers, 4);
    attr_type_cache = (int8_t *)calloc(_num_workers, 1);

    byte_about_valid = (bool *)calloc(_num_workers, 1);
    byte_map_base_cache = (uintptr_t *)calloc(_num_workers, 8);
    byte_map_cache = (uintptr_t *)calloc(_num_workers, 8);
    last_index_valid = (bool *)calloc(_num_workers, 1);
    last_index_cache = (uintptr_t *)calloc(_num_workers, 8);
    parScan_offset20_valid = (bool *)calloc(_num_workers, 1);
    parScan_offset40_valid = (bool *)calloc(_num_workers, 1);
    index_cache = (uintptr_t *)calloc(_num_workers, 8);
    buffer_cache = (uintptr_t *)calloc(_num_workers, 8);
    node_allocator_ptr_cache = (uintptr_t *)calloc(_num_workers, 8);
    offset30_cache = (uintptr_t *)calloc(_num_workers, 8);
    offset38_cache = (uintptr_t *)calloc(_num_workers, 8);

    dest_attr_valid = (bool *)calloc(_num_workers, 1);
    dest_attr_cache = (uint *)calloc(_num_workers, 4);

    plab_buffer_valid = (bool **)calloc(_num_workers, sizeof(bool *));
    plab_buffer_ptr_cache = (uintptr_t **)calloc(_num_workers, sizeof(uintptr_t *));
    plab_top_cache = (uintptr_t **)calloc(_num_workers, sizeof(uintptr_t *));
    plab_end_cache = (uintptr_t **)calloc(_num_workers, sizeof(uintptr_t *));
    plab_top_end_valid = (bool **)calloc(_num_workers, sizeof(bool *));

    plab_stats_valid = (bool **)calloc(_num_workers, sizeof(bool *));
    plab_stats_cache = (uintptr_t **)calloc(_num_workers, sizeof(uintptr_t *));

    region_ptr_valid = (bool **)calloc(_num_workers, sizeof(bool *));
    region_ptr_cache = (uintptr_t **)calloc(_num_workers, sizeof(uintptr_t *));
    alloc_region_valid = (bool **)calloc(_num_workers, sizeof(bool *));
    alloc_region_cache = (uintptr_t **)calloc(_num_workers, sizeof(uintptr_t *));

    for (uint i = 0; i < num_workers; ++i)
    {
      plab_buffer_valid[i] = (bool *)calloc(2, sizeof(bool));
      plab_buffer_ptr_cache[i] = (uintptr_t *)calloc(2, sizeof(uintptr_t));
      plab_top_cache[i] = (uintptr_t *)calloc(2, sizeof(uintptr_t));
      plab_end_cache[i] = (uintptr_t *)calloc(2, sizeof(uintptr_t));
      plab_top_end_valid[i] = (bool *)calloc(2, sizeof(bool));
      plab_stats_valid[i] = (bool *)calloc(2, sizeof(bool));
      plab_stats_cache[i] = (uintptr_t *)calloc(2, sizeof(uintptr_t));
      region_ptr_valid[i] = (bool *)calloc(2, sizeof(bool));
      region_ptr_cache[i] = (uintptr_t *)calloc(2, sizeof(uintptr_t));
      alloc_region_valid[i] = (bool *)calloc(2, sizeof(bool));
      alloc_region_cache[i] = (uintptr_t *)calloc(2, sizeof(uintptr_t));
    }

    heap_oop_shift_cache = (uint *)calloc(_num_workers, 4);
    heap_type_is_young = (bool *)calloc(_num_workers, 1);

    src_region_ptr_cache = (uintptr_t *)calloc(_num_workers, 8);
    src_region_attr_cache = (uint16_t *)calloc(_num_workers, 2);

    heap_oop_shift_cache2 = (uint *)calloc(_num_workers, 4);
    heap_type_is_young2 = (bool *)calloc(_num_workers, 1);

    localBot = (uint *)calloc(_num_workers, 4);

    list_length = 0;
    list_head_ptr = 0;
    list_end_ptr = 0;
    list_last_ptr = 0;

    grow_array_ptr_cache_valid = false;
    region_attr_base_valid = false;
    expand_failure_valid = false;
    during_im_valid = false;
  }

#define TRACE 0
#define IFDEF(cond, stmt) \
  if (cond)               \
    do                    \
    {                     \
      stmt;               \
    } while (0);
#define OopSize (UseCompressedOops ? 4 : 8)
#define ArrayLenOff (UseCompressedClassPointers ? 12 : 16)
#define ArrayElementOff (UseCompressedClassPointers ? 16 : 24)
/*----------------- KID --------------------------*/
#define InstanceKlassID 0
#define InstanceRefKlassID 1
#define InstanceMirrorKlassID 2
#define InstanceClassLoaderKlassID 3
#define TypeArrayKlassID 4
#define ObjectArrayKlassID 5

  uintptr_t buffer_node_allocate(uintptr_t allocator_ptr)
  {
    uintptr_t node = 0;
    uintptr_t free_list_ptr = allocator_ptr + 0x80;
    {
      node = *(uintptr_t *)free_list_ptr;
      IFDEF(TRACE, tty->print_cr("buffer_node_allocate: access %lx (%d bytes) to get %lx", free_list_ptr, 8, node));

      uintptr_t new_top = 0;
      if (node != 0)
      {
        new_top = *(uintptr_t *)(node + 0x8);
        IFDEF(TRACE, tty->print_cr("buffer_node_allocate: access %lx (%d bytes) to get %lx", node + 0x8, 8, new_top));
      }
      *(uintptr_t *)free_list_ptr = new_top;
      IFDEF(TRACE, tty->print_cr("buffer_node_allocate: access %lx (%d bytes) to write %lx", free_list_ptr, 8, new_top));

      if (node != 0)
      {
        *(uintptr_t *)(node + 0x8) = 0;
        IFDEF(TRACE, tty->print_cr("buffer_node_allocate: access %lx (%d bytes) to write %x", node + 0x8, 8, 0));
      }
    }
    if (node == 0)
    {
      IFDEF(TRACE, tty->print_cr("needs interrupt to call buffernode_allocate"));
      node = (uintptr_t)BufferNode::allocate(*(size_t *)(allocator_ptr));
    }
    return node + 0x10;
  }

  void aop_work_enqueue_card(uintptr_t region_attr_ptr, uintptr_t p, G1ParScanThreadState *pss, uint worker_id)
  {
    uint8_t needs_remset_update = *(uint8_t *)(region_attr_ptr);
    IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to get %x", region_attr_ptr, 1, needs_remset_update));

    if (needs_remset_update == 0)
      return;

    uintptr_t ct_ptr = *(uintptr_t *)((uintptr_t)pss + 0x60);
    IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to get %lx", (uintptr_t)pss + 0x60, 8, ct_ptr));

    if (!byte_about_valid[worker_id])
    {
      byte_about_valid[worker_id] = true;
      byte_map_cache[worker_id] = *(uintptr_t *)(ct_ptr + 0x38);
      byte_map_base_cache[worker_id] = *(uintptr_t *)(ct_ptr + 0x40);
      IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to get %lx", ct_ptr + 0x38, 8, byte_map_cache[worker_id]));
      IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to get %lx", ct_ptr + 0x40, 8, byte_map_base_cache[worker_id]));
    }

    uintptr_t res = byte_map_base_cache[worker_id] + (p >> 9);
    size_t card_index = res - byte_map_cache[worker_id];

    if (!last_index_valid[worker_id])
    {
      last_index_valid[worker_id] = true;
      last_index_cache[worker_id] = *(size_t *)((uintptr_t)pss + 0x1b0);
      IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to get %lx", (uintptr_t)pss + 0x1b0, 8, *(size_t *)((uintptr_t)pss + 0x1b0)));
    }

    if (last_index_cache[worker_id] != card_index)
    {
      uintptr_t rdc_local_qset_ptr = (uintptr_t)pss->getRdcQueueSetPtr();

      if (!parScan_offset40_valid[worker_id])
      {
        parScan_offset40_valid[worker_id] = true;
        index_cache[worker_id] = *(size_t *)(rdc_local_qset_ptr + 0x30);
        buffer_cache[worker_id] = *(uintptr_t *)(rdc_local_qset_ptr + 0x40);
        IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to get %lx", rdc_local_qset_ptr + 0x30, 8, index_cache[worker_id]));
        IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to get %lx", rdc_local_qset_ptr + 0x40, 8, buffer_cache[worker_id]));
      }

      if (index_cache[worker_id] / 8 == 0)
      {
        uintptr_t node = 0;
        if (!parScan_offset20_valid[worker_id])
        {
          parScan_offset20_valid[worker_id] = true;
          node_allocator_ptr_cache[worker_id] = *(uintptr_t *)(rdc_local_qset_ptr + 0x8);
          offset30_cache[worker_id] = *(uintptr_t *)(rdc_local_qset_ptr + 0x18);
          offset38_cache[worker_id] = *(uintptr_t *)(rdc_local_qset_ptr + 0x20);
          IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to get %lx", rdc_local_qset_ptr + 0x8, 8, node_allocator_ptr_cache[worker_id]));
          IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to get %lx", rdc_local_qset_ptr + 0x18, 8, offset30_cache[worker_id]));
          IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to get %lx", rdc_local_qset_ptr + 0x20, 8, offset38_cache[worker_id]));
        }

        if (buffer_cache[worker_id] != 0)
        {
          node = buffer_cache[worker_id] - 0x10;

          *(uintptr_t *)node = 0;
          *(uintptr_t *)(node + 0x8) = offset30_cache[worker_id];
          IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to write %x", node, 8, 0));
          IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to write %lx", node + 0x8, 8, offset30_cache[worker_id]));

          offset30_cache[worker_id] = node;
          if (offset38_cache[worker_id] == 0)
            offset38_cache[worker_id] = node;
        }
        buffer_cache[worker_id] = buffer_node_allocate(node_allocator_ptr_cache[worker_id]);
        index_cache[worker_id] = *(size_t *)(node_allocator_ptr_cache[worker_id]) * 8;
      }

      int idx = index_cache[worker_id] / 8 - 1;
      *(size_t *)(buffer_cache[worker_id] + idx * 8) = res;
      IFDEF(TRACE, tty->print_cr("aop: access %lx (%d bytes) to write %lx", buffer_cache[worker_id] + idx * 8, 8, res));
      index_cache[worker_id] = idx * 8;
      last_index_cache[worker_id] = card_index;
    }
  }

  void do_oop_work(uintptr_t src, uintptr_t dest, uint scanning_in_young, G1ParScanThreadState *pss, uint worker_id)
  {
    uintptr_t heap_oop, obj;

    if (UseCompressedOops)
      heap_oop = *(uint32_t *)src;
    else
      heap_oop = *(uintptr_t *)(src);
    IFDEF(TRACE, tty->print_cr("do_oop_work: access %lx (%d bytes) to get %lx", src, 8, heap_oop));

    if (heap_oop == 0)
      return;

    if (UseCompressedOops)
      obj = (uintptr_t)CompressedOops::base() + ((uintptr_t)heap_oop << CompressedOops::shift());
    else
      obj = heap_oop;

    // 15 in mechrevo r78845h 16 in others
    // tty->print_cr("1---%x", HeapRegion::LogOfHRGrainBytes);
    uint shift_obj = obj >> pss->getRegionAttrShiftBy();
    uintptr_t region_attr_ptr = pss->getRegionAttrBiasedBase() + shift_obj * 2;
    if (shift_obj != obj_shift_cache[worker_id])
    {
      obj_shift_cache[worker_id] = shift_obj;
      attr_type_cache[worker_id] = *(int8_t *)(region_attr_ptr + 1);
      IFDEF(TRACE, tty->print_cr("do_oop_work: access %lx (%x bytes) to get %x", region_attr_ptr + 1, 1, attr_type_cache[worker_id]));
    }

    if (attr_type_cache[worker_id] >= 0)
    {
      uintptr_t elems = pss->getTaskQueueElemsBase();
      *(uintptr_t *)(elems + localBot[worker_id] * 8) = UseCompressedOops ? dest + 0x1 : dest;
      IFDEF(TRACE, tty->print_cr("do_oop_work: access %lx (%x bytes) to write %lx", elems + localBot[worker_id] * 8, 8, UseCompressedOops ? dest + 0x1 : dest));
      localBot[worker_id] = localBot[worker_id] + 1;
    }
    else if (((dest ^ obj) >> HeapRegion::LogOfHRGrainBytes) != 0)
    {
      // 不会是-3 optional
      if (attr_type_cache[worker_id] == -2)
      {
        uint region_bias = pss->getHeapRegionBias();
        uint region_shiftby = pss->getHeapRegionShiftBy();
        size_t pointer_delta = obj - ((uintptr_t)region_bias << region_shiftby);
        uint region = pointer_delta >> HeapRegion::LogOfHRGrainBytes;

        if (region != do_oop_region_cache[worker_id])
        {
          uintptr_t bool_base = _g1h->getHumongousReclaimCandidatesBoolBase();
          IFDEF(TRACE, tty->print_cr("do_oop_work: access %lx (%x bytes) to get %x", bool_base + region, 1, *(bool *)(bool_base + region)));
          if (*(bool *)(bool_base + region))
          {
            *(bool *)(bool_base + region) = false;
            IFDEF(TRACE, tty->print_cr("do_oop_work: access %lx (%x bytes) to write %x", bool_base + region, 1, 0));

            uintptr_t region_attr = pss->getRegionAttrBase() + region * 2;
            *(int8_t *)(region_attr + 1) = -1;
            IFDEF(TRACE, tty->print_cr("do_oop_work: access %lx (%x bytes) to write %x", region_attr + 1, 1, -1));
          }
          do_oop_region_cache[worker_id] = region;
        }
      }

      if (scanning_in_young == 1)
        return;

      aop_work_enqueue_card(region_attr_ptr, dest, pss, worker_id);
      // pss->enqueue_card_if_tracked(*(G1HeapRegionAttr *)region_attr_ptr, (oop *)dest, (oop)obj);
    }
  }

  uintptr_t par_allocate_iml(uintptr_t alloc_region, size_t min_word_size, size_t desired_word_size, size_t *actual_plab_size, uint worker_id)
  {
    /*
    template<>
template<typename T>
inline T Atomic::PlatformCmpxchg<8>::operator()(T volatile* dest,
                                                T compare_value,
                                                T exchange_value,
                                                atomic_memory_order order) const {
  STATIC_ASSERT(8 == sizeof(T));

  // Note that cmpxchg guarantees a two-way memory barrier across
  // the cmpxchg, so it's really a a 'fence_cmpxchg_fence' if not
  // specified otherwise (see atomic.hpp).

  T old_value;
  const uint64_t zero = 0;

  pre_membar(order);

  __asm__ __volatile__ (
    // simple guard
    "   ld      %[old_value], 0(%[dest])                \n"
    "   cmpd    %[compare_value], %[old_value]          \n"
    "   bne-    2f                                      \n"
    // atomic loop
    "1:                                                 \n"
    "   ldarx   %[old_value], %[dest], %[zero]          \n"
    "   cmpd    %[compare_value], %[old_value]          \n"
    "   bne-    2f                                      \n"
    "   stdcx.  %[exchange_value], %[dest], %[zero]     \n"
    "   bne-    1b                                      \n"
    // exit
    "2:                                                 \n"
        // out
        : [old_value]       "=&r"   (old_value),
                            "=m"    (*dest)
        // in
        : [dest]            "b"     (dest),
          [zero]            "r"     (zero),
          [compare_value]   "r"     (compare_value),
          [exchange_value]  "r"     (exchange_value),
                            "m"     (*dest)
        // clobber
        : "cc",
          "memory"
        );

    post_membar(order);

    return old_value;
  }
  */
    uintptr_t alloc_result;
    do
    {
      uintptr_t top = *(uintptr_t *)(alloc_region + 0x10);
      IFDEF(TRACE, tty->print_cr("par_allocate_iml: access %lx (%x bytes) to get %lx", alloc_region + 0x10, 8, top));

      uintptr_t end = *(uintptr_t *)(alloc_region + 0x8);
      IFDEF(TRACE, tty->print_cr("par_allocate_iml: access %lx (%x bytes) to get %lx", alloc_region + 0x8, 8, end));

      size_t available = (end - top) / 8;
      size_t want_to_allocate = available > desired_word_size ? desired_word_size : available;
      if (want_to_allocate >= min_word_size)
      {
        uintptr_t new_top = top + want_to_allocate * 8;
        uintptr_t result = Atomic::cmpxchg((uintptr_t *)(alloc_region + 0x10), top, new_top);
        if (result == top)
        {
          *actual_plab_size = want_to_allocate;
          return top;
        }
      }
      else
        return 0;
    } while (true);
  }

  uintptr_t par_allocate(uintptr_t alloc_region, size_t min_word_size, size_t desired_word_size, size_t *actual_word_size, bool bot_updates, uint worker_id)
  {
    uintptr_t result = par_allocate_iml(alloc_region, min_word_size, desired_word_size, actual_word_size, worker_id);

    if (result != 0 && bot_updates)
    {
      uintptr_t blk_start = result;
      uintptr_t blk_end = result + (*actual_word_size * 8);
      uintptr_t bot_part_ptr = alloc_region + 0x20;
      uintptr_t next_offset_threshold = *(uintptr_t *)(bot_part_ptr);
      IFDEF(TRACE, tty->print_cr("par_allocate: access %lx (%x bytes) to get %lx", bot_part_ptr, 8, next_offset_threshold));

      if (blk_end > next_offset_threshold)
      {
        uintptr_t threshold = next_offset_threshold;
        size_t index = *(uintptr_t *)(bot_part_ptr + 0x8);
        IFDEF(TRACE, tty->print_cr("par_allocate: access %lx (%x bytes) to get %lx", bot_part_ptr + 0x8, 8, index));

        uintptr_t bot_ptr = *(uintptr_t *)(bot_part_ptr + 0x10);
        IFDEF(TRACE, tty->print_cr("par_allocate: access %lx (%x bytes) to get %lx", bot_part_ptr + 0x10, 8, bot_ptr));

        uintptr_t array = *(uintptr_t *)(bot_ptr + 0x10);
        IFDEF(TRACE, tty->print_cr("par_allocate: access %lx (%x bytes) to get %lx", bot_ptr + 0x10, 8, array));

        size_t offset = (threshold - blk_start) / 8;
        *(uint8_t *)(array + index) = offset;
        IFDEF(TRACE, tty->print_cr("par_allocate: access %lx (%x bytes) to write %lx", array + index, 1, offset));

        uintptr_t reserved_start = *(uintptr_t *)(bot_ptr);
        IFDEF(TRACE, tty->print_cr("par_allocate: access %lx (%x bytes) to get %lx", bot_ptr, 8, reserved_start));

        size_t end_index = (blk_end - 8 - reserved_start) >> 9;

        if (index + 1 <= end_index)
        {
          uintptr_t rem_st = reserved_start + ((index + 1) << 6) * 8;
          uintptr_t rem_end = reserved_start + ((end_index << 6) + 64) * 8;

          if (rem_st < rem_end)
          {
            size_t start_card = (rem_st - reserved_start) >> 9;
            size_t end_card = (rem_end - 8 - reserved_start) >> 9;

            if (start_card <= end_card)
            {
              size_t remaining = end_card - start_card + 1;
              uintptr_t begin = array + start_card;

              for (uint i = 0; i < 14 && remaining > 0; i++)
              {
                size_t chunk = size_t(15) << (4 * i); // 15 * 16^i
                size_t nbytes = (remaining < chunk) ? remaining : chunk;
                u_char offset = u_char(64 + i);

                memset((void *)begin, offset, nbytes);

                IFDEF(TRACE, tty->print_cr("par_allocate: access %lx (%zx bytes) to write %x", begin, nbytes, offset));

                begin += nbytes;
                remaining -= nbytes;
              }
            }
          }
        }

        index = end_index + 1;
        threshold = reserved_start + ((end_index << 6) + 64) * 8;
        *(uintptr_t *)(bot_part_ptr) = threshold;
        *(uintptr_t *)(bot_part_ptr + 0x8) = index;
        IFDEF(TRACE, tty->print_cr("par_allocate: access %lx (%x bytes) to write %lx", bot_part_ptr, 8, threshold));
        IFDEF(TRACE, tty->print_cr("par_allocate: access %lx (%x bytes) to write %lx", bot_part_ptr + 0x8, 8, index));
      }
    }
    return result;
  }

  uintptr_t allocate_free_region(uint heap_region_type, uint node_index, uint worker_id)
  {
    uintptr_t hrm_ptr = (uintptr_t)_g1h + 0x130;
    uintptr_t free_list_ptr = hrm_ptr + 0xb0;
    bool from_head = (heap_region_type & 0x2) == 0;

    uintptr_t res = 0;

    if (res == 0)
    {
      list_length = *(uint *)(free_list_ptr + 0x10);
      list_head_ptr = *(uintptr_t *)(free_list_ptr + 0x28);
      list_end_ptr = *(uintptr_t *)(free_list_ptr + 0x30);
      list_last_ptr = *(uintptr_t *)(free_list_ptr + 0x38);
      IFDEF(TRACE, tty->print_cr("allocate_free: access %lx (%x bytes) to get %x", free_list_ptr + 0x10, 4, list_length));
      IFDEF(TRACE, tty->print_cr("allocate_free: access %lx (%x bytes) to get %lx", free_list_ptr + 0x28, 8, list_head_ptr));
      IFDEF(TRACE, tty->print_cr("allocate_free: access %lx (%x bytes) to get %lx", free_list_ptr + 0x30, 8, list_end_ptr));
      IFDEF(TRACE, tty->print_cr("allocate_free: access %lx (%x bytes) to get %lx", free_list_ptr + 0x38, 8, list_last_ptr));
      if (list_length == 0)
        res = 0;
      else
      {
        res = from_head ? list_head_ptr : list_end_ptr;

        uintptr_t res_conf = *(uintptr_t *)(res + (from_head ? 0xd0 : 0xd8));
        IFDEF(TRACE, tty->print_cr("allocate_free: access %lx (%x bytes) to get %lx", res + (from_head ? 0xd0 : 0xd8), 8, res_conf));

        uintptr_t addr = free_list_ptr + (from_head ? 0x28 : 0x30);
        *(uintptr_t *)addr = res_conf;
        IFDEF(TRACE, tty->print_cr("allocate_free: access %lx (%x bytes) to write %lx", addr, 8, res_conf));

        if (res_conf == 0)
        {
          uintptr_t addr = free_list_ptr + (from_head ? 0x30 : 0x28);
          *(uintptr_t *)addr = 0;
          IFDEF(TRACE, tty->print_cr("allocate_free: access %lx (%x bytes) to write %x", addr, 8, 0));
        }
        else
        {
          *(uintptr_t *)(res_conf + (from_head ? 0xd8 : 0xd0)) = 0;
          IFDEF(TRACE, tty->print_cr("allocate_free: access %lx (%x bytes) to write %x", res_conf + (from_head ? 0xd8 : 0xd0), 8, 0));
        }

        *(uintptr_t *)(res + (from_head ? 0xd0 : 0xd8)) = 0;
        IFDEF(TRACE, tty->print_cr("allocate_free: access %lx (%x bytes) to write %x", res + (from_head ? 0xd0 : 0xd8), 8, 0));
      }
    }

    if (res != 0)
    {
      if (list_last_ptr == res)
      {
        *(uintptr_t *)(free_list_ptr + 0x38) = 0;
        IFDEF(TRACE, tty->print_cr("allocate_free: access %lx (%x bytes) to write %x", free_list_ptr + 0x38, 8, 0));
      }
      list_length -= 1;
      *(uintptr_t *)(free_list_ptr + 0x10) = list_length;
      IFDEF(TRACE, tty->print_cr("allocate_free: access %lx (%x bytes) to write %x", free_list_ptr + 0x10, 4, list_length));
    }

    return res;
  }

  uintptr_t new_region(uint heap_region_type, uint node_index, uint worker_id)
  {
    uintptr_t res = allocate_free_region(heap_region_type, node_index, worker_id);

    if (!expand_failure_valid)
    {
      expand_failure_valid = true;
      expand_failure_cache = *(bool *)((uintptr_t)_g1h + 0x370);
      IFDEF(TRACE, tty->print_cr("new_region: access %lx (%x bytes) to get %x", (uintptr_t)_g1h + 0x370, 1, expand_failure_cache));
    }

    if (res == 0 && expand_failure_cache)
    {
      IFDEF(TRACE, tty->print_cr("needs interrupt to call expand_single_region"));
      if (_g1h->expand_single_region(node_index))
        res = allocate_free_region(heap_region_type, node_index, worker_id);
      else
      {
        *(bool *)((uintptr_t)_g1h + 0x370) = false;
        expand_failure_cache = false;
        IFDEF(TRACE, tty->print_cr("new_region: access %lx (%x bytes) to write %x", (uintptr_t)_g1h + 0x370, 1, 0));
      }
    }

    return res;
  }

  uintptr_t new_gc_alloc_region(uintptr_t region_ptr, size_t word_sz, int8_t type, uint worker_id)
  {
    uint node_index = *(uint *)(region_ptr + 0x30);
    IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to get %x", region_ptr + 0x30, 4, node_index));

    bool has_more_regions;
    uint heap_region_type;
    if (type == 1)
      heap_region_type = 0x10;
    else
      heap_region_type = 0x3;

    uintptr_t new_alloc_region = new_region(heap_region_type, node_index, worker_id);

    uintptr_t survivor_ptr = (uintptr_t)_g1h + 0x3f8;
    if (!grow_array_ptr_cache_valid)
    {
      grow_array_ptr_cache_valid = true;
      grow_array_ptr_cache = *(uintptr_t *)(survivor_ptr + 0x8);
      IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to get %lx", survivor_ptr + 0x8, 8, grow_array_ptr_cache));
    }
    uintptr_t grow_array_ptr = grow_array_ptr_cache;

    if (new_alloc_region != 0)
    {
      IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to write %x", (uintptr_t)new_alloc_region + 0xbc, 4, heap_region_type));
      if (heap_region_type == 0x3)
      {
        *(uint *)(new_alloc_region + 0xbc) = 0x3;

        int len = *(int *)(grow_array_ptr);
        int max = *(int *)(grow_array_ptr + 0x4);
        IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to get %lx", grow_array_ptr, 8, *(uintptr_t *)grow_array_ptr));

        if (len == max)
        {
          IFDEF(TRACE, tty->print_cr("needs interrupt to call grow array grow"));
          ((GrowableArray<HeapRegion *> *)grow_array_ptr)->grow(len);
        }
        int idx = len;
        ++len;
        *(int *)(grow_array_ptr) = len;
        IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to write %x", grow_array_ptr, 4, len));

        uintptr_t data_ptr = *(uintptr_t *)(grow_array_ptr + 0x8);
        IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to get %lx", grow_array_ptr + 0x8, 8, data_ptr));

        *(uintptr_t *)(data_ptr + idx * 8) = new_alloc_region;
        IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to write %lx", data_ptr + idx * 8, 8, new_alloc_region));
      }
      else
        *(uint *)(new_alloc_region + 0xbc) = 0x10;

      uintptr_t remset_ptr = *(uintptr_t *)(new_alloc_region + 0xb0);
      IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to get %lx", new_alloc_region + 0xb0, 8, remset_ptr));

      uintptr_t state_ptr = remset_ptr + 0xf0;
      if ((heap_region_type & 0x2) != 0)
        *(uint *)state_ptr = 2;
      else if ((heap_region_type & 0x10) != 0)
        *(uint *)state_ptr = 0;
      IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to write %x", state_ptr, 4, *(uint *)state_ptr));

      uint hrm_index = *(uint *)(new_alloc_region + 0xb8);
      IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to get %x", new_alloc_region + 0xb8, 4, hrm_index));

      bool needs_remset_update = (heap_region_type & 0x10) == 0;
      uintptr_t g1h_region_attr_ptr = (uintptr_t)_g1h + 0x580;
      if (!region_attr_base_valid)
      {
        region_attr_base_valid = true;
        region_attr_base_cache = *(uintptr_t *)(g1h_region_attr_ptr + 0x10);
        IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to get %lx", g1h_region_attr_ptr + 0x10, 8, region_attr_base_cache));
      }
      uintptr_t region_attr_base = region_attr_base_cache;

      *(u_int8_t *)(region_attr_base + hrm_index * 2) = needs_remset_update;
      IFDEF(TRACE, tty->print_cr("new_gc_alloc: access %lx (%x bytes) to write %x", region_attr_base + hrm_index * 2, 1, needs_remset_update));

      return new_alloc_region;
    }
    return 0;
  }

  uintptr_t attempt_allocation_using_new_region(uintptr_t region_ptr, uintptr_t alloc_region, uintptr_t dummy_region, size_t min_word_size, size_t desired_word_size, size_t *actual_word_size, uint worker_id)
  {
    int8_t type = *(int8_t *)(region_ptr + 0x40);
    IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %x", region_ptr + 0x40, 1, type));

    uintptr_t new_alloc_region = new_gc_alloc_region(region_ptr, desired_word_size, type, worker_id);

    if (alloc_region != dummy_region)
    {
      // fill up can set false
      uintptr_t bottom = *(uintptr_t *)(alloc_region);
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", alloc_region, 8, bottom));

      uintptr_t top = *(uintptr_t *)(alloc_region + 0x10);
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", alloc_region + 0x10, 8, bottom));

      size_t allocated_bytes = top - bottom - *(uintptr_t *)(region_ptr + 0x18);
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", region_ptr + 0x18, 8, *(uintptr_t *)(region_ptr + 0x18)));

      if (type == 1)
      {
        uintptr_t old_set = (uintptr_t)_g1h + 0xa0;
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %x", old_set + 0x10, 4, *(uint *)(old_set + 0x10)));
        *(uint *)(old_set + 0x10) += 1;
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to write %x", old_set + 0x10, 4, *(uint *)(old_set + 0x10)));
      }
      else
      {
        uintptr_t survivor_ptr = (uintptr_t)_g1h + 0x3f8;
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", survivor_ptr + 0x10, 8, *(uintptr_t *)(survivor_ptr + 0x10)));
        *(size_t *)(survivor_ptr + 0x10) += allocated_bytes;
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", survivor_ptr + 0x10, 8, *(uintptr_t *)(survivor_ptr + 0x10)));
      }

      if (!during_im_valid)
      {
        during_im_valid = true;
        during_im_cache = *(bool *)((uintptr_t)_g1h + 0x3c1);
        cm_cache = *(uintptr_t *)((uintptr_t)_g1h + 0x4e8);
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %x", (uintptr_t)_g1h + 0x3c1, 1, during_im_cache));
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", (uintptr_t)_g1h + 0x4e8, 8, cm_cache));
      }

      if (during_im_cache && allocated_bytes > 0)
      {
        uintptr_t start = *(uintptr_t *)(alloc_region + 0xe8);
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", alloc_region + 0xe8, 8, start));

        uintptr_t end = *(uintptr_t *)(alloc_region + 0x10);
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", alloc_region + 0x10, 8, end));

        uintptr_t root_regions_ptr = cm_cache + 0xb0;
        uintptr_t root_regions_array = *(uintptr_t *)(root_regions_ptr);
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", root_regions_ptr, 8, root_regions_array));

        uintptr_t idx = *(uintptr_t *)(root_regions_ptr + 0x10);
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", root_regions_ptr + 0x10, 8, idx));

        uintptr_t mem_region = root_regions_array + idx * 0x10;

        *(uintptr_t *)(mem_region) = start;
        *(uintptr_t *)(mem_region + 0x8) = (end - start) / 8;
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to write %lx", mem_region, 8, start));
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to write %lx", mem_region + 0x8, 8, (end - start) / 8));

        *(uintptr_t *)(root_regions_ptr + 0x10) = idx + 1;
        IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to write %lx", root_regions_ptr + 0x10, 8, idx + 1));
      }

      *(uintptr_t *)(region_ptr + 0x18) = 0;
      *(uintptr_t *)(region_ptr + 0x8) = dummy_region;
      for (uint i = 0; i < _num_workers; ++i)
        for (int j = 0; j < 2; ++j)
          if (region_ptr_valid[i][j] && region_ptr_cache[i][j] == region_ptr && alloc_region_valid[i][j])
            alloc_region_cache[i][j] = dummy_region;
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to write %x", region_ptr + 0x18, 8, 0));
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to write %lx", region_ptr + 0x8, 8, dummy_region));
    }

    if (new_alloc_region != 0)
    {
      bool bot_updates = *(bool *)(region_ptr + 0x20);
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %x", region_ptr + 0x20, 1, bot_updates));

      size_t temp;
      uintptr_t result = par_allocate(new_alloc_region, desired_word_size, desired_word_size, &temp, bot_updates, worker_id);

      *(uintptr_t *)(new_alloc_region + 0xa8) = 0;
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to write %x", new_alloc_region + 0xa8, 8, 0));

      uintptr_t bottom = *(uintptr_t *)(new_alloc_region);
      uintptr_t top = *(uintptr_t *)(new_alloc_region + 0x10);
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", new_alloc_region, 8, bottom));
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %lx", new_alloc_region + 0x10, 8, top));

      *(uintptr_t *)(region_ptr + 0x18) = top - bottom;
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to write %lx", region_ptr + 0x18, 8, top - bottom));

      *(uintptr_t *)(region_ptr + 0x8) = new_alloc_region;
      for (uint i = 0; i < _num_workers; ++i)
        for (int j = 0; j < 2; ++j)
          if (region_ptr_valid[i][j] && region_ptr_cache[i][j] == region_ptr && alloc_region_valid[i][j])
            alloc_region_cache[i][j] = new_alloc_region;
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to write %lx", region_ptr + 0x8, 8, new_alloc_region));

      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to get %x", region_ptr + 0x10, 4, *(uint *)(region_ptr + 0x10)));
      *(uint *)(region_ptr + 0x10) += 1;
      IFDEF(TRACE, tty->print_cr("attempt_allocation: access %lx (%x bytes) to write %x", region_ptr + 0x10, 4, *(uint *)(region_ptr + 0x10)));

      if (result != 0)
        *actual_word_size = desired_word_size;
      return result;
    }
    else
      return 0;
  }

  uintptr_t par_allocate_during_gc(int8_t dest_attr_type, size_t min_word_size, size_t desired_word_size, size_t *actual_word_size, uintptr_t allocator_ptr, G1ParScanThreadState *pss, uint worker_id)
  {
    if (!region_ptr_valid[worker_id][dest_attr_type])
    {
      region_ptr_valid[worker_id][dest_attr_type] = true;
      if (dest_attr_type == 0)
      {
        uintptr_t survivor_gc_alloc_ptr = *(uintptr_t *)(allocator_ptr + 0x28);
        IFDEF(TRACE, tty->print_cr("par_allocate_during_gc: access %lx (%x bytes) to get %lx", allocator_ptr + 0x28, 8, survivor_gc_alloc_ptr));
        region_ptr_cache[worker_id][dest_attr_type] = survivor_gc_alloc_ptr;
      }
      else if (dest_attr_type == 1)
        region_ptr_cache[worker_id][dest_attr_type] = allocator_ptr + 0x30;
    }

    uintptr_t region_ptr = region_ptr_cache[worker_id][dest_attr_type];

    if (!alloc_region_valid[worker_id][dest_attr_type])
    {
      alloc_region_valid[worker_id][dest_attr_type] = true;
      alloc_region_cache[worker_id][dest_attr_type] = *(uintptr_t *)(region_ptr + 0x8);
      IFDEF(TRACE, tty->print_cr("par_allocate_during_gc: access %lx (%x bytes) to get %lx", region_ptr + 0x8, 8, alloc_region_cache[worker_id][dest_attr_type]));
    }

    uintptr_t alloc_region = alloc_region_cache[worker_id][dest_attr_type];

    uintptr_t result = 0;

    while (true)
    {
      uintptr_t old = Atomic::cmpxchg(&par_allocate_owner, (uintptr_t)0, (uintptr_t)Thread::current());
      if (old == 0)
      {
        if (dest_attr_type == 0)
          result = par_allocate_iml(alloc_region, min_word_size, desired_word_size, actual_word_size, worker_id);
        else if (dest_attr_type == 1)
        {
          uintptr_t lock_ptr = alloc_region + 0x40;
          IFDEF(TRACE, tty->print_cr("par_allocate_during_gc: access %lx (%x bytes) to get %x", lock_ptr + 8, 4, *(uint *)(lock_ptr + 8)));
          while (Atomic::cmpxchg((uint *)(lock_ptr + 8), (uint)0, (uint)1) != 0)
          {
            IFDEF(TRACE, tty->print_cr("wait par_allocate mutex"));
          }
          result = par_allocate(alloc_region, min_word_size, desired_word_size, actual_word_size, true, worker_id);
          uint old_lock_value = Atomic::cmpxchg((uint *)(lock_ptr + 8), (uint)1, (uint)0);
          if (old_lock_value > 1)
          {
            tty->print_cr("par_allocate alloc_region_lock_ptr unlock");
            ((Mutex *)(lock_ptr))->unlock();
          }
        }

        if (result == 0)
        {
          uint8_t is_full_value = *(uint8_t *)(allocator_ptr + 0x10);
          IFDEF(TRACE, tty->print_cr("par_allocate_during_gc: access %lx (%x bytes) to get %x", allocator_ptr + 0x10, 1, is_full_value));
          bool is_full = dest_attr_type == 0 ? is_full_value & 0x1 : is_full_value & 0x2;
          if (!is_full)
          {
            if (dest_attr_type == 0)
              result = par_allocate_iml(alloc_region, min_word_size, desired_word_size, actual_word_size, worker_id);
            else if (dest_attr_type == 1)
            {
              uintptr_t lock_ptr = alloc_region + 0x40;
              IFDEF(TRACE, tty->print_cr("par_allocate_during_gc: access %lx (%x bytes) to get %x", lock_ptr + 8, 4, *(uint *)(lock_ptr + 8)));
              while (Atomic::cmpxchg((uint *)(lock_ptr + 8), (uint)0, (uint)1) != 0)
              {
                IFDEF(TRACE, tty->print_cr("wait par_allocate mutex"));
              }
              result = par_allocate(alloc_region, min_word_size, desired_word_size, actual_word_size, true, worker_id);
              uint old_lock_value = Atomic::cmpxchg((uint *)(lock_ptr + 8), (uint)1, (uint)0);
              if (old_lock_value > 1)
              {
                tty->print_cr("par_allocate alloc_region_lock_ptr unlock");
                ((Mutex *)(lock_ptr))->unlock();
              }
            }

            if (result == 0)
            {
              uintptr_t freelist_lock_ptr = (uintptr_t)FreeList_lock;
              while (Atomic::cmpxchg((uint *)(freelist_lock_ptr + 8), (uint)0, (uint)1) != 0)
              {
                IFDEF(TRACE, tty->print_cr("wait par_allocate freelist lock"));
              }
              *(uintptr_t *)(freelist_lock_ptr) = (uintptr_t)Thread::current();
              IFDEF(TRACE, tty->print_cr("par_allocate_during_gc: access %lx (%x bytes) to write %lx", freelist_lock_ptr, 8, (uintptr_t)Thread::current()));

              result = attempt_allocation_using_new_region(region_ptr, alloc_region, (uintptr_t)G1AllocRegion::_dummy_region, min_word_size, desired_word_size, actual_word_size, worker_id);
              if (result == 0)
              {
                if (dest_attr_type == 0)
                  *(bool *)(allocator_ptr + 0x10) = true;
                else if (dest_attr_type == 1)
                  *(bool *)(allocator_ptr + 0x11) = true;
                uintptr_t addr = allocator_ptr + (dest_attr_type == 0 ? 0x10 : 0x11);
                IFDEF(TRACE, tty->print_cr("par_allocate_during_gc: access %lx (%x bytes) to write %x", addr, 1, true));
              }
              uint old_lock_value = Atomic::cmpxchg((uint *)(freelist_lock_ptr + 8), (uint)1, (uint)0);
              if (old_lock_value > 1)
              {
                FreeList_lock->unlock();
                tty->print_cr("par_allocate freelist lock unlock");
              }
            }
          }
        }
        *(uintptr_t *)(&par_allocate_owner) = (uintptr_t)0;
        return result;
      }
    }
  }

  uintptr_t allocate_direct_or_new_plab(u_int16_t dest_attr, size_t word_sz, bool *plab_refill_failed, uintptr_t plab_allocator_ptr, G1ParScanThreadState *pss, uint worker_id)
  {
    int8_t dest_attr_type = (int8_t)(dest_attr >> 8);

    uintptr_t plab_stats_ptr = 0;
    if (dest_attr_type == 0)
      plab_stats_ptr = (uintptr_t)_g1h + 0x250;
    else if (dest_attr_type == 1)
      plab_stats_ptr = (uintptr_t)_g1h + 0x2d0;

    uint no_of_gc_workers = _num_workers;

    size_t gclab_word_size;
    size_t min_size = 0x102;
    size_t max_size = 0x40000;
    // ResizePLAB = 1
    if (!plab_stats_valid[worker_id][dest_attr_type])
    {
      plab_stats_valid[worker_id][dest_attr_type] = true;
      plab_stats_cache[worker_id][dest_attr_type] = *(uintptr_t *)(plab_stats_ptr + 0x30);
      IFDEF(TRACE, tty->print_cr("allocate_direct_or_new_plab: access %lx (%d bytes) to get %lx", plab_stats_ptr + 0x30, 8, plab_stats_cache[worker_id][dest_attr_type]));
    }

    size_t temp = plab_stats_cache[worker_id][dest_attr_type] / no_of_gc_workers;
    gclab_word_size = MIN2(MAX2(temp, min_size), max_size);
    size_t plab_word_size = MIN2(max_size, gclab_word_size);
    size_t required_in_plab = word_sz + 0x2;

    uintptr_t allocator_ptr = *(uintptr_t *)(plab_allocator_ptr + 0x8);
    IFDEF(TRACE, tty->print_cr("allocate_direct_or_new_plab: access %lx (%d bytes) to get %lx", plab_allocator_ptr + 0x8, 8, allocator_ptr));
    bool may_throw_away_buffer = required_in_plab * 100 < plab_word_size * 0xa;
    if ((required_in_plab <= plab_word_size) && may_throw_away_buffer)
    {
      size_t actual_plab_size = 0;
      // uintptr_t obj_ptr = (uintptr_t)((G1Allocator *)allocator_ptr)->par_allocate_during_gc(dest, required_in_plab, plab_word_size, &actual_plab_size, 0);
      uintptr_t obj_ptr = par_allocate_during_gc(dest_attr_type, required_in_plab, plab_word_size, &actual_plab_size, allocator_ptr, pss, worker_id);

      uintptr_t alloc_buffers_ptr = plab_allocator_ptr + 0x10;
      int idx = dest_attr_type;
      if (!plab_buffer_valid[worker_id][idx])
      {
        plab_buffer_valid[worker_id][idx] = true;

        plab_buffer_ptr_cache[worker_id][idx] = *(uintptr_t *)(*(uintptr_t *)(alloc_buffers_ptr + dest_attr_type * 8));
        IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", alloc_buffers_ptr + dest_attr_type * 8, 8, *(uintptr_t *)(alloc_buffers_ptr + dest_attr_type * 8)));
        IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", *(uintptr_t *)(alloc_buffers_ptr + dest_attr_type * 8), 8, plab_buffer_ptr_cache[worker_id][idx]));
      }

      uintptr_t buffer = plab_buffer_ptr_cache[worker_id][idx];

      size_t result = 0;
      uintptr_t top_ptr = *(uintptr_t *)(buffer + 0x30);
      uintptr_t hard_end_ptr = *(uintptr_t *)(buffer + 0x40);
      IFDEF(TRACE, tty->print_cr("allocate_direct_or_new_plab: access %lx (%d bytes) to get %lx", buffer + 0x30, 8, top_ptr));
      IFDEF(TRACE, tty->print_cr("allocate_direct_or_new_plab: access %lx (%d bytes) to get %lx", buffer + 0x40, 8, hard_end_ptr));

      if (top_ptr < hard_end_ptr)
      {
        {
          uintptr_t start = top_ptr;
          size_t words = (hard_end_ptr - top_ptr) / 8;
          uintptr_t klass_ptr = 0;
          if (words >= (UseCompressedClassPointers ? 2 : 3))
          {
            size_t payload_size = words - (UseCompressedClassPointers ? 2 : 3);
            size_t len = payload_size * 2;
            *(int *)(start + ArrayLenOff) = len;
            IFDEF(TRACE, tty->print_cr("allocate_direct: access %lx (%x bytes) to write %lx", start + ArrayLenOff, 4, len));

            klass_ptr = (uintptr_t)Universe::intArrayKlassObj();
          }
          else if (words > 0)
            klass_ptr = (uintptr_t)vmClasses::Object_klass();
          *(uintptr_t *)start = (0x0 | 0x1);
          IFDEF(TRACE, tty->print_cr("allocate_direct: access %lx (%x bytes) to write %x", start, 8, 0x1));

          if (UseCompressedClassPointers)
          {
            *(uint *)(start + 0x8) = (klass_ptr - (uintptr_t)CompressedKlassPointers::base()) >> CompressedKlassPointers::shift();
            IFDEF(TRACE, tty->print_cr("allocate_direct: access %lx (%x bytes) to write %x", start + 0x8, 4, (uint)(klass_ptr - (uintptr_t)CompressedKlassPointers::base()) >> CompressedKlassPointers::shift()));
          }
          else
          {
            *(uintptr_t *)(start + 0x8) = klass_ptr;
            IFDEF(TRACE, tty->print_cr("allocate_direct: access %lx (%x bytes) to write %lx", start + 0x8, 8, klass_ptr));
          }
        }
      }

      if (obj_ptr != 0)
      {
        // @ deletable?
        IFDEF(TRACE, tty->print_cr("allocate_direct_or_new_plab: access %lx (%d bytes) to get %lx", buffer + 0x48, 8, *(uintptr_t *)(buffer + 0x48)));
        *(uintptr_t *)(buffer + 0x20) = actual_plab_size;
        *(uintptr_t *)(buffer + 0x28) = obj_ptr;
        *(uintptr_t *)(buffer + 0x30) = obj_ptr;
        *(uintptr_t *)(buffer + 0x40) = obj_ptr + actual_plab_size * 8;
        *(uintptr_t *)(buffer + 0x38) = obj_ptr + (actual_plab_size - 2) * 8;
        *(uintptr_t *)(buffer + 0x48) += actual_plab_size;
        uintptr_t obj = obj_ptr;
        size_t delta = actual_plab_size - 2;
        if (delta >= word_sz)
          *(uintptr_t *)(buffer + 0x30) = obj + word_sz * 8;
        else
          obj = 0;
        if (TRACE)
        {
          for (int i = 0x20; i <= 0x48; i += 0x8)
            tty->print_cr("allocate_direct_or_new_plab: access %lx (%d bytes) to get %lx", buffer + i, 8, *(uintptr_t *)(buffer + i));
        }

        return obj;
      }
      else if (top_ptr < hard_end_ptr)
      {
        *(uintptr_t *)(buffer + 0x38) = hard_end_ptr;
        *(uintptr_t *)(buffer + 0x30) = hard_end_ptr;
        *(uintptr_t *)(buffer + 0x28) = hard_end_ptr;
        if (TRACE)
        {
          for (int i = 0x28; i <= 0x38; i += 0x8)
            tty->print_cr("allocate_direct_or_new_plab: access %lx (%d bytes) to get %lx", buffer + i, 8, *(uintptr_t *)(buffer + i));
        }
      }

      *plab_refill_failed = true;
    }

    temp = 0;
    // uintptr_t obj = (uintptr_t)((G1Allocator *)allocator_ptr)->par_allocate_during_gc(dest, word_sz, word_sz, &temp, 0);
    uintptr_t obj = par_allocate_during_gc(dest_attr_type, word_sz, word_sz, &temp, allocator_ptr, pss, worker_id);
    return obj;
  }

  uintptr_t do_copy_to_survivor_space(uintptr_t src_region_attr_ptr, u_int16_t src_region_attr, uintptr_t old, uintptr_t m_value, G1ParScanThreadState *pss, uint worker_id)
  {
    uintptr_t klass_ptr;
    if (UseCompressedClassPointers)
    {
      uint offset = *(uint *)(old + 0x8);
      klass_ptr = (uintptr_t)CompressedKlassPointers::base() + ((uintptr_t)offset << CompressedKlassPointers::shift());
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %x", old + 0x8, 4, offset));
    }
    else
    {
      klass_ptr = *(uintptr_t *)(old + 0x8);
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", old + 0x8, 8, klass_ptr));
    }

    uint64_t lh_kid = *(uint64_t *)(klass_ptr + 0x8);
    IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", klass_ptr + 0x8, 8, lh_kid));
    int lh = (int)lh_kid;
    int kid = lh_kid >> 32;
    size_t size;

    if (lh < 0)
    {
      int array_length = *(int *)(old + ArrayLenOff);
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %x", old + ArrayLenOff, 4, array_length));
      // lh[7:0]是log2(esz)
      // lh[23:16]是hsz
      size_t size_in_bytes = (array_length << (uint8_t)lh) + (uint8_t)(lh >> 16);
      size = (size_t)(size_in_bytes & 0x7 ? (size_in_bytes >> LogHeapWordSize) + 1 : size_in_bytes >> LogHeapWordSize);
    }
    else if (lh > 0 && lh & 0x1 == 0)
      size = lh >> LogHeapWordSize;
    else
    {
      // size = ((oop)old)->size_given_klass((Klass *)klass_ptr);
      if (kid == InstanceMirrorKlassID)
      {
        size = *(uint *)(old + java_lang_Class::get_oop_size_offset());
        IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", old + java_lang_Class::get_oop_size_offset(), 4, size));
      }
      else
        size = lh >> 3;
    }

    uint age = 0;
    if (!dest_attr_valid[worker_id])
    {
      dest_attr_valid[worker_id] = true;
      dest_attr_cache[worker_id] = *(uint *)((uintptr_t)pss + 0x178);
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %x", (uintptr_t)pss + 0x178, 4, dest_attr_cache[worker_id]));
    }
    int8_t src_region_attr_type = (int8_t)(src_region_attr >> 8);
    u_int16_t dest_attr = src_region_attr_type == 1 ? dest_attr_cache[worker_id] >> 16 : dest_attr_cache[worker_id] & 0xffff;
    uintptr_t dest_attr_ptr = src_region_attr_type == 1 ? (uintptr_t)pss + 0x178 + 0x2 : (uintptr_t)pss + 0x178;
    if (src_region_attr_type == 0)
    {
      if ((m_value & 0x1) == 0x0)
      {
        bool has_monitor = m_value & 0x2;
        uint64_t ptr = has_monitor ? m_value ^ 0x2 : m_value;
        uint64_t mark = *(uint64_t *)ptr;
        IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", ptr, 8, mark));
        age = (mark >> 0x3) & 0x1111;
      }
      else
        age = (m_value >> 0x3) & 0x1111;

      uint threshold = *(uint *)((uintptr_t)pss + 0x17c);
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %x", (uintptr_t)pss + 0x17c, 4, threshold));
      if (age < threshold)
      {
        dest_attr = src_region_attr;
        dest_attr_ptr = src_region_attr_ptr;
      }
    }

    int8_t dest_attr_type = (int8_t)(dest_attr >> 8);
    int idx = dest_attr_type;
    uintptr_t plab_allocator_ptr = *(uintptr_t *)((uintptr_t)pss + 0x70);
    IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", (uintptr_t)pss + 0x70, 8, plab_allocator_ptr));
    uintptr_t alloc_buffers_ptr = plab_allocator_ptr + 0x10;
    if (!plab_buffer_valid[worker_id][idx])
    {
      plab_buffer_valid[worker_id][idx] = true;

      plab_buffer_ptr_cache[worker_id][idx] = *(uintptr_t *)(*(uintptr_t *)(alloc_buffers_ptr + dest_attr_type * 8));
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", alloc_buffers_ptr + dest_attr_type * 8, 8, *(uintptr_t *)(alloc_buffers_ptr + dest_attr_type * 8)));
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", *(uintptr_t *)(alloc_buffers_ptr + dest_attr_type * 8), 8, plab_buffer_ptr_cache[worker_id][idx]));
    }
    if (!plab_top_end_valid[worker_id][idx])
    {
      uintptr_t buffer = plab_buffer_ptr_cache[worker_id][idx];

      uintptr_t new_top = *(uintptr_t *)(buffer + 0x30);
      uintptr_t new_end = *(uintptr_t *)(buffer + 0x38);

      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", buffer + 0x30, 8, new_top));
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", buffer + 0x38, 8, new_end));

      plab_top_cache[worker_id][idx] = new_top;
      plab_end_cache[worker_id][idx] = new_end;

      plab_top_end_valid[worker_id][idx] = true;
    }

    uintptr_t obj_ptr = 0;
    if ((plab_end_cache[worker_id][idx] - plab_top_cache[worker_id][idx]) / 8 >= size)
    {
      obj_ptr = plab_top_cache[worker_id][idx];
      plab_top_cache[worker_id][idx] = obj_ptr + size * 8;
      *(uintptr_t *)(plab_buffer_ptr_cache[worker_id][idx] + 0x30) = plab_top_cache[worker_id][idx];
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %lx", plab_buffer_ptr_cache[worker_id][idx] + 0x30, 8, plab_top_cache[worker_id][idx]));
      int other = idx == 0 ? 1 : 0;
      if (plab_top_end_valid[worker_id][other] && plab_buffer_ptr_cache[worker_id][0] == plab_buffer_ptr_cache[worker_id][1])
        plab_top_cache[worker_id][other] = plab_top_cache[worker_id][idx];
    }
    else
    {
      obj_ptr = 0;
      plab_top_end_valid[worker_id][idx] = false;
      int other = idx == 0 ? 1 : 0;
      if (plab_top_end_valid[worker_id][other] && plab_buffer_ptr_cache[worker_id][0] == plab_buffer_ptr_cache[worker_id][1])
        plab_top_end_valid[worker_id][other] = false;
    }

    if (obj_ptr == 0)
    {
      // obj_ptr = (uintptr_t)pss->allocate_copy_slow(&dest, (oop)old, size, age, 0);
      bool is_old = dest_attr_type == 1;
      bool old_gen_is_full = *(bool *)((uintptr_t)pss + 0x1e8);
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %x", (uintptr_t)pss + 0x1e8, 1, old_gen_is_full));
      if (!(is_old && old_gen_is_full))
      {
        bool plab_refill_failed = false;
        // obj_ptr = (uintptr_t)((G1PLABAllocator *)plab_allocator_ptr)->allocate_direct_or_new_plab(dest, size, &plab_refill_failed, 0);
        obj_ptr = allocate_direct_or_new_plab(dest_attr, size, &plab_refill_failed, plab_allocator_ptr, pss, worker_id);
        if (obj_ptr == 0)
        {
          bool plab_refill_in_old_failed = false;

          // plab_allocate
          idx = 1;
          if (!plab_buffer_valid[worker_id][idx])
          {
            plab_buffer_valid[worker_id][idx] = true;

            plab_buffer_ptr_cache[worker_id][idx] = *(uintptr_t *)(*(uintptr_t *)(alloc_buffers_ptr + dest_attr_type * 8));
            IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", alloc_buffers_ptr + dest_attr_type * 8, 8, *(uintptr_t *)(alloc_buffers_ptr + dest_attr_type * 8)));
            IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", *(uintptr_t *)(alloc_buffers_ptr + dest_attr_type * 8), 8, plab_buffer_ptr_cache[worker_id][idx]));
          }
          if (!plab_top_end_valid[worker_id][idx])
          {
            uintptr_t buffer = plab_buffer_ptr_cache[worker_id][idx];

            uintptr_t new_top = *(uintptr_t *)(buffer + 0x30);
            uintptr_t new_end = *(uintptr_t *)(buffer + 0x38);

            IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", buffer + 0x30, 8, new_top));
            IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", buffer + 0x38, 8, new_end));

            plab_top_cache[worker_id][idx] = new_top;
            plab_end_cache[worker_id][idx] = new_end;

            plab_top_end_valid[worker_id][idx] = true;
          }

          if ((plab_end_cache[worker_id][idx] - plab_top_cache[worker_id][idx]) / 8 >= size)
          {
            obj_ptr = plab_top_cache[worker_id][idx];
            plab_top_cache[worker_id][idx] = obj_ptr + size * 8;
            *(uintptr_t *)(plab_buffer_ptr_cache[worker_id][idx] + 0x30) = plab_top_cache[worker_id][idx];
            IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %lx", plab_buffer_ptr_cache[worker_id][idx] + 0x30, 8, plab_top_cache[worker_id][idx]));
            if (plab_top_end_valid[worker_id][0] && plab_buffer_ptr_cache[worker_id][0] == plab_buffer_ptr_cache[worker_id][1])
              plab_top_cache[worker_id][0] = plab_top_cache[worker_id][idx];
          }
          else
          {
            obj_ptr = 0;
            plab_top_end_valid[worker_id][idx] = false;
            if (plab_top_end_valid[worker_id][0] && plab_buffer_ptr_cache[worker_id][0] == plab_buffer_ptr_cache[worker_id][1])
              plab_top_cache[worker_id][0] = false;

            G1HeapRegionAttr temp;
            temp.set_old();
            // obj_ptr = (uintptr_t)((G1PLABAllocator *)plab_allocator_ptr)->allocate_direct_or_new_plab(temp, size, &plab_refill_in_old_failed, 0);
            obj_ptr = allocate_direct_or_new_plab(*(u_int16_t *)&temp, size, &plab_refill_in_old_failed, plab_allocator_ptr, pss, worker_id);
          }

          if (plab_refill_failed)
          {
            *(uint *)((uintptr_t)pss + 0x17c) = 0;
            IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %x", (uintptr_t)pss + 0x17c, 4, 0));
          }

          // 这里会对后面的dest_attr有影响
          *(int8_t *)(dest_attr_ptr + 1) = 1;

          if (dest_attr_ptr == src_region_ptr_cache[worker_id])
          {
            ((uint8_t *)&src_region_attr_cache[worker_id])[1] = 1;
            IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %x", (uintptr_t)&src_region_ptr_cache[worker_id] + 1, 1, 1));
          }

          if (dest_attr_ptr == (uintptr_t)pss + 0x178)
          {
            ((uint8_t *)&dest_attr_cache[worker_id])[1] = 1;
            IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %x", (uintptr_t)&dest_attr_cache[worker_id] + 1, 1, 1));
          }
          else if (dest_attr_ptr == (uintptr_t)pss + 0x17a)
          {
            ((uint8_t *)&dest_attr_cache[worker_id])[3] = 1;
            IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %x", (uintptr_t)&dest_attr_cache[worker_id] + 3, 1, 1));
          }
          dest_attr_type = 1;
        }
      }
    }

    uintptr_t m = (obj_ptr & ~0x3) | 0x3;
    uintptr_t forward_ptr = 0;
    uintptr_t old_mark = Atomic::cmpxchg((uintptr_t *)old, m_value, m);
    if (old_mark == m_value)
    {
      forward_ptr = 0;
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %lx", old, 8, m));
    }
    else
      forward_ptr = old_mark & ~0x3;

    if (forward_ptr == 0)
    {
      // upadte age
      uint64_t new_mark = m_value;
      // 这里的dest attr type可能已经被修改了
      if (dest_attr_type == 0)
      {
        if ((m_value & 0x1) == 0x0)
        {
          bool has_monitor = m_value & 0x2;
          uint64_t ptr = has_monitor ? m_value ^ 0x2 : m_value;
          uint64_t mark = *(uint64_t *)ptr;
          IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", ptr, 8, mark));
          *(uint64_t *)ptr = (mark & ~(0x1111 << 3)) | (((age + 1 < 15 ? age + 1 : age) & 15) << 3);
          IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %lx", ptr, 8, (mark & ~(0x1111 << 3)) | (((age + 1 < 15 ? age + 1 : age) & 15) << 3)));
        }
        else
          new_mark = (m_value & ~(0x1111 << 3)) | (((age + 1 < 15 ? age + 1 : age) & 0x1111) << 3);
      }
      *(uint64_t *)obj_ptr = new_mark;
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %lx", obj_ptr, 8, new_mark));

      // 不重叠区域的复制
      for (size_t i = 1; i < size; ++i)
      {
        IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", old + i * 8, 8, *(uintptr_t *)(old + i * 8)));
        *(uintptr_t *)(obj_ptr + i * 8) = *(uintptr_t *)(old + i * 8);
        IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %lx", obj_ptr + i * 8, 8, *(uintptr_t *)(old + i * 8)));
      }

      uintptr_t scanning_in_young = dest_attr_type == 0;
      // obj_array trace
      if (lh < 0)
      {
        if (kid == ObjectArrayKlassID)
        {
          int array_length = *(int *)(old + ArrayLenOff);
          IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %x", old + ArrayLenOff, 4, array_length));

          int chunk_size = *(int *)((uintptr_t)pss + 0x1ec);
          IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %x", (uintptr_t)pss + 0x1ec, 4, chunk_size));

          int end = array_length % chunk_size;
          *(int *)(obj_ptr + ArrayLenOff) = end;
          IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %x", obj_ptr + ArrayLenOff, 4, end));

          uint step_index = end;
          uint step_ncreate = array_length > end ? 1u : 0u;

          for (uint i = 0; i < step_ncreate; ++i)
          {
            // push 这里只push taskqueue_t
            uintptr_t base = pss->getTaskQueueElemsBase();
            *(uintptr_t *)(base + localBot[worker_id] * 8) = old + 0x2;
            IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %lx", base + localBot[worker_id] * 8, 8, old + 0x2));
            localBot[worker_id] = (localBot[worker_id] + 1) & (TASKQUEUE_SIZE - 1);
          }

          uintptr_t low = obj_ptr + ArrayElementOff;
          uintptr_t high = obj_ptr + ArrayElementOff + step_index * OopSize;
          uintptr_t p = obj_ptr + ArrayElementOff;
          uintptr_t q = p + array_length * OopSize;
          if (p < low)
            p = low;
          if (q > high)
            q = high;
          while (p < q)
          {
            //((G1ScanEvacuatedObjClosure *)((uintptr_t)pss + OBJCLOSURE_OFFSET))->do_oop((oop *)p);
            do_oop_work(p - obj_ptr + old, p, scanning_in_young, pss, worker_id);
            p += OopSize;
          }
        }
        return obj_ptr;
      }
      // oop_trace
      int vtable_len = *(int *)(klass_ptr + 160);
      int itable_len = *(int *)(klass_ptr + 300);
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %x", klass_ptr + 160, 4, vtable_len));
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %x", klass_ptr + 300, 4, itable_len));

      int nonStaticOopMapSize = *(int *)(klass_ptr + 296);
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %x", klass_ptr + 296, 4, nonStaticOopMapSize));

      uintptr_t start_map = (uintptr_t)((uintptr_t *)(klass_ptr + 464) + vtable_len + itable_len);
      uintptr_t end_map = start_map + nonStaticOopMapSize * 8;
      while (start_map < end_map)
      {
        end_map -= 8;
        int offset = *(int *)(end_map);
        int count = *(int *)(end_map + 0x4);
        IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", end_map, 8, *(uintptr_t *)end_map));

        uintptr_t start = obj_ptr + offset;
        uintptr_t end = start + count * OopSize;
        while (start < end)
        {
          end -= OopSize;
          //((G1ScanEvacuatedObjClosure *)((uintptr_t)pss + 0x180))->do_oop((oop *)end);
          do_oop_work(end - obj_ptr + old, end, scanning_in_young, pss, worker_id);
        }
      }
      if (kid == InstanceMirrorKlassID)
      {
        uintptr_t static_start = obj_ptr + InstanceMirrorKlass::offset_of_static_fields();
        uint staticCount = *(uint *)(old + java_lang_Class::get_static_oop_field_count_offset());
        IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %x", old + 40, 4, staticCount));

        uintptr_t static_end = static_start + staticCount * OopSize;

        while (static_start < static_end)
        {
          do_oop_work(static_start - obj_ptr + old, static_start, scanning_in_young, pss, worker_id);
          static_start += OopSize;
        }
      }
      else if (kid == InstanceRefKlassID)
      {
        uint discovered_offset;
        uint referent_offset;
        if (UseCompressedClassPointers & UseCompressedOops)
        {
          discovered_offset = 0x18;
          referent_offset = 0xc;
        }
        else if (UseCompressedClassPointers)
        {
          discovered_offset = 0x1c;
          referent_offset = 0x10;
        }
        else
        {
          discovered_offset = 0x28;
          referent_offset = 0x10;
        }
        do_oop_work(old + discovered_offset, obj_ptr + discovered_offset, scanning_in_young, pss, worker_id);
        do_oop_work(old + referent_offset, obj_ptr + referent_offset, scanning_in_young, pss, worker_id);
        do_oop_work(old + discovered_offset, obj_ptr + discovered_offset, scanning_in_young, pss, worker_id);
      }
      // if (UseCompressedOops)
      //   ((InstanceKlass *)klass_ptr)->oop_oop_iterate_reverse<narrowOop>((oop)obj_ptr, scanner);
      // else
      //   ((InstanceKlass *)klass_ptr)->oop_oop_iterate_reverse<oop>((oop)obj_ptr, scanner);
      // if (kid == InstanceMirrorKlassID)
      //{
      //   if (UseCompressedOops)
      //     ((InstanceMirrorKlass *)klass_ptr)->oop_oop_iterate_statics<narrowOop>((oop)obj_ptr, scanner);
      //   else
      //     ((InstanceMirrorKlass *)klass_ptr)->oop_oop_iterate_statics<oop>((oop)obj_ptr, scanner);
      // }
      // if (kid == InstanceRefKlassID)
      //{
      //  AlwaysContains always_c;
      //  if (UseCompressedOops)
      //    ((InstanceRefKlass *)klass_ptr)->oop_oop_iterate_ref_processing<narrowOop>((oop)obj_ptr, scanner, always_c);
      //  else
      //    ((InstanceRefKlass *)klass_ptr)->oop_oop_iterate_ref_processing<oop>((oop)obj_ptr, scanner, always_c);
      //}
      return obj_ptr;
    }
    else
    {
      uintptr_t region_bottom = *(uintptr_t *)(plab_buffer_ptr_cache[worker_id][idx] + 0x28);
      uintptr_t region_hard_end = *(uintptr_t *)(plab_buffer_ptr_cache[worker_id][idx] + 0x40);
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", plab_buffer_ptr_cache[worker_id][idx] + 0x28, 8, region_bottom));
      IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to get %lx", plab_buffer_ptr_cache[worker_id][idx] + 0x40, 8, region_hard_end));
      if (obj_ptr >= region_bottom && obj_ptr < region_hard_end)
      {
        int other = idx == 1 ? 0 : 1;
        if (plab_top_end_valid[worker_id][idx])
          plab_top_cache[worker_id][idx] = obj_ptr;
        if (plab_top_end_valid[worker_id][other] && plab_buffer_ptr_cache[worker_id][0] == plab_buffer_ptr_cache[worker_id][1])
          plab_top_cache[worker_id][other] = obj_ptr;
        *(uintptr_t *)(plab_buffer_ptr_cache[worker_id][idx] + 0x30) = obj_ptr;
        IFDEF(TRACE, tty->print_cr("do_copy2survivor: access %lx (%d bytes) to write %lx", plab_buffer_ptr_cache[worker_id][idx] + 0x30, 8, obj_ptr));
      }
      else
      {
        // @todo: deletable?
        tty->print_cr("not in region");

        // Universe::heap()->fill_with_dummy_object((HeapWord *)obj_ptr, (HeapWord *)obj_ptr + size, true);
        size_t words = size / 8;
        uintptr_t cur_klass = 0;
        if (words >= (UseCompressedClassPointers ? 2 : 3))
        {
          size_t payload_size = words - (UseCompressedClassPointers ? 2 : 3);
          size_t len = payload_size * 2;
          *(int *)(obj_ptr + ArrayLenOff) = len;
          IFDEF(TRACE, tty->print_cr("allocate_direct: access %lx (%x bytes) to write %lx", obj_ptr + ArrayLenOff, 4, len));

          cur_klass = (uintptr_t)Universe::intArrayKlassObj();
        }
        else if (words > 0)
          cur_klass = (uintptr_t)vmClasses::Object_klass();
        *(uintptr_t *)obj_ptr = 0x1;
        IFDEF(TRACE, tty->print_cr("allocate_direct: access %lx (%x bytes) to write %x", obj_ptr, 8, 0x1));

        if (UseCompressedClassPointers)
        {
          *(uint *)(obj_ptr + 0x8) = (cur_klass - (uintptr_t)CompressedKlassPointers::base()) >> CompressedKlassPointers::shift();
          IFDEF(TRACE, tty->print_cr("allocate_direct: access %lx (%x bytes) to write %x", obj_ptr + 0x8, 4, (uint)(cur_klass - (uintptr_t)CompressedKlassPointers::base()) >> CompressedKlassPointers::shift()));
        }
        else
        {
          *(uintptr_t *)(obj_ptr + 0x8) = cur_klass;
          IFDEF(TRACE, tty->print_cr("allocate_direct: access %lx (%x bytes) to write %lx", obj_ptr + 0x8, 8, cur_klass));
        }
      }
      return forward_ptr;
    }
  }

  void do_oop_evac(uintptr_t src, G1ParScanThreadState *pss, uint worker_id)
  {
    uintptr_t obj;
    uintptr_t offset = *(uintptr_t *)src;
    IFDEF(TRACE, tty->print_cr("do_oop_evac: access %lx (%d bytes) to get %lx", src, 8, offset));

    if (UseCompressedOops)
    {
      offset = (uint32_t)offset;
      obj = (uintptr_t)CompressedOops::base() + ((uintptr_t)offset << CompressedOops::shift());
      IFDEF(TRACE, tty->print_cr("do_oop_evac: caculate compressed oop obj %lx %lx %x to get %lx", (uintptr_t)CompressedOops::base(), (uintptr_t)offset, CompressedOops::shift(), obj));
    }
    else
      obj = offset;

    uintptr_t regionAttrBiasedBase = pss->getRegionAttrBiasedBase();
    uint regionAttrShiftBy = pss->getRegionAttrShiftBy();

    // 1. get region_attr_ptr
    uintptr_t region_attr_ptr = regionAttrBiasedBase + (obj >> regionAttrShiftBy) * 2;
    if (region_attr_ptr != src_region_ptr_cache[worker_id])
    {
      src_region_ptr_cache[worker_id] = region_attr_ptr;
      src_region_attr_cache[worker_id] = *(u_int16_t *)region_attr_ptr;
      IFDEF(TRACE, tty->print_cr("do_oop_evac: access %lx (%d bytes) to get %x", region_attr_ptr, 2, src_region_attr_cache[worker_id]))
    }
    if ((int8_t)(src_region_attr_cache[worker_id] >> 8) < 0)
      return;

    uintptr_t m_value = *(uintptr_t *)obj;
    IFDEF(TRACE, tty->print_cr("do_oop_evac: access %lx (%d bytes) to get %lx", obj, 8, m_value));

    // m.is_marked
    if ((m_value & 0x3) == 0x3)
    {
      uintptr_t clear_lock_bits = m_value & ~0x3;
      obj = clear_lock_bits;
    }
    else
      // obj = (uintptr_t)pss->copy_to_survivor_space(*(G1HeapRegionAttr *)region_attr_ptr,  (oop)obj, markWord(m_value));
      obj = do_copy_to_survivor_space(region_attr_ptr, src_region_attr_cache[worker_id], obj, m_value, pss, worker_id);

    uint src_shift = src >> pss->getHeapRegionShiftBy();
    if (src_shift != heap_oop_shift_cache2[worker_id])
    {
      heap_oop_shift_cache2[worker_id] = src_shift;
      uintptr_t heap_region = *(uintptr_t *)(pss->getHeapRegionBiasedBase() + (src >> pss->getHeapRegionShiftBy()) * 8);
      IFDEF(TRACE, tty->print_cr("do_oop_evac: access %lx (%d bytes) to get %lx", pss->getHeapRegionBiasedBase() + (src >> pss->getHeapRegionShiftBy()) * 8, 8, heap_region));
      heap_type_is_young2[worker_id] = (*(uint *)(heap_region + 0xbc) & 0x2) != 0;
      IFDEF(TRACE, tty->print_cr("do_oop_evac: access %lx (%d bytes) to get %x", heap_region + 0xbc, 4, *(uint *)(heap_region + 0xbc)));
    }

    if (UseCompressedOops)
    {
      uintptr_t writeObj = (obj - (uintptr_t)CompressedOops::base()) >> CompressedOops::shift();
      *(uint32_t *)src = writeObj;
      IFDEF(TRACE, tty->print_cr("do_oop_evac: access %lx (%d bytes) to write %lx", src, 4, writeObj));
    }
    else
    {
      *(uintptr_t *)src = obj;
      IFDEF(TRACE, tty->print_cr("do_oop_evac: access %lx (%d bytes) to write %lx", src, 8, obj));
    }

    if (((src ^ obj) >> HeapRegion::LogOfHRGrainBytes) == 0)
      return;

    if (!heap_type_is_young2[worker_id])
    {
      region_attr_ptr = regionAttrBiasedBase + (obj >> regionAttrShiftBy) * 2;
      aop_work_enqueue_card(region_attr_ptr, src, pss, worker_id);
    }
  }

  void do_partial_array(uintptr_t src, G1ParScanThreadState *pss, uint worker_id)
  {
    uintptr_t from_obj = src;
    uintptr_t m_value = *(uintptr_t *)from_obj;
    IFDEF(TRACE, tty->print_cr("partial_array: access %lx (%d bytes) to get %lx", from_obj, 8, m_value));

    uintptr_t clear_lock_bits = m_value & ~0x3;
    uintptr_t to_obj = clear_lock_bits;

    int array_length = *(int *)(from_obj + ArrayLenOff);
    IFDEF(TRACE, tty->print_cr("partial_array: access %lx (%d bytes) to get %x", from_obj + ArrayLenOff, 4, array_length));

    int chunk_size = *(int *)((uintptr_t)pss + 0x1ec);
    IFDEF(TRACE, tty->print_cr("partial_array: access %lx (%d bytes) to get %x", (uintptr_t)pss + 0x1ec, 4, chunk_size));

    uint start = *(int *)(to_obj + ArrayLenOff);
    IFDEF(TRACE, tty->print_cr("partial_array: access %lx (%d bytes) to get %x", to_obj + ArrayLenOff, 4, start));
    *(int *)(to_obj + ArrayLenOff) = start + chunk_size;
    IFDEF(TRACE, tty->print_cr("partial_array: access %lx (%d bytes) to write %x", to_obj + ArrayLenOff, 4, start + chunk_size));

    uint task_num = start / chunk_size;
    uint remaining_tasks = (array_length - start) / chunk_size;
    uint _task_limit = *(uint *)((uintptr_t)pss + 0x1f0);
    uint _task_fanout = *(uint *)((uintptr_t)pss + 0x1f0 + 0x4);
    IFDEF(TRACE, tty->print_cr("partial_array: access %lx (%d bytes) to get %x", (uintptr_t)pss + 0x1f0, 4, _task_limit));
    IFDEF(TRACE, tty->print_cr("partial_array: access %lx (%d bytes) to get %x", (uintptr_t)pss + 0x1f0 + 0x4, 4, _task_fanout));
    uint max_pending = (_task_fanout - 1) * task_num + 1;
    uint pending = MIN3(max_pending, remaining_tasks, _task_limit);
    uint ncreate = MIN2(_task_fanout, MIN2(remaining_tasks, _task_limit + 1) - pending);

    for (uint i = 0; i < ncreate; ++i)
    {
      uintptr_t elems = pss->getTaskQueueElemsBase();
      *(uintptr_t *)(elems + localBot[worker_id] * 8) = from_obj + 0x2;
      IFDEF(TRACE, tty->print_cr("partial_array: access %lx (%d bytes) to write %lx", elems + localBot[worker_id] * 8, 8, from_obj + 0x2));
      localBot[worker_id] = localBot[worker_id] + 1;
    }

    uint to_oop_shift = to_obj >> pss->getHeapRegionShiftBy();
    if (heap_oop_shift_cache[worker_id] != to_oop_shift)
    {
      heap_oop_shift_cache[worker_id] = to_oop_shift;
      uintptr_t heap_region = *(uintptr_t *)(pss->getHeapRegionBiasedBase() + to_oop_shift * 8);
      IFDEF(TRACE, tty->print_cr("partial_array: access %lx (%d bytes) to get %lx", pss->getHeapRegionBiasedBase() + to_oop_shift * 8, 8, heap_region));
      heap_type_is_young[worker_id] = (*(uint *)(heap_region + 0xbc) & 0x2) != 0;
      IFDEF(TRACE, tty->print_cr("partial_array: access %lx (%d bytes) to get %x", heap_region + 0xbc, 4, *(uint *)(heap_region + 0xbc)));
    }

    uintptr_t scanning_in_young = heap_type_is_young[worker_id];

    uintptr_t low = to_obj + ArrayElementOff + start * OopSize;
    uintptr_t high = to_obj + ArrayElementOff + (start + chunk_size) * OopSize;
    uintptr_t p = to_obj + ArrayElementOff;
    uintptr_t q = p + (start + chunk_size) * OopSize;
    if (p < low)
      p = low;
    if (q > high)
      q = high;
    while (p < q)
    {
      do_oop_work(p - to_obj + from_obj, p, scanning_in_young, pss, worker_id);
      p += OopSize;
    }
  }

  void dispatch_task(uintptr_t task, G1ParScanThreadState *pss, uint worker_id)
  {
    if ((task & 0x3) != 0x2)
      do_oop_evac(task - (task & 0x3), pss, worker_id);
    else
      do_partial_array(task - 0x2, pss, worker_id);
  }

  void work(uint worker_id)
  {
    start_work(worker_id);

    {
      G1ParScanThreadState *pss = _per_thread_states->state_for_worker(worker_id);
      pss->set_ref_discoverer(_g1h->ref_processor_stw());
      scan_roots(pss, worker_id);

      // @notice: 可以插在这里进行HWGC工作 也就是evacuate_live_objects的功能卸载到硬件去做
      // 取任务需要的参数
      uintptr_t elems = pss->getTaskQueueElemsBase();
      uintptr_t bottom_addr = pss->getTaskQueueBottomAddr();
      uintptr_t age_top_addr = pss->getTaskQueueAgeTopAddr();
      localBot[worker_id] = *(uint *)(bottom_addr);
      tty->print_cr("thread %d, localBot is %d pss %lx", worker_id, localBot[worker_id], (uintptr_t)pss);
      uint oop_size_offset = java_lang_Class::get_oop_size_offset();                   // 0x20
      uint static_count_offset = java_lang_Class::get_static_oop_field_count_offset(); // 0x24
      IFDEF(TRACE, tty->print_cr("oop_size_offset %x, static coutn offset %x", oop_size_offset, static_count_offset));
      IFDEF(TRACE, tty->print_cr("ref offset %x %x %x", java_lang_ref_Reference::discovered_offset(), java_lang_ref_Reference::referent_offset(), InstanceMirrorKlass::offset_of_static_fields()));
      tty->print_cr("oop_size_offset %x, static coutn offset %x", oop_size_offset, static_count_offset);
      tty->print_cr("ref offset %x %x %x", java_lang_ref_Reference::discovered_offset(), java_lang_ref_Reference::referent_offset(), InstanceMirrorKlass::offset_of_static_fields());

      // @notice: print task
      if (TRACE)
      {
        uint localBot = *(uint *)(bottom_addr);
        uint ageTop = *(uint *)(age_top_addr);
        tty->print_cr("work: access %lx (%x bytes) to get %x", bottom_addr, 4, *(uint *)(bottom_addr));
        tty->print_cr("work: access %lx (%x bytes) to get %x", age_top_addr, 4, *(uint *)(age_top_addr));
        for (int i = localBot - 1; i >= 0; --i)
          tty->print_cr("work: access %lx (%x bytes) to get %lx", elems + i * 8, 8, *(uintptr_t *)(elems + i * 8));
      }

      // int fd = open("/dev/hwgc", O_RDWR);
      struct HWGCParameter
      {
        uint32_t chunkSize;
        uint32_t ageThreshold;
        uint32_t heapRegionBias;
        uint32_t regionAttrShiftBy;
        uint32_t heapRegionShiftBy;
        uint32_t logOfHRGrainBytes;
        uint64_t stepperOffset;
        uint64_t youngWordsBase;
        uint64_t regionAttrBase;
        uint64_t plabAllocatorPtr;
        uint64_t regionAttrBiasedBase;
        uint64_t heapRegionBiasedBase;
        uint64_t parScanThreadStatePtr;
        uint64_t taskQueueBottomAddr;
        uint64_t taskQueueElemsBase;
        uint64_t humogousReclaimCandidateBoolBase;
        uint64_t cardTablePtr;
        uint64_t g1h;
        uint64_t intArrayKlass;
        uint64_t objectKlass;
        uint64_t lockPtr;
        uint64_t thread;
        uint64_t dummyRegion;
        uint64_t numaPtr;
        uint64_t compressedOopBase;
        uint64_t compressedKlassPointerBase;
        uint8_t compressedOopShift;
        uint8_t compressedKlassPointerShift;
        uint8_t useCompressedOops;
        uint8_t useCompressedKlassPointers;
      };
      // enum hwgc_state
      //{
      //   HWGC_IDLE,
      //   HWGC_RUNNING,
      //   HWGC_WAIT_MALLOC,
      //   HWGC_WAIT_ENQUEUED,
      //   HWGC_WAIT_PAGEFAULT,
      //   HWGC_DEBUG,
      //   HWGC_DONE
      // };
      // #define HWGC_IOC_MAGIC 'H'
      // #define HWGC_IOC_START _IOW(HWGC_IOC_MAGIC, 0, struct HWGCParameter)
      // #define HWGC_IOC_WAIT_EVENT _IOR(HWGC_IOC_MAGIC, 1, int)
      // #define HWGC_IOC_SOFT_PROVIDE _IOW(HWGC_IOC_MAGIC, 2, uint64_t)
      // #define HWGC_IOC_DEBUG_WRITE _IOW(HWGC_IOC_MAGIC, 3, uint64_t)
      struct HWGCParameter par = {0};
      //  int state;
      par.chunkSize = *(int *)((uintptr_t)pss + 0x1ec);
      par.ageThreshold = *(uint *)((uintptr_t)pss + 0x17c);
      par.heapRegionBias = pss->getHeapRegionBias();
      par.regionAttrShiftBy = pss->getRegionAttrShiftBy();
      par.heapRegionShiftBy = pss->getHeapRegionShiftBy();
      par.logOfHRGrainBytes = HeapRegion::LogOfHRGrainBytes;
      par.stepperOffset = *(uint64_t *)((uintptr_t)pss + 0x1f0);
      par.youngWordsBase = *(uintptr_t *)((uintptr_t)pss + 0x1d0);
      par.regionAttrBase = pss->getRegionAttrBase();
      par.plabAllocatorPtr = *(uintptr_t *)((uintptr_t)pss + 0x70);
      par.regionAttrBiasedBase = pss->getRegionAttrBiasedBase();
      par.heapRegionBiasedBase = pss->getHeapRegionBiasedBase();
      par.parScanThreadStatePtr = (uintptr_t)pss;
      par.taskQueueBottomAddr = bottom_addr;
      par.taskQueueElemsBase = pss->getTaskQueueElemsBase();
      par.humogousReclaimCandidateBoolBase = _g1h->getHumongousReclaimCandidatesBoolBase();
      par.cardTablePtr = *(uintptr_t *)((uintptr_t)pss + 0x60);
      par.g1h = (uintptr_t)_g1h;
      par.intArrayKlass = (uintptr_t)Universe::intArrayKlassObj();
      par.objectKlass = (uintptr_t)vmClasses::Object_klass();
      par.lockPtr = (uintptr_t)FreeList_lock;
      par.thread = (uintptr_t)Thread::current();
      par.dummyRegion = (uintptr_t)G1AllocRegion::_dummy_region;
      par.numaPtr = (uintptr_t)G1NUMA::numa();
      par.compressedOopBase = (uintptr_t)CompressedOops::base();
      par.compressedKlassPointerBase = (uintptr_t)CompressedKlassPointers::base();
      par.compressedOopShift = CompressedOops::shift();
      par.compressedKlassPointerShift = CompressedKlassPointers::shift();
      par.useCompressedOops = UseCompressedOops;
      par.useCompressedKlassPointers = UseCompressedClassPointers;
      // Ticks start = Ticks::now();

      if (TRACE)
      {
        tty->print_cr("=== Dumping 'par' struct ===");
        tty->print_cr("par.chunkSize = %d", par.chunkSize);
        tty->print_cr("par.ageThreshold = %u", par.ageThreshold);
        tty->print_cr("par.heapRegionBias = %u", par.heapRegionBias);
        tty->print_cr("par.regionAttrShiftBy = %u", par.regionAttrShiftBy);
        tty->print_cr("par.heapRegionShiftBy = %u", par.heapRegionShiftBy);
        tty->print_cr("par.logOfHRGrainBytes = %d", par.logOfHRGrainBytes);
        tty->print_cr("par.stepperOffset = " UINT64_FORMAT, par.stepperOffset);
        tty->print_cr("par.youngWordsBase = " PTR_FORMAT, par.youngWordsBase);
        tty->print_cr("par.regionAttrBase = " PTR_FORMAT, par.regionAttrBase);
        tty->print_cr("par.plabAllocatorPtr = " PTR_FORMAT, par.plabAllocatorPtr);
        tty->print_cr("par.regionAttrBiasedBase = " PTR_FORMAT, par.regionAttrBiasedBase);
        tty->print_cr("par.heapRegionBiasedBase = " PTR_FORMAT, par.heapRegionBiasedBase);
        tty->print_cr("par.parScanThreadStatePtr = " PTR_FORMAT, par.parScanThreadStatePtr);
        tty->print_cr("par.taskQueueBottomAddr = " PTR_FORMAT, par.taskQueueBottomAddr);
        tty->print_cr("par.taskQueueElemsBase = " PTR_FORMAT, par.taskQueueElemsBase);
        tty->print_cr("par.humogousReclaimCandidateBoolBase = " PTR_FORMAT, par.humogousReclaimCandidateBoolBase);
        tty->print_cr("par.cardTablePtr = " PTR_FORMAT, par.cardTablePtr);
        tty->print_cr("par.g1h = " PTR_FORMAT, par.g1h);
        tty->print_cr("par.intArrayKlass = " PTR_FORMAT, par.intArrayKlass);
        tty->print_cr("par.objectKlass = " PTR_FORMAT, par.objectKlass);
        tty->print_cr("par.lockPtr = " PTR_FORMAT, par.lockPtr);
        tty->print_cr("par.thread = " PTR_FORMAT, par.thread);
        tty->print_cr("par.dummyRegion = " PTR_FORMAT, par.dummyRegion);
        tty->print_cr("par.numaPtr = " PTR_FORMAT, par.numaPtr);
        tty->print_cr("par.compressedOopBase = " PTR_FORMAT, par.compressedOopBase);
        tty->print_cr("par.compressedKlassPointerBase = " PTR_FORMAT, par.compressedKlassPointerBase);
        tty->print_cr("par.compressedOopShift = %d", par.compressedOopShift);
        tty->print_cr("par.compressedKlassPointerShift = %d", par.compressedKlassPointerShift);
        tty->print_cr("par.useCompressedOops = %d", par.useCompressedOops);
        tty->print_cr("par.useCompressedKlassPointers = %d", par.useCompressedKlassPointers);
        tty->print_cr("=== End of 'par' dump ===");
      }

      // tty->print_cr("work start");
      //  ioctl(fd, HWGC_IOC_START, &par);
      //  while (1)
      //{
      //    ioctl(fd, HWGC_IOC_WAIT_EVENT, &state);
      //    if (state == HWGC_DONE)
      //    {
      //      Ticks end = Ticks::now();
      //      jlong nanos = (end - start).nanoseconds();
      //      tty->print_cr("work done, time is %ld ns", nanos);
      //      break;
      //    }
      //    if (state == HWGC_WAIT_ENQUEUED)
      //    {
      //      lseek(fd, 0xe0, SEEK_SET);
      //      uint64_t allocator_ptr, buffer = 0;
      //      read(fd, &allocator_ptr, sizeof(allocator_ptr));
      //      buffer = (uintptr_t)BufferNode::allocate(*(size_t *)allocator_ptr);
      //      ioctl(fd, HWGC_IOC_SOFT_PROVIDE, &buffer);
      //    }
      //    if (state == HWGC_WAIT_MALLOC)
      //    {
      //      lseek(fd, 0xe0, SEEK_SET);

      //    uintptr_t grow_array_ptr, len;
      //    read(fd, &grow_array_ptr, 8);
      //    read(fd, &len, 4);
      //    ((GrowableArray<HeapRegion *> *)grow_array_ptr)->grow(len);
      //    ioctl(fd, HWGC_IOC_SOFT_PROVIDE, &len);
      //  }
      //  if (state == HWGC_WAIT_PAGEFAULT)
      //  {
      //    lseek(fd, 0xe0, SEEK_SET);
      //    uintptr_t vaddr, data, write, size;
      //    read(fd, &vaddr, sizeof(vaddr));
      //    read(fd, &data, sizeof(data));
      //    read(fd, &write, sizeof(write));
      //    read(fd, &size, sizeof(size));
      //    if ((vaddr >> 40) != 0 || (vaddr & 0xf000000000ull) != 0xf000000000ull)
      //      tty->print_cr("%lx %lx %lx %lx\n", vaddr, data, write, size);

      //    uint64_t return_value = 0;
      //    if (write)
      //      memcpy((void *)vaddr, &data, size);
      //    else
      //      memcpy(&return_value, (void *)vaddr, size);
      //    ioctl(fd, HWGC_IOC_SOFT_PROVIDE, &return_value);
      //  }
      //  if (state == HWGC_DEBUG)
      //  {
      //    lseek(fd, 0xe0, SEEK_SET);

      //    // uintptr_t dest_attr_type, min_word_size, desired_word_size, allocator_ptr;
      //    // read(fd, &dest_attr_type, 8);
      //    // read(fd, &min_word_size, 8);
      //    // read(fd, &desired_word_size, 8);
      //    // read(fd, &allocator_ptr, 8);
      //    // uintptr_t temp;
      //    // uintptr_t obj = par_allocate_during_gc_debug((int8_t)dest_attr_type, min_word_size, desired_word_size, &temp, 0, allocator_ptr, pss);
      //    // ioctl(fd, HWGC_IOC_DEBUG_WRITE, &temp);
      //    // ioctl(fd, HWGC_IOC_SOFT_PROVIDE, &obj);
      //    // uintptr_t region_ptr, desired_word_size;
      //    // read(fd, &region_ptr, 8);
      //    // read(fd, &desired_word_size, 8);
      //    // uintptr_t temp;
      //    //// uintptr_t obj_ptr = attempt_allocation_using_new_region_debug(region_ptr, desired_word_size, &temp);
      //    //// ioctl(fd, HWGC_IOC_DEBUG_WRITE, &temp);
      //    // uintptr_t obj_ptr = new_gc_alloc_region(region_ptr, desired_word_size);
      //    // ioctl(fd, HWGC_IOC_SOFT_PROVIDE, &obj_ptr);

      //    // uintptr_t desired_word_size, heap_region_type, node_index;
      //    // read(fd, &desired_word_size, 8);
      //    // read(fd, &heap_region_type, 8);
      //    // read(fd, &node_index, 8);
      //    // size_t temp;
      //    // uintptr_t obj_ptr = new_region(desired_word_size, (uint)heap_region_type, (uint)node_index);
      //    // ioctl(fd, HWGC_IOC_SOFT_PROVIDE, &obj_ptr);

      //    uintptr_t node_index;
      //    read(fd, &node_index, 8);
      //    uintptr_t obj_ptr = _g1h->expand_single_region(node_index);
      //    ioctl(fd, HWGC_IOC_SOFT_PROVIDE, &obj_ptr);
      //  }
      //}
      // close(fd);

      bool tag = false; // 决定是否需要分发处理该task
      do
      {
        uintptr_t task;
        if (localBot[worker_id] <= 0)
          tag = false;
        else
        {
          localBot[worker_id] = (localBot[worker_id] - 1) & (TASKQUEUE_SIZE - 1);
          task = *(uintptr_t *)(elems + localBot[worker_id] * 8);
          tag = true;
        }
        if (tag)
          dispatch_task(task, pss, worker_id);
      } while (tag);

      *(uint *)bottom_addr = localBot[worker_id];
      // evacuate_live_objects(pss, worker_id);
      tty->print_cr("thread %d, work done", worker_id);

      if (last_index_valid[worker_id])
        *(size_t *)((uintptr_t)pss + 0x1b0) = last_index_cache[worker_id];
      if (parScan_offset40_valid[worker_id])
      {
        uintptr_t rdc_local_qset_ptr = (uintptr_t)pss->getRdcQueueSetPtr();
        *(size_t *)(rdc_local_qset_ptr + 0x30) = index_cache[worker_id];
        *(uintptr_t *)(rdc_local_qset_ptr + 0x40) = buffer_cache[worker_id];
      }
      if (parScan_offset20_valid[worker_id])
      {
        uintptr_t rdc_local_qset_ptr = (uintptr_t)pss->getRdcQueueSetPtr();
        *(size_t *)(rdc_local_qset_ptr + 0x18) = offset30_cache[worker_id];
        *(uintptr_t *)(rdc_local_qset_ptr + 0x20) = offset38_cache[worker_id];
      }
    }

    end_work(worker_id);
  }
};

class G1EvacuateRegionsTask : public G1EvacuateRegionsBaseTask
{
  G1RootProcessor *_root_processor;
  bool _has_optional_evacuation_work;

  void scan_roots(G1ParScanThreadState *pss, uint worker_id)
  {
    _root_processor->evacuate_roots(pss, worker_id);
    _g1h->rem_set()->scan_heap_roots(pss, worker_id, G1GCPhaseTimes::ScanHR, G1GCPhaseTimes::ObjCopy, _has_optional_evacuation_work);
    _g1h->rem_set()->scan_collection_set_regions(pss, worker_id, G1GCPhaseTimes::ScanHR, G1GCPhaseTimes::CodeRoots, G1GCPhaseTimes::ObjCopy);
  }

  void evacuate_live_objects(G1ParScanThreadState *pss, uint worker_id)
  {
    G1EvacuateRegionsBaseTask::evacuate_live_objects(pss, worker_id, G1GCPhaseTimes::ObjCopy, G1GCPhaseTimes::Termination);
  }

  void start_work(uint worker_id)
  {
    _g1h->phase_times()->record_time_secs(G1GCPhaseTimes::GCWorkerStart, worker_id, Ticks::now().seconds());
  }

  void end_work(uint worker_id)
  {
    _g1h->phase_times()->record_time_secs(G1GCPhaseTimes::GCWorkerEnd, worker_id, Ticks::now().seconds());
  }

public:
  G1EvacuateRegionsTask(G1CollectedHeap *g1h,
                        G1ParScanThreadStateSet *per_thread_states,
                        G1ScannerTasksQueueSet *task_queues,
                        G1RootProcessor *root_processor,
                        uint num_workers,
                        bool has_optional_evacuation_work) : G1EvacuateRegionsBaseTask("G1 Evacuate Regions", per_thread_states, task_queues, num_workers),
                                                             _root_processor(root_processor),
                                                             _has_optional_evacuation_work(has_optional_evacuation_work)
  {
  }
};

void G1CollectedHeap::evacuate_initial_collection_set(G1ParScanThreadStateSet *per_thread_states,
                                                      bool has_optional_evacuation_work)
{
  G1GCPhaseTimes *p = phase_times();

  {
    Ticks start = Ticks::now();
    rem_set()->merge_heap_roots(true /* initial_evacuation */);
    p->record_merge_heap_roots_time((Ticks::now() - start).seconds() * 1000.0);
  }

  Tickspan task_time;
  const uint num_workers = workers()->active_workers();

  Ticks start_processing = Ticks::now();
  {
    G1RootProcessor root_processor(this, num_workers);
    G1EvacuateRegionsTask g1_par_task(this,
                                      per_thread_states,
                                      _task_queues,
                                      &root_processor,
                                      num_workers,
                                      has_optional_evacuation_work);
    task_time = run_task_timed(&g1_par_task);
    // Closing the inner scope will execute the destructor for the G1RootProcessor object.
    // To extract its code root fixup time we measure total time of this scope and
    // subtract from the time the WorkGang task took.
  }
  Tickspan total_processing = Ticks::now() - start_processing;

  p->record_initial_evac_time(task_time.seconds() * 1000.0);
  p->record_or_add_code_root_fixup_time((total_processing - task_time).seconds() * 1000.0);

  rem_set()->complete_evac_phase(has_optional_evacuation_work);
}

class G1EvacuateOptionalRegionsTask : public G1EvacuateRegionsBaseTask
{

  void scan_roots(G1ParScanThreadState *pss, uint worker_id)
  {
    _g1h->rem_set()->scan_heap_roots(pss, worker_id, G1GCPhaseTimes::OptScanHR, G1GCPhaseTimes::OptObjCopy, true /* remember_already_scanned_cards */);
    _g1h->rem_set()->scan_collection_set_regions(pss, worker_id, G1GCPhaseTimes::OptScanHR, G1GCPhaseTimes::OptCodeRoots, G1GCPhaseTimes::OptObjCopy);
  }

  void evacuate_live_objects(G1ParScanThreadState *pss, uint worker_id)
  {
    G1EvacuateRegionsBaseTask::evacuate_live_objects(pss, worker_id, G1GCPhaseTimes::OptObjCopy, G1GCPhaseTimes::OptTermination);
  }

public:
  G1EvacuateOptionalRegionsTask(G1ParScanThreadStateSet *per_thread_states,
                                G1ScannerTasksQueueSet *queues,
                                uint num_workers) : G1EvacuateRegionsBaseTask("G1 Evacuate Optional Regions", per_thread_states, queues, num_workers)
  {
  }
};

void G1CollectedHeap::evacuate_next_optional_regions(G1ParScanThreadStateSet *per_thread_states)
{
  class G1MarkScope : public MarkScope
  {
  };

  Tickspan task_time;

  Ticks start_processing = Ticks::now();
  {
    G1MarkScope code_mark_scope;
    G1EvacuateOptionalRegionsTask task(per_thread_states, _task_queues, workers()->active_workers());
    task_time = run_task_timed(&task);
    // See comment in evacuate_collection_set() for the reason of the scope.
  }
  Tickspan total_processing = Ticks::now() - start_processing;

  G1GCPhaseTimes *p = phase_times();
  p->record_or_add_code_root_fixup_time((total_processing - task_time).seconds() * 1000.0);
}

void G1CollectedHeap::evacuate_optional_collection_set(G1ParScanThreadStateSet *per_thread_states)
{
  const double gc_start_time_ms = phase_times()->cur_collection_start_sec() * 1000.0;

  while (!evacuation_failed() && _collection_set.optional_region_length() > 0)
  {

    double time_used_ms = os::elapsedTime() * 1000.0 - gc_start_time_ms;
    double time_left_ms = MaxGCPauseMillis - time_used_ms;

    if (time_left_ms < 0 ||
        !_collection_set.finalize_optional_for_evacuation(time_left_ms * policy()->optional_evacuation_fraction()))
    {
      log_trace(gc, ergo, cset)("Skipping evacuation of %u optional regions, no more regions can be evacuated in %.3fms",
                                _collection_set.optional_region_length(), time_left_ms);
      break;
    }

    {
      Ticks start = Ticks::now();
      rem_set()->merge_heap_roots(false /* initial_evacuation */);
      phase_times()->record_or_add_optional_merge_heap_roots_time((Ticks::now() - start).seconds() * 1000.0);
    }

    {
      Ticks start = Ticks::now();
      evacuate_next_optional_regions(per_thread_states);
      phase_times()->record_or_add_optional_evac_time((Ticks::now() - start).seconds() * 1000.0);
    }

    rem_set()->complete_evac_phase(true /* has_more_than_one_evacuation_phase */);
  }

  _collection_set.abandon_optional_collection_set(per_thread_states);
}

void G1CollectedHeap::post_evacuate_collection_set(G1EvacuationInfo *evacuation_info,
                                                   G1RedirtyCardsQueueSet *rdcqs,
                                                   G1ParScanThreadStateSet *per_thread_states)
{
  G1GCPhaseTimes *p = phase_times();

  // Process any discovered reference objects - we have
  // to do this _before_ we retire the GC alloc regions
  // as we may have to copy some 'reachable' referent
  // objects (and their reachable sub-graphs) that were
  // not copied during the pause.
  process_discovered_references(per_thread_states);

  G1STWIsAliveClosure is_alive(this);
  G1KeepAliveClosure keep_alive(this);

  WeakProcessor::weak_oops_do(workers(), &is_alive, &keep_alive, p->weak_phase_times());

  _allocator->release_gc_alloc_regions(evacuation_info);

  post_evacuate_cleanup_1(per_thread_states, rdcqs);

  post_evacuate_cleanup_2(&_preserved_marks_set, rdcqs, evacuation_info, per_thread_states->surviving_young_words());

  assert_used_and_recalculate_used_equal(this);

  rebuild_free_region_list();

  record_obj_copy_mem_stats();

  evacuation_info->set_collectionset_used_before(collection_set()->bytes_used_before());
  evacuation_info->set_bytes_used(_bytes_used_during_gc);
}

void G1CollectedHeap::record_obj_copy_mem_stats()
{
  policy()->old_gen_alloc_tracker()->add_allocated_bytes_since_last_gc(_old_evac_stats.allocated() * HeapWordSize);

  _gc_tracer_stw->report_evacuation_statistics(create_g1_evac_summary(&_survivor_evac_stats),
                                               create_g1_evac_summary(&_old_evac_stats));
}

void G1CollectedHeap::free_region(HeapRegion *hr, FreeRegionList *free_list)
{
  assert(!hr->is_free(), "the region should not be free");
  assert(!hr->is_empty(), "the region should not be empty");
  assert(_hrm.is_available(hr->hrm_index()), "region should be committed");

  if (G1VerifyBitmaps)
  {
    MemRegion mr(hr->bottom(), hr->end());
    concurrent_mark()->clear_range_in_prev_bitmap(mr);
  }

  // Clear the card counts for this region.
  // Note: we only need to do this if the region is not young
  // (since we don't refine cards in young regions).
  if (!hr->is_young())
  {
    _hot_card_cache->reset_card_counts(hr);
  }

  // Reset region metadata to allow reuse.
  hr->hr_clear(true /* clear_space */);
  _policy->remset_tracker()->update_at_free(hr);

  if (free_list != NULL)
  {
    free_list->add_ordered(hr);
  }
}

void G1CollectedHeap::free_humongous_region(HeapRegion *hr,
                                            FreeRegionList *free_list)
{
  assert(hr->is_humongous(), "this is only for humongous regions");
  hr->clear_humongous();
  free_region(hr, free_list);
}

void G1CollectedHeap::remove_from_old_gen_sets(const uint old_regions_removed,
                                               const uint archive_regions_removed,
                                               const uint humongous_regions_removed)
{
  if (old_regions_removed > 0 || archive_regions_removed > 0 || humongous_regions_removed > 0)
  {
    MutexLocker x(OldSets_lock, Mutex::_no_safepoint_check_flag);
    _old_set.bulk_remove(old_regions_removed);
    _archive_set.bulk_remove(archive_regions_removed);
    _humongous_set.bulk_remove(humongous_regions_removed);
  }
}

void G1CollectedHeap::prepend_to_freelist(FreeRegionList *list)
{
  assert(list != NULL, "list can't be null");
  if (!list->is_empty())
  {
    MutexLocker x(FreeList_lock, Mutex::_no_safepoint_check_flag);
    _hrm.insert_list_into_free_list(list);
  }
}

void G1CollectedHeap::decrement_summary_bytes(size_t bytes)
{
  decrease_used(bytes);
}

void G1CollectedHeap::post_evacuate_cleanup_1(G1ParScanThreadStateSet *per_thread_states,
                                              G1RedirtyCardsQueueSet *rdcqs)
{
  Ticks start = Ticks::now();
  {
    G1PostEvacuateCollectionSetCleanupTask1 cl(per_thread_states, rdcqs);
    run_batch_task(&cl);
  }
  phase_times()->record_post_evacuate_cleanup_task_1_time((Ticks::now() - start).seconds() * 1000.0);
}

void G1CollectedHeap::post_evacuate_cleanup_2(PreservedMarksSet *preserved_marks,
                                              G1RedirtyCardsQueueSet *rdcqs,
                                              G1EvacuationInfo *evacuation_info,
                                              const size_t *surviving_young_words)
{
  Ticks start = Ticks::now();
  {
    G1PostEvacuateCollectionSetCleanupTask2 cl(preserved_marks, rdcqs, evacuation_info, surviving_young_words);
    run_batch_task(&cl);
  }
  phase_times()->record_post_evacuate_cleanup_task_2_time((Ticks::now() - start).seconds() * 1000.0);
}

void G1CollectedHeap::clear_eden()
{
  _eden.clear();
}

void G1CollectedHeap::clear_collection_set()
{
  collection_set()->clear();
}

void G1CollectedHeap::rebuild_free_region_list()
{
  Ticks start = Ticks::now();
  _hrm.rebuild_free_list(workers());
  phase_times()->record_total_rebuild_freelist_time_ms((Ticks::now() - start).seconds() * 1000.0);
}

class G1AbandonCollectionSetClosure : public HeapRegionClosure
{
public:
  virtual bool do_heap_region(HeapRegion *r)
  {
    assert(r->in_collection_set(), "Region %u must have been in collection set", r->hrm_index());
    G1CollectedHeap::heap()->clear_region_attr(r);
    r->clear_young_index_in_cset();
    return false;
  }
};

void G1CollectedHeap::abandon_collection_set(G1CollectionSet *collection_set)
{
  G1AbandonCollectionSetClosure cl;
  collection_set_iterate_all(&cl);

  collection_set->clear();
  collection_set->stop_incremental_building();
}

bool G1CollectedHeap::is_old_gc_alloc_region(HeapRegion *hr)
{
  return _allocator->is_retained_old_region(hr);
}

void G1CollectedHeap::set_region_short_lived_locked(HeapRegion *hr)
{
  _eden.add(hr);
  _policy->set_region_eden(hr);
}

#ifdef ASSERT

class NoYoungRegionsClosure : public HeapRegionClosure
{
private:
  bool _success;

public:
  NoYoungRegionsClosure() : _success(true) {}
  bool do_heap_region(HeapRegion *r)
  {
    if (r->is_young())
    {
      log_error(gc, verify)("Region [" PTR_FORMAT ", " PTR_FORMAT ") tagged as young",
                            p2i(r->bottom()), p2i(r->end()));
      _success = false;
    }
    return false;
  }
  bool success() { return _success; }
};

bool G1CollectedHeap::check_young_list_empty()
{
  bool ret = (young_regions_count() == 0);

  NoYoungRegionsClosure closure;
  heap_region_iterate(&closure);
  ret = ret && closure.success();

  return ret;
}

#endif // ASSERT

// Remove the given HeapRegion from the appropriate region set.
void G1CollectedHeap::prepare_region_for_full_compaction(HeapRegion *hr)
{
  if (hr->is_archive())
  {
    _archive_set.remove(hr);
  }
  else if (hr->is_humongous())
  {
    _humongous_set.remove(hr);
  }
  else if (hr->is_old())
  {
    _old_set.remove(hr);
  }
  else if (hr->is_young())
  {
    // Note that emptying the eden and survivor lists is postponed and instead
    // done as the first step when rebuilding the regions sets again. The reason
    // for this is that during a full GC string deduplication needs to know if
    // a collected region was young or old when the full GC was initiated.
    hr->uninstall_surv_rate_group();
  }
  else
  {
    // We ignore free regions, we'll empty the free list afterwards.
    assert(hr->is_free(), "it cannot be another type");
  }
}

void G1CollectedHeap::increase_used(size_t bytes)
{
  _summary_bytes_used += bytes;
}

void G1CollectedHeap::decrease_used(size_t bytes)
{
  assert(_summary_bytes_used >= bytes,
         "invariant: _summary_bytes_used: " SIZE_FORMAT " should be >= bytes: " SIZE_FORMAT,
         _summary_bytes_used, bytes);
  _summary_bytes_used -= bytes;
}

void G1CollectedHeap::set_used(size_t bytes)
{
  _summary_bytes_used = bytes;
}

class RebuildRegionSetsClosure : public HeapRegionClosure
{
private:
  bool _free_list_only;

  HeapRegionSet *_old_set;
  HeapRegionSet *_archive_set;
  HeapRegionSet *_humongous_set;

  HeapRegionManager *_hrm;

  size_t _total_used;

public:
  RebuildRegionSetsClosure(bool free_list_only,
                           HeapRegionSet *old_set,
                           HeapRegionSet *archive_set,
                           HeapRegionSet *humongous_set,
                           HeapRegionManager *hrm) : _free_list_only(free_list_only), _old_set(old_set), _archive_set(archive_set),
                                                     _humongous_set(humongous_set), _hrm(hrm), _total_used(0)
  {
    assert(_hrm->num_free_regions() == 0, "pre-condition");
    if (!free_list_only)
    {
      assert(_old_set->is_empty(), "pre-condition");
      assert(_archive_set->is_empty(), "pre-condition");
      assert(_humongous_set->is_empty(), "pre-condition");
    }
  }

  bool do_heap_region(HeapRegion *r)
  {
    if (r->is_empty())
    {
      assert(r->rem_set()->is_empty(), "Empty regions should have empty remembered sets.");
      // Add free regions to the free list
      r->set_free();
      _hrm->insert_into_free_list(r);
    }
    else if (!_free_list_only)
    {
      assert(r->rem_set()->is_empty(), "At this point remembered sets must have been cleared.");

      if (r->is_humongous())
      {
        _humongous_set->add(r);
      }
      else if (r->is_archive())
      {
        _archive_set->add(r);
      }
      else
      {
        assert(r->is_young() || r->is_free() || r->is_old(), "invariant");
        // We now move all (non-humongous, non-old, non-archive) regions to old gen,
        // and register them as such.
        r->move_to_old();
        _old_set->add(r);
      }
      _total_used += r->used();
    }

    return false;
  }

  size_t total_used()
  {
    return _total_used;
  }
};

void G1CollectedHeap::rebuild_region_sets(bool free_list_only)
{
  assert_at_safepoint_on_vm_thread();

  if (!free_list_only)
  {
    _eden.clear();
    _survivor.clear();
  }

  RebuildRegionSetsClosure cl(free_list_only,
                              &_old_set, &_archive_set, &_humongous_set,
                              &_hrm);
  heap_region_iterate(&cl);

  if (!free_list_only)
  {
    set_used(cl.total_used());
    if (_archive_allocator != NULL)
    {
      _archive_allocator->clear_used();
    }
  }
  assert_used_and_recalculate_used_equal(this);
}

// Methods for the mutator alloc region

HeapRegion *G1CollectedHeap::new_mutator_alloc_region(size_t word_size,
                                                      bool force,
                                                      uint node_index)
{
  assert_heap_locked_or_at_safepoint(true /* should_be_vm_thread */);
  bool should_allocate = policy()->should_allocate_mutator_region();
  if (force || should_allocate)
  {
    HeapRegion *new_alloc_region = new_region(word_size,
                                              HeapRegionType::Eden,
                                              false /* do_expand */,
                                              node_index);
    if (new_alloc_region != NULL)
    {
      set_region_short_lived_locked(new_alloc_region);
      _hr_printer.alloc(new_alloc_region, !should_allocate);
      _verifier->check_bitmaps("Mutator Region Allocation", new_alloc_region);
      _policy->remset_tracker()->update_at_allocate(new_alloc_region);
      return new_alloc_region;
    }
  }
  return NULL;
}

void G1CollectedHeap::retire_mutator_alloc_region(HeapRegion *alloc_region,
                                                  size_t allocated_bytes)
{
  assert_heap_locked_or_at_safepoint(true /* should_be_vm_thread */);
  assert(alloc_region->is_eden(), "all mutator alloc regions should be eden");

  collection_set()->add_eden_region(alloc_region);
  increase_used(allocated_bytes);
  _eden.add_used_bytes(allocated_bytes);
  _hr_printer.retire(alloc_region);

  // We update the eden sizes here, when the region is retired,
  // instead of when it's allocated, since this is the point that its
  // used space has been recorded in _summary_bytes_used.
  g1mm()->update_eden_size();
}

// Methods for the GC alloc regions

bool G1CollectedHeap::has_more_regions(G1HeapRegionAttr dest)
{
  if (dest.is_old())
  {
    return true;
  }
  else
  {
    return survivor_regions_count() < policy()->max_survivor_regions();
  }
}

HeapRegion *G1CollectedHeap::new_gc_alloc_region(size_t word_size, G1HeapRegionAttr dest, uint node_index)
{
  assert(FreeList_lock->owned_by_self(), "pre-condition");

  if (!has_more_regions(dest))
  {
    return NULL;
  }

  HeapRegionType type;
  if (dest.is_young())
  {
    type = HeapRegionType::Survivor;
  }
  else
  {
    type = HeapRegionType::Old;
  }

  HeapRegion *new_alloc_region = new_region(word_size,
                                            type,
                                            true /* do_expand */,
                                            node_index);

  if (new_alloc_region != NULL)
  {
    if (type.is_survivor())
    {
      new_alloc_region->set_survivor();
      _survivor.add(new_alloc_region);
      _verifier->check_bitmaps("Survivor Region Allocation", new_alloc_region);
    }
    else
    {
      new_alloc_region->set_old();
      _verifier->check_bitmaps("Old Region Allocation", new_alloc_region);
    }
    _policy->remset_tracker()->update_at_allocate(new_alloc_region);
    register_region_with_region_attr(new_alloc_region);
    _hr_printer.alloc(new_alloc_region);
    return new_alloc_region;
  }
  return NULL;
}

void G1CollectedHeap::retire_gc_alloc_region(HeapRegion *alloc_region,
                                             size_t allocated_bytes,
                                             G1HeapRegionAttr dest)
{
  _bytes_used_during_gc += allocated_bytes;
  if (dest.is_old())
  {
    old_set_add(alloc_region);
  }
  else
  {
    assert(dest.is_young(), "Retiring alloc region should be young (%d)", dest.type());
    _survivor.add_used_bytes(allocated_bytes);
  }

  bool const during_im = collector_state()->in_concurrent_start_gc();
  if (during_im && allocated_bytes > 0)
  {
    _cm->root_regions()->add(alloc_region->next_top_at_mark_start(), alloc_region->top());
  }
  _hr_printer.retire(alloc_region);
}

HeapRegion *G1CollectedHeap::alloc_highest_free_region()
{
  bool expanded = false;
  uint index = _hrm.find_highest_free(&expanded);

  if (index != G1_NO_HRM_INDEX)
  {
    if (expanded)
    {
      log_debug(gc, ergo, heap)("Attempt heap expansion (requested address range outside heap bounds). region size: " SIZE_FORMAT "B",
                                HeapRegion::GrainWords * HeapWordSize);
    }
    return _hrm.allocate_free_regions_starting_at(index, 1);
  }
  return NULL;
}

// Optimized nmethod scanning

class RegisterNMethodOopClosure : public OopClosure
{
  G1CollectedHeap *_g1h;
  nmethod *_nm;

  template <class T>
  void do_oop_work(T *p)
  {
    T heap_oop = RawAccess<>::oop_load(p);
    if (!CompressedOops::is_null(heap_oop))
    {
      oop obj = CompressedOops::decode_not_null(heap_oop);
      HeapRegion *hr = _g1h->heap_region_containing(obj);
      assert(!hr->is_continues_humongous(),
             "trying to add code root " PTR_FORMAT " in continuation of humongous region " HR_FORMAT
             " starting at " HR_FORMAT,
             p2i(_nm), HR_FORMAT_PARAMS(hr), HR_FORMAT_PARAMS(hr->humongous_start_region()));

      // HeapRegion::add_strong_code_root_locked() avoids adding duplicate entries.
      hr->add_strong_code_root_locked(_nm);
    }
  }

public:
  RegisterNMethodOopClosure(G1CollectedHeap *g1h, nmethod *nm) : _g1h(g1h), _nm(nm) {}

  void do_oop(oop *p) { do_oop_work(p); }
  void do_oop(narrowOop *p) { do_oop_work(p); }
};

class UnregisterNMethodOopClosure : public OopClosure
{
  G1CollectedHeap *_g1h;
  nmethod *_nm;

  template <class T>
  void do_oop_work(T *p)
  {
    T heap_oop = RawAccess<>::oop_load(p);
    if (!CompressedOops::is_null(heap_oop))
    {
      oop obj = CompressedOops::decode_not_null(heap_oop);
      HeapRegion *hr = _g1h->heap_region_containing(obj);
      assert(!hr->is_continues_humongous(),
             "trying to remove code root " PTR_FORMAT " in continuation of humongous region " HR_FORMAT
             " starting at " HR_FORMAT,
             p2i(_nm), HR_FORMAT_PARAMS(hr), HR_FORMAT_PARAMS(hr->humongous_start_region()));

      hr->remove_strong_code_root(_nm);
    }
  }

public:
  UnregisterNMethodOopClosure(G1CollectedHeap *g1h, nmethod *nm) : _g1h(g1h), _nm(nm) {}

  void do_oop(oop *p) { do_oop_work(p); }
  void do_oop(narrowOop *p) { do_oop_work(p); }
};

void G1CollectedHeap::register_nmethod(nmethod *nm)
{
  guarantee(nm != NULL, "sanity");
  RegisterNMethodOopClosure reg_cl(this, nm);
  nm->oops_do(&reg_cl);
}

void G1CollectedHeap::unregister_nmethod(nmethod *nm)
{
  guarantee(nm != NULL, "sanity");
  UnregisterNMethodOopClosure reg_cl(this, nm);
  nm->oops_do(&reg_cl, true);
}

void G1CollectedHeap::update_used_after_gc()
{
  if (evacuation_failed())
  {
    // Reset the G1EvacuationFailureALot counters and flags
    NOT_PRODUCT(reset_evacuation_should_fail();)

    set_used(recalculate_used());

    if (_archive_allocator != NULL)
    {
      _archive_allocator->clear_used();
    }
    for (uint i = 0; i < ParallelGCThreads; i++)
    {
      if (_evacuation_failed_info_array[i].has_failed())
      {
        _gc_tracer_stw->report_evacuation_failed(_evacuation_failed_info_array[i]);
      }
    }
  }
  else
  {
    // The "used" of the the collection set have already been subtracted
    // when they were freed.  Add in the bytes used.
    increase_used(_bytes_used_during_gc);
  }
}

void G1CollectedHeap::reset_hot_card_cache()
{
  _hot_card_cache->reset_hot_cache();
  _hot_card_cache->set_use_cache(true);
}

void G1CollectedHeap::purge_code_root_memory()
{
  G1CodeRootSet::purge();
}

class RebuildStrongCodeRootClosure : public CodeBlobClosure
{
  G1CollectedHeap *_g1h;

public:
  RebuildStrongCodeRootClosure(G1CollectedHeap *g1h) : _g1h(g1h) {}

  void do_code_blob(CodeBlob *cb)
  {
    nmethod *nm = (cb != NULL) ? cb->as_nmethod_or_null() : NULL;
    if (nm == NULL)
    {
      return;
    }

    _g1h->register_nmethod(nm);
  }
};

void G1CollectedHeap::rebuild_strong_code_roots()
{
  RebuildStrongCodeRootClosure blob_cl(this);
  CodeCache::blobs_do(&blob_cl);
}

void G1CollectedHeap::initialize_serviceability()
{
  _g1mm->initialize_serviceability();
}

MemoryUsage G1CollectedHeap::memory_usage()
{
  return _g1mm->memory_usage();
}

GrowableArray<GCMemoryManager *> G1CollectedHeap::memory_managers()
{
  return _g1mm->memory_managers();
}

GrowableArray<MemoryPool *> G1CollectedHeap::memory_pools()
{
  return _g1mm->memory_pools();
}
