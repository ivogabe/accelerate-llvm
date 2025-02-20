#include "types.h"
#include <unistd.h>
#include <sched.h>

struct RuntimeLib accelerate_runtime_lib = (struct RuntimeLib){
  .accelerate_buffer_alloc = accelerate_buffer_alloc,
  .accelerate_buffer_release = accelerate_buffer_release,
  .accelerate_buffer_retain = accelerate_buffer_retain,
  .accelerate_ref_release = accelerate_ref_release,
  .accelerate_ref_retain = accelerate_ref_retain,
  .accelerate_ref_write_buffer = accelerate_ref_write_buffer,
  .accelerate_schedule = accelerate_schedule,
  .accelerate_schedule_after = accelerate_schedule_after,
  .accelerate_schedule_after_or = accelerate_schedule_after_or,
  .accelerate_signal_resolve = accelerate_signal_resolve,
  .hs_try_putmvar = hs_try_putmvar
};

static void accelerate_parker_maybe_park(struct ThreadParker *parker) {
  pthread_mutex_lock(&parker->lock);
  atomic_store_explicit(&parker->any_sleeping, 1, memory_order_release);
}
static void accelerate_parker_confirm_park(struct ThreadParker *parker) {
  pthread_cond_wait(&parker->cond_var, &parker->lock);
  // Note that spurious wakes may happen, but that's not a big problem.
  // We'll just check the queue a few times then, and then park again.
  pthread_mutex_unlock(&parker->lock);
}
static void accelerate_parker_cancel_park(struct ThreadParker *parker) {
  pthread_mutex_unlock(&parker->lock);
  // Note: we cannot change parker->any_sleeping here, as that may prevent other threads from waking up.
}
void accelerate_parker_wake_all(struct ThreadParker *parker) {
  pthread_mutex_lock(&parker->lock);
  // TODO: We need to perform this check inside the critical section to avoid
  // a race condition. However, this does increase lock contention, so ideally
  // we should find a better solution for this. For now, this at least makes it
  // sound.
  if (atomic_load_explicit(&parker->any_sleeping, memory_order_acquire) == 0) {
    // No thread is sleeping
    pthread_mutex_unlock(&parker->lock);
    return;
  }
  atomic_store_explicit(&parker->any_sleeping, 0, memory_order_release);
  pthread_cond_broadcast(&parker->cond_var);
  pthread_mutex_unlock(&parker->lock);
}

#define ATTEMPTS 16

void* accelerate_worker(void *data_packed) {
  struct Workers *workers = accelerate_unpack_ptr((uintptr_t) data_packed);
  uint16_t thread_idx = accelerate_unpack_tag((uintptr_t) data_packed);

  unsigned int attempts_remaining = ATTEMPTS;

  struct Task task;
  task.program = NULL;
  task.location = 0;
  while (true) {
    if (attempts_remaining == 0) {
      accelerate_parker_maybe_park(&workers->scheduler.parker);
    }
    if (task.program == NULL) {
      task = accelerate_dequeue(workers);
    }

    if (task.program != NULL) {
      if (attempts_remaining == 0) {
        accelerate_parker_cancel_park(&workers->scheduler.parker);
      }
      struct KernelLaunch* kernel = task.program->run(&accelerate_runtime_lib, workers, thread_idx, task.program, task.location);
      if (kernel == NULL) {
        accelerate_program_release(task.program);
        task.program = NULL;
        task.location = 0;
      } else {
        // Initialize kernel memory and check if the kernel should be executed in parallel.
        unsigned char parallel =
          kernel->work_function(kernel, 0xFFFFFFFF, NULL);

        // start_task from the Work Assisting paper
        if (parallel == 1) {
          atomic_store_explicit(&workers->scheduler.activities[thread_idx], accelerate_pack(kernel, 0), memory_order_release);
          accelerate_parker_wake_all(&workers->scheduler.parker);
        }
        kernel->work_function(kernel, 0, (uintptr_t*) &workers->scheduler.activities[thread_idx]);
        // Keep track of whether this was the last thread working on the kernel
        bool is_last;
        if (parallel == 1) {
          // signal_task_empty from the Work Assisting paper,
          // and end_task
          // Note that in the paper, the work function calls this function.
          // In this implementation, this happens here.
          // This simplifies the code generation for work function (which are compiled via LLVM),
          // and allows us to combine the decrement of active_threads from end_task.
          uintptr_t old = atomic_exchange_explicit(
            &workers->scheduler.activities[thread_idx],
            accelerate_pack(NULL, 0),
            memory_order_relaxed
          );
          if (accelerate_unpack_ptr(old) == kernel) {
            // Move the reference count from the pointer to the task object,
            // and decrement the reference count by one.
            // This combines the atomic_fetch_add in signal_task_empty with the one in end_task
            uint16_t count = accelerate_unpack_tag(old);
            if (count == 0) {
              // No other thread has assisted. No need to update the reference count.
              // Since there is no other thread, we know this is also th last thread.
              is_last = true;
            } else {
              int32_t remaining_threads = atomic_fetch_add_explicit(
                &kernel->active_threads,
                // The + 1 from signal_task_empty cancels out with the -1 in end_task
                count,
                memory_order_acq_rel
              );
              is_last = -remaining_threads == count;
            }
          } else {
            // Decrement active_threads (end_task in the Work Assisting paper)
            int32_t remaining_threads = atomic_fetch_add_explicit(
              &kernel->active_threads,
              -1,
              memory_order_acq_rel
            );
            is_last = remaining_threads == 1;
          }
        } else {
          // This kernel was executed by a single thread, so this is definitely the last thread.
          is_last = true;
        }

        if (is_last) {
          // The last thread executes the finish function.
          // First, execute the finish procedure of the kernel:
          kernel->work_function(kernel, 0xFFFFFFFE, NULL);
          // Then continue the program after this kernel, via
          // program_continuation in the KernelLaunch structure.
          task.program = kernel->program;
          task.location = kernel->program_continuation;
        } else {
          task.program = NULL;
          task.location = 0;
        }
      }
      attempts_remaining = ATTEMPTS;
      continue;
    }

    // Try assisting with the data-parallel activity (KernelLaunch) from another thread.
    // try_assist from the Work Assisting paper
    uint16_t thread_count = workers->thread_count;
    int16_t inc = (thread_idx % 2 == 0) ? 1 : -1;
    int16_t other_thread = thread_idx;
    bool workassisting_found = false;
    while (true) {
      other_thread += inc;
      while (other_thread >= thread_count) other_thread -= thread_count;
      if (other_thread < 0) other_thread += thread_count;
      if (other_thread == thread_idx) break;

      _Atomic(uintptr_t) *ptr = &workers->scheduler.activities[other_thread];
      if (atomic_load_explicit(ptr, memory_order_relaxed) == 0) continue;
      uintptr_t activity = atomic_fetch_add_explicit(ptr, accelerate_pack(NULL, 1), memory_order_acquire);
      struct KernelLaunch *kernel = accelerate_unpack_ptr(activity);
      if (kernel == NULL) continue;
      // We found a data-parallel activity where we can assist!
      if (attempts_remaining == 0) {
        accelerate_parker_cancel_park(&workers->scheduler.parker);
      }
      uint32_t i = atomic_fetch_add_explicit(&kernel->work_index, 1, memory_order_relaxed);
      kernel->work_function(kernel, i, (uintptr_t*) ptr);
      // signal_task_empty from the Work Assisting paper,
      // and end_task
      // Similar to above, signal_task_empty happens here instead of in the work function.
      // The same reasoning as above applies here.
      uintptr_t old = atomic_load_explicit(ptr, memory_order_relaxed);
      bool is_last;
      while (true) {
        if (accelerate_unpack_ptr(old) != kernel) {
          // Another thread has moved the reference count.
          // We now only need to decrement the reference count for this thread.
          int32_t remaining_threads = atomic_fetch_add_explicit(
            &kernel->active_threads,
            -1,
            memory_order_acq_rel
          );
          is_last = remaining_threads == 1;
          break;
        }
        if (atomic_compare_exchange_weak_explicit(ptr, &old, accelerate_pack(NULL, 0), memory_order_relaxed, memory_order_relaxed)) {
          // Move the reference count from the pointer to the task object.
          int32_t remaining_threads = atomic_fetch_add_explicit(&kernel->active_threads, accelerate_unpack_tag(old), memory_order_acq_rel);
          is_last = -remaining_threads == accelerate_unpack_tag(old);
          break;
        }
      }
      if (is_last) {
        // The last thread executes the finish function.
        // First, execute the finish procedure of the kernel:
        kernel->work_function(kernel, 0xFFFFFFFE, NULL);
        // Then continue the program after this kernel, via
        // program_continuation in the KernelLaunch structure.
        task.program = kernel->program;
        task.location = kernel->program_continuation;
      }
      attempts_remaining = ATTEMPTS;
      workassisting_found = true;
      break;
    }
    if (workassisting_found) continue;

    // No task or data-parallel activity available.
    if (attempts_remaining == 0) {
      accelerate_parker_confirm_park(&workers->scheduler.parker);
      attempts_remaining = ATTEMPTS;
    } else {
      if (attempts_remaining < ATTEMPTS / 2) {
        sched_yield();
      }
      attempts_remaining -= 1;
    }
  }
}

struct Workers* accelerate_start_workers(uint64_t thread_count) {
  struct Workers *workers = malloc(sizeof(struct Workers));

  workers->scheduler.queue = accelerate_queue_new();
  if (pthread_mutex_init(&workers->scheduler.parker.lock, NULL) != 0) {
    perror("Accelerate runtime: could not initialize mutex.");                                        
    exit(1);      
  }
  if (pthread_cond_init(&workers->scheduler.parker.cond_var, NULL) != 0) {                                    
    perror("Accelerate runtime: could not initialize pthread cond var.");                                        
    exit(1);                                                                    
  }

  workers->scheduler.activities = malloc(sizeof(uintptr_t) * thread_count);

  workers->thread_count = thread_count;

  for (uint64_t i = 0; i < thread_count; i++) {
    workers->scheduler.activities[i] = 0;
  }

  for (uint64_t i = 0; i < thread_count; i++) {
    // TODO: Check if setting thread affinities helps
    pthread_t worker_thread;
    uintptr_t data = accelerate_pack(workers, i);
    pthread_create(&worker_thread, NULL, accelerate_worker, (void*) data);
  }

  return workers;
}
