#include "types.h"

void accelerate_schedule_after(struct Workers *workers, struct Program *program, uint32_t location, struct Signal *signal, struct SignalWaiter *waiter) {
  if (0 == accelerate_schedule_after_or(workers, program, location, signal, waiter)) {
    // Signal is already resolved
    accelerate_schedule(workers, program, location);
  }
}
// Tries to schedules this program after the given signal.
// If the signal is already resolved,
// this function will not schedule it but instead return false (0).
// If the signal is not resolved,
// this function will schedule this program after the given signal
// and retain (increment the reference count of) the program.
char accelerate_schedule_after_or(struct Workers *workers, struct Program *program, uint32_t location, struct Signal *signal, struct SignalWaiter *waiter) {
  // Check if signal is already resolved.
  size_t current = atomic_load_explicit(&signal->state, memory_order_acquire);
  if (current == 1) {
    // Signal is already resolved.
    return 0;
  }

  // Try to store this task in the linked list of waiting tasks for this signal.
  // This happens via a compare-and-swap loop.
  waiter->program = program;
  waiter->location = location;

  accelerate_program_retain(program);
  while (true) {
    waiter->next = (struct SignalWaiter*) current;
    if (atomic_compare_exchange_weak_explicit(&signal->state, &current, (size_t) waiter, memory_order_acq_rel, memory_order_acquire)) {
      return 1;
    }
    if (current == 1) {
      accelerate_program_release(program);
      // Signal was resolved while trying to register this task as waiting.
      return 0;
    }
  }
}
void accelerate_signal_resolve(struct Workers *workers, struct Signal *signal) {
  // Register that this signal is resolved, and acquire a pointer to the first waiting task.
  size_t old = atomic_exchange_explicit(&signal->state, 1, memory_order_acq_rel);
  while (old == 1) {
    return;
  }
  // Schedule all tasks that were waiting on this signal
  struct SignalWaiter *ptr = (struct SignalWaiter*) old;
  while (ptr != NULL) {
    // First read the SignalWaiter, then schedule the task.
    // Scheduling the task will cause the task to be executed,
    // which may cause that the program (and thus the SignalWaiter) is deallocated.
    struct SignalWaiter waiter = *ptr;
    accelerate_schedule_owned(workers, waiter.program, waiter.location);
    ptr = waiter.next;
  }
}

// Variant of 'accelerate_schedule' which takes ownership of the program.
void accelerate_schedule_owned(struct Workers *workers, struct Program *program, uint32_t location) {
  struct Task task;
  task.program = program;
  task.location = location;
  if (!accelerate_queue_enqueue(workers->scheduler.queue, task)) {
    printf("Scheduling a task failed. Out of memory?\n");
  }
  accelerate_parker_wake_all(&workers->scheduler.parker);
}
// Schedules a program at a given location for execution.
void accelerate_schedule(struct Workers *workers, struct Program *program, uint32_t location) {
  accelerate_program_retain(program);
  accelerate_schedule_owned(workers, program, location);
}

struct Task accelerate_dequeue(struct Workers *workers) {
  return accelerate_queue_dequeue(workers->scheduler.queue);
}

void accelerate_execute_kernel(struct Workers *workers, struct KernelLaunch *kernel) {
  // TODO: Implement work assisting here
  kernel->work_function(kernel, 0, NULL);
  accelerate_schedule(workers, kernel->program, kernel->program_continuation);
}
