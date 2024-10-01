#include <inttypes.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <pthread.h>

struct Workers;

struct Program;
typedef void ProgramFunction(struct Workers*, struct Program* data, uint32_t location);
struct Program {
  uint64_t reference_count;
  ProgramFunction *run;
  uint8_t data[0]; // Actual type will be different. Only use this field to get a pointer to the data.
};

struct Task {
  struct Program *program;
  uint32_t location;
};

// Bindings to concurrentqueue (implemented in C++)
typedef void Queue;
Queue* accelerate_queue_new();
bool accelerate_queue_enqueue(Queue *queue, struct Task task);
struct Task accelerate_queue_dequeue(Queue *queue);

struct ThreadParker {
  // The lock to take before letting a thread wait, or waking all threads.
  pthread_mutex_t lock;
  pthread_cond_t cond_var;
  // Should be modified with atomic instructions.
  // Contains 0 (false) or 1 (true).
  // Denotes whether any thread might be sleeping.
  uint any_sleeping;
};
void accelerate_parker_wake_all(struct ThreadParker *parker);

struct Scheduler {
  Queue* queue;
  struct ThreadParker parker;
};

struct Workers {
  struct Scheduler scheduler;
  uint64_t thread_count;
};

struct Signal {
  // State is either:
  // 0 for an unresolved signal without terms that wait on this signal
  // 1 for a resolved signal
  // Otherwise, pointer to a SignalWaiter for an term that waits on this signal
  size_t state;
};

struct SignalWaiter {
  // The program that should be scheduled
  struct Program *program;
  uint32_t location; // The location in the program
  struct SignalWaiter *next;
};

struct Workers* accelerate_start_workers(uint64_t thread_count);

struct Program* accelerate_program_alloc(uint64_t byte_size, ProgramFunction *function);
void accelerate_program_retain(struct Program *program);
void accelerate_program_release(struct Program *program);

void accelerate_schedule(struct Workers *workers, struct Program *program, uint32_t location);
void accelerate_schedule_owned(struct Workers *workers, struct Program *program, uint32_t location);
void accelerate_schedule_after(struct Workers *workers, struct Program *program, uint32_t location, struct Signal *signal, struct SignalWaiter *waiter);
char accelerate_schedule_after_or(struct Workers *workers, struct Program *program, uint32_t location, struct Signal *signal, struct SignalWaiter *waiter);

struct Task accelerate_dequeue(struct Workers *workers);

void accelerate_signal_resolve(struct Workers *workers, struct Signal *signal);

void accelerate_buffer_retain(void* interior);
void accelerate_buffer_retain_by(void* interior, uint64_t amount);
void accelerate_buffer_release(void* interior);
void accelerate_buffer_release_by(void* interior, uint64_t amount);

inline uintptr_t accelerate_pack(void *pointer, uint16_t tag) {
  const uintptr_t MASK = ~(1ULL << 48);
  uintptr_t result = (uintptr_t) pointer & MASK;
  return result | (((uintptr_t) tag) << 48);
}
inline void* accelerate_unpack_ptr(uintptr_t packed) {
  intptr_t pointer = ((intptr_t)packed << 16) >> 16;
  return (void*) pointer;
}
inline uint16_t accelerate_unpack_tag(uintptr_t packed) {
  return packed >> 48;
}

struct KernelLaunch;
typedef void KernelFunction(struct KernelLaunch *kernel, uint32_t first_index, struct KernelLaunch **activities_slot);
struct KernelLaunch {
  KernelFunction *work_function;
  struct Program *program;
  uint32_t program_continuation;
  uint32_t active_threads;
  uint32_t work_index;
  // In the future, perhaps also store a uint32_t work_size
  uint8_t args[0]; // Actual type will be different. Only use this field to get a pointer to the arguments.
};
