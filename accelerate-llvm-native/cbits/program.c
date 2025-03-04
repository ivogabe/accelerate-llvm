#include "types.h"

struct Program* accelerate_program_alloc(uint64_t byte_size, ProgramFunction *function, void *destructor_mvar) {
  struct Program* program = accelerate_raw_alloc(byte_size, 8);
  program->reference_count = 1;
  program->run = function;
  program->destructor_mvar = destructor_mvar;
  return program;
}
void accelerate_program_retain(struct Program *program) {
  atomic_fetch_add_explicit(&program->reference_count, 1, memory_order_acquire);
}
void accelerate_program_release(struct Program *program) {
  uint64_t old = atomic_fetch_add_explicit(&program->reference_count, -1, memory_order_acq_rel);
  if (old == 1) {
    // Location 1 of the program is the destructor,
    // which may be invoked without a Worker* pointer and without a thread index.
    program->run(&accelerate_runtime_lib, NULL, 0, program, 1);
    // By filling this MVar, the Haskell runtime is informed that the run function (program->run)
    // and any kernels from this program, are not needed by this program any more.
    // The Haskell garbage collector may eventually deallocate them.
    hs_try_putmvar(-1, program->destructor_mvar);
    accelerate_raw_free(program);
  }
}

// Reference counting on Refs containing Buffers
// See [reference counting for Ref] in Data.Array.Accelerate.LLVM.Native.Link.Schedule
void accelerate_ref_write_buffer(void **ref, void *buffer) {
  _Atomic size_t *ptr = (_Atomic size_t*) ref;
  size_t value = *ptr;
  size_t incremented = value >> 1;
  // Add the number of references to the Ref to the Buffer
  accelerate_buffer_retain_by(buffer, incremented);
  while (true) {
    if (atomic_compare_exchange_weak_explicit(ptr, &value, (size_t) buffer, memory_order_relaxed, memory_order_relaxed)) {
      // Check if we incremented the reference count by too much
      size_t over = incremented - (value >> 1);
      if (over > 0) {
        accelerate_buffer_release_by(buffer, over);
      }
      return;
    }
    // compare-and-swap failed.
    // Check if we need to increment the reference count more
    if ((value >> 1) > incremented) {
      accelerate_buffer_retain_by(buffer, (value >> 1) - incremented);
      incremented = value >> 1;
    }
  }
}
void accelerate_ref_retain(void **ref) {
  _Atomic(size_t) *ptr = (_Atomic size_t*) ref;
  size_t value = *ptr;
  while (true) {
    // Note: reference count is shifted by one. The least significant bit is a tag to denote that this is an unfilled reference.
    if ((value & 1) == 0) {
      // Ref is already filled. Retain the buffer stored in the Ref.
      accelerate_buffer_retain((void*) value);
      return;
    }
    // Ref is not filled. Update the reference count in the Ref.
    if (atomic_compare_exchange_weak_explicit(ptr, &value, value + 2, memory_order_relaxed, memory_order_relaxed)) {
      return;
    }
  }
}
void accelerate_ref_release(void **ref) {
  _Atomic(size_t) *ptr = (_Atomic size_t*) ref;
  size_t value = *ptr;
  while (true) {
    // Note: reference count is shifted by one. The least significant bit is a tag to denote that this is an unfilled reference.
    if ((value & 1) == 0) {
      // Ref is already filled
      accelerate_buffer_release((void*) value);
      return;
    }
    // Ref is not filled. Update the reference count in the Ref.
    if (atomic_compare_exchange_weak_explicit(ptr, &value, value - 2, memory_order_relaxed, memory_order_relaxed)) {
      return;
    }
  }
}
