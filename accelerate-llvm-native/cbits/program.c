#include "types.h"

struct Program* accelerate_program_alloc(uint64_t byte_size, ProgramFunction *function) {
  struct Program* program = malloc(byte_size);
  program->reference_count = 1;
  program->run = function;
  return program;
}
void accelerate_program_retain(struct Program *program) {
  atomic_fetch_add_explicit(&program->reference_count, 1, memory_order_acquire);
}
void accelerate_program_release(struct Program *program) {
  int old = atomic_fetch_add_explicit(&program->reference_count, -1, memory_order_acq_rel);
  if (old == 1) {
    // Location 1 of the program is the destructor,
    // which may be invoked without a Worker* pointer.
    program->run(NULL, program, 1);
    free(program);
  }
}
