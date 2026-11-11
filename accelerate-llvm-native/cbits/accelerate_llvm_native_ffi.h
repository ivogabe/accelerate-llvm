#ifndef __ACCELERATE_LLVM_NATIVE_FFI_H__
#define __ACCELERATE_LLVM_NATIVE_FFI_H__

#include <inttypes.h>

struct AccelerateKernelHeader {
  // Public interface to struct KernelLaunch (defined in types.h)
  void *private0;
  void *private1;
  uint32_t private2;
  uint32_t private3;
  _Atomic uint64_t work_index;
  _Atomic uint64_t *work_per_thread;
  void *private4;
};

void accelerate_llvm_native_ffi_parallel_loop(void (*work)(void*, int64_t), void *ctx, int64_t n);

#endif // __ACCELERATE_LLVM_NATIVE_FFI_H__
