#include <cuda.h>
#include <cuda_bf16.h>
#include <cuda_runtime.h>

extern "C" __global__ void __launch_bounds__(32, 1) retirement_fragment(const __grid_constant__ CUtensorMap O_map, unsigned K, bool flag, bool leader) {
  extern __shared__ __align__(1024) unsigned char gpu_smem[];
  const unsigned gpu_smem_base = static_cast<unsigned>(__cvta_generic_to_shared(gpu_smem));
  {
    {
      for (unsigned v0 = 0u; v0 < K; ++v0) {
        if (((threadIdx.x % 32u) == 0u)) {
          asm volatile("cp.async.bulk.tensor.2d.global.shared::cta.bulk_group [%0, {%2, %3}], [%1];" :  : "l"(reinterpret_cast<unsigned long long>(&O_map)), "r"((gpu_smem_base + 0u)), "r"(0u), "r"(0u) : "memory");
          asm volatile("cp.async.bulk.commit_group;" :  :  : "memory");
        }
        __syncwarp();
      }
    }
    {
      {
        if (leader) {
          asm volatile("tcgen05.fence::before_thread_sync;" :  :  : "memory");
        }
      }
      {
        if (((threadIdx.x % 32u) == 0u)) {
          asm volatile("cp.async.bulk.wait_group 0;" :  :  : "memory");
        }
        __syncwarp();
      }
    }
  }
}

// Launches retirement_fragment on `stream`, encoding its tensor maps as its parameter types require.
extern "C" cudaError_t retirement_fragment_launch(float* O, unsigned M, unsigned N, unsigned K, bool flag, bool leader, cudaStream_t stream) {
  CUtensorMap O_map;
  {
    const cuuint64_t dims[2] = {N, M};
    const cuuint64_t strides[1] = {static_cast<cuuint64_t>(N) * 4u};
    const cuuint32_t box[2] = {32u, 32u};
    const cuuint32_t steps[2] = {1u, 1u};
    if (cuTensorMapEncodeTiled(&O_map, CU_TENSOR_MAP_DATA_TYPE_FLOAT32, 2, const_cast<void*>(static_cast<const void*>(O)), dims, strides, box, steps,
        CU_TENSOR_MAP_INTERLEAVE_NONE, CU_TENSOR_MAP_SWIZZLE_128B, CU_TENSOR_MAP_L2_PROMOTION_L2_256B,
        CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE) != CUDA_SUCCESS) {
      return cudaErrorInvalidValue;
    }
  }
  const cudaError_t status = cudaFuncSetAttribute(reinterpret_cast<const void*>(retirement_fragment), cudaFuncAttributeMaxDynamicSharedMemorySize, 4096);
  if (status != cudaSuccess) {
    return status;
  }
  void* args[] = {&O_map, &K, &flag, &leader};
  return cudaLaunchKernel(reinterpret_cast<const void*>(retirement_fragment), dim3(1u, 1u), dim3(32u), args, 4096u, stream);
}
