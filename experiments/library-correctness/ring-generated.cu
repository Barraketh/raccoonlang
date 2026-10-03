#include <cuda.h>
#include <cuda_bf16.h>
#include <cuda_runtime.h>

extern "C" __global__ void __launch_bounds__(64, 1) primitive_copy_ring(const __grid_constant__ CUtensorMap I_map, unsigned PK, unsigned CK, bool Pflag, bool Cflag) {
  extern __shared__ __align__(1024) unsigned char gpu_smem[];
  const unsigned gpu_smem_base = static_cast<unsigned>(__cvta_generic_to_shared(gpu_smem));
  unsigned v0 = 0u;
  unsigned v1 = 0u;
  {
    if ((threadIdx.x == 0u)) {
      asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 0u)), "r"(1u) : "memory");
      asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 8u)), "r"(1u) : "memory");
      asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0];" :  : "r"((gpu_smem_base + 8u)) : "memory");
      asm volatile("fence.mbarrier_init.release.cluster;" :  :  : "memory");
    }
    __syncthreads();
  }
  {
    if ((threadIdx.x == 0u)) {
      {
        for (unsigned v2 = 0u; v2 < PK; ++v2) {
          {
            asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"((gpu_smem_base + 8u)), "r"(v0) : "memory");
          }
          {
            asm volatile("mbarrier.arrive.expect_tx.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 0u)), "r"(8192u) : "memory");
            asm volatile("cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes [%0], [%1, {%3, %4}], [%2];" :  : "r"((gpu_smem_base + 1024u)), "l"(reinterpret_cast<unsigned long long>(&I_map)), "r"((gpu_smem_base + 0u)), "r"(0u), "r"(0u) : "memory");
            v0 = (v0 ^ 1u);
          }
        }
      }
      {
        asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"((gpu_smem_base + 8u)), "r"(v0) : "memory");
      }
    }
    if ((threadIdx.x == 32u)) {
      {
        for (unsigned v6 = 0u; v6 < CK; ++v6) {
          {
            asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"((gpu_smem_base + 0u)), "r"(v1) : "memory");
          }
          {
            {
              if (Cflag) {
                const __nv_bfloat16 v8 = reinterpret_cast<__nv_bfloat16*>(gpu_smem + 1024)[0u];
              } else {
                {
                  const __nv_bfloat16 v9 = reinterpret_cast<__nv_bfloat16*>(gpu_smem + 1024)[0u];
                }
                {
                  const __nv_bfloat16 v10 = reinterpret_cast<__nv_bfloat16*>(gpu_smem + 1024)[0u];
                }
              }
            }
            {
              asm volatile("fence.proxy.async.shared::cta;" :  :  : "memory");
              asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0];" :  : "r"((gpu_smem_base + 8u)) : "memory");
              v1 = (v1 ^ 1u);
            }
          }
        }
      }
      {
      }
    }
    __syncthreads();
    if ((threadIdx.x == 0u)) {
      asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 0u)) : "memory");
      asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 8u)) : "memory");
    }
  }
}

// Launches primitive_copy_ring on `stream`, encoding its tensor maps as its parameter types require.
extern "C" cudaError_t primitive_copy_ring_launch(const __nv_bfloat16* I, unsigned M, unsigned N, unsigned PK, unsigned CK, bool Pflag, bool Cflag, cudaStream_t stream) {
  CUtensorMap I_map;
  {
    const cuuint64_t dims[2] = {N, M};
    const cuuint64_t strides[1] = {static_cast<cuuint64_t>(N) * 2u};
    const cuuint32_t box[2] = {64u, 64u};
    const cuuint32_t steps[2] = {1u, 1u};
    if (cuTensorMapEncodeTiled(&I_map, CU_TENSOR_MAP_DATA_TYPE_BFLOAT16, 2, const_cast<void*>(static_cast<const void*>(I)), dims, strides, box, steps,
        CU_TENSOR_MAP_INTERLEAVE_NONE, CU_TENSOR_MAP_SWIZZLE_128B, CU_TENSOR_MAP_L2_PROMOTION_L2_256B,
        CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE) != CUDA_SUCCESS) {
      return cudaErrorInvalidValue;
    }
  }
  const cudaError_t status = cudaFuncSetAttribute(reinterpret_cast<const void*>(primitive_copy_ring), cudaFuncAttributeMaxDynamicSharedMemorySize, 9216);
  if (status != cudaSuccess) {
    return status;
  }
  void* args[] = {&I_map, &PK, &CK, &Pflag, &Cflag};
  return cudaLaunchKernel(reinterpret_cast<const void*>(primitive_copy_ring), dim3(1u, 1u), dim3(64u), args, 9216u, stream);
}
