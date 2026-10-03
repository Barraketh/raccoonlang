#include <cuda.h>
#include <cuda_bf16.h>
#include <cuda_runtime.h>

extern "C" __global__ void __cluster_dims__(2, 1, 1) __launch_bounds__(256, 1) gemm_pair(const __grid_constant__ CUtensorMap A_map, const __grid_constant__ CUtensorMap B_map, const __grid_constant__ CUtensorMap C_map, unsigned M, unsigned N, unsigned K) {
  extern __shared__ __align__(1024) unsigned char gpu_smem[];
  const unsigned gpu_smem_base = static_cast<unsigned>(__cvta_generic_to_shared(gpu_smem));
  unsigned v0;
  asm volatile("mov.u32 %0, %%cluster_ctarank;" : "=r"(v0) :  : "memory");
  unsigned v1;
  asm volatile("mov.u32 %0, %%clusterid.x;" : "=r"(v1) :  : "memory");
  unsigned v2;
  asm volatile("mov.u32 %0, %%nclusterid.x;" : "=r"(v2) :  : "memory");
  const unsigned v3 = ((N + 255u) / 256u);
  const unsigned v4 = ((M + 255u) / 256u);
  const unsigned v5 = (v4 * v3);
  const unsigned v6 = ((v4 < 8u) ? v4 : 8u);
  const unsigned v7 = (v6 * v3);
  if ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) == 0u)) {
    asm volatile("tcgen05.alloc.cta_group::2.sync.aligned.shared::cta.b32 [%0], %1;" :  : "r"((gpu_smem_base + 0u)), "r"(512u) : "memory");
    asm volatile("tcgen05.relinquish_alloc_permit.cta_group::2.sync.aligned;" :  :  : "memory");
  }
  asm volatile("tcgen05.fence::before_thread_sync;" :  :  : "memory");
  __syncthreads();
  asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
  const unsigned v8 = reinterpret_cast<unsigned*>(gpu_smem + 0)[0u];
  if ((threadIdx.x == 0u)) {
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 8u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 16u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 24u)), "r"(256u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 32u)), "r"(256u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 24u)), "r"(256u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 32u)), "r"(256u) : "memory");
    asm volatile("fence.mbarrier_init.release.cluster;" :  :  : "memory");
  }
  __syncwarp();
  asm volatile("barrier.cluster.arrive.release.aligned;" :  :  : "memory");
  asm volatile("barrier.cluster.wait.acquire.aligned;" :  :  : "memory");
  if ((threadIdx.x == 0u)) {
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230400u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230408u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230416u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230424u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230432u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230440u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230448u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230456u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230464u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230472u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230480u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 230488u)), "r"(1u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 230448u)), "r"(1u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 230456u)), "r"(1u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 230464u)), "r"(1u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 230472u)), "r"(1u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 230480u)), "r"(1u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 230488u)), "r"(1u) : "memory");
    asm volatile("fence.mbarrier_init.release.cluster;" :  :  : "memory");
  }
  __syncwarp();
  asm volatile("barrier.cluster.arrive.release.aligned;" :  :  : "memory");
  asm volatile("barrier.cluster.wait.acquire.aligned;" :  :  : "memory");
  if ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) < 4u)) {
    if ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) < 1u)) {
      unsigned v18 = 0u;
      asm volatile("{\n\t.reg .b32 rx;\n\t.reg .pred px;\n\telect.sync rx|px, 0xffffffff;\n\t@px mov.u32 %0, 1;\n\t}" : "+r"(v18) :  : "memory");
      if ((0u < v18)) {
        unsigned v14 = 0u;
        unsigned v15 = 0u;
        for (unsigned v19 = v1; v19 < v5; v19 += v2) {
          {
            asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 230448u) + (v14 * 8u))), "r"(v15) : "memory");
            unsigned v20;
            asm volatile("mapa.shared::cluster.u32 %0, %1, %2;" : "=r"(v20) : "r"(((gpu_smem_base + 230400u) + (v14 * 8u))), "r"(0u) : "memory");
            if ((v0 == 0u)) {
              asm volatile("mbarrier.arrive.expect_tx.shared::cta.b64 _, [%0], %1;" :  : "r"(((gpu_smem_base + 230400u) + (v14 * 8u))), "r"(65536u) : "memory");
            }
            asm volatile("cp.async.bulk.tensor.2d.cta_group::2.shared::cluster.global.mbarrier::complete_tx::bytes [%0], [%1, {%3, %4}], [%2];" :  : "r"(((gpu_smem_base + 33792u) + (v14 * 32768u))), "l"(reinterpret_cast<unsigned long long>(&A_map)), "r"(v20), "r"((0u * 64u)), "r"((((((v19 / v7) * v6) + ((v19 - ((v19 / v7) * v7)) % (((v4 - ((v19 / v7) * v6)) < v6) ? (v4 - ((v19 / v7) * v6)) : v6))) * 256u) + (v0 * 128u))) : "memory");
            asm volatile("cp.async.bulk.tensor.2d.cta_group::2.shared::cluster.global.mbarrier::complete_tx::bytes [%0], [%1, {%3, %4}], [%2];" :  : "r"((((gpu_smem_base + 33792u) + (v14 * 32768u)) + 16384u)), "l"(reinterpret_cast<unsigned long long>(&B_map)), "r"(v20), "r"((0u * 64u)), "r"(((((v19 - ((v19 / v7) * v7)) / (((v4 - ((v19 / v7) * v6)) < v6) ? (v4 - ((v19 / v7) * v6)) : v6)) * 256u) + (v0 * 128u))) : "memory");
            v14 = (v14 + 1u);
            if ((v14 == 6u)) {
              v14 = 0u;
              v15 = (1u - v15);
            }
          }
          for (unsigned v21 = 1u; v21 < ((63u + K) / 64u); ++v21) {
            asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 230448u) + (v14 * 8u))), "r"(v15) : "memory");
            unsigned v22;
            asm volatile("mapa.shared::cluster.u32 %0, %1, %2;" : "=r"(v22) : "r"(((gpu_smem_base + 230400u) + (v14 * 8u))), "r"(0u) : "memory");
            if ((v0 == 0u)) {
              asm volatile("mbarrier.arrive.expect_tx.shared::cta.b64 _, [%0], %1;" :  : "r"(((gpu_smem_base + 230400u) + (v14 * 8u))), "r"(65536u) : "memory");
            }
            asm volatile("cp.async.bulk.tensor.2d.cta_group::2.shared::cluster.global.mbarrier::complete_tx::bytes [%0], [%1, {%3, %4}], [%2];" :  : "r"(((gpu_smem_base + 33792u) + (v14 * 32768u))), "l"(reinterpret_cast<unsigned long long>(&A_map)), "r"(v22), "r"((v21 * 64u)), "r"((((((v19 / v7) * v6) + ((v19 - ((v19 / v7) * v7)) % (((v4 - ((v19 / v7) * v6)) < v6) ? (v4 - ((v19 / v7) * v6)) : v6))) * 256u) + (v0 * 128u))) : "memory");
            asm volatile("cp.async.bulk.tensor.2d.cta_group::2.shared::cluster.global.mbarrier::complete_tx::bytes [%0], [%1, {%3, %4}], [%2];" :  : "r"((((gpu_smem_base + 33792u) + (v14 * 32768u)) + 16384u)), "l"(reinterpret_cast<unsigned long long>(&B_map)), "r"(v22), "r"((v21 * 64u)), "r"(((((v19 - ((v19 / v7) * v7)) / (((v4 - ((v19 / v7) * v6)) < v6) ? (v4 - ((v19 / v7) * v6)) : v6)) * 256u) + (v0 * 128u))) : "memory");
            v14 = (v14 + 1u);
            if ((v14 == 6u)) {
              v14 = 0u;
              v15 = (1u - v15);
            }
          }
        }
        asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 230448u) + (v14 * 8u))), "r"(v15) : "memory");
        v14 = (v14 + 1u);
        if ((v14 == 6u)) {
          v14 = 0u;
          v15 = (1u - v15);
        }
        asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 230448u) + (v14 * 8u))), "r"(v15) : "memory");
        v14 = (v14 + 1u);
        if ((v14 == 6u)) {
          v14 = 0u;
          v15 = (1u - v15);
        }
        asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 230448u) + (v14 * 8u))), "r"(v15) : "memory");
        v14 = (v14 + 1u);
        if ((v14 == 6u)) {
          v14 = 0u;
          v15 = (1u - v15);
        }
        asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 230448u) + (v14 * 8u))), "r"(v15) : "memory");
        v14 = (v14 + 1u);
        if ((v14 == 6u)) {
          v14 = 0u;
          v15 = (1u - v15);
        }
        asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 230448u) + (v14 * 8u))), "r"(v15) : "memory");
        v14 = (v14 + 1u);
        if ((v14 == 6u)) {
          v14 = 0u;
          v15 = (1u - v15);
        }
        asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 230448u) + (v14 * 8u))), "r"(v15) : "memory");
        v14 = (v14 + 1u);
        if ((v14 == 6u)) {
          v14 = 0u;
          v15 = (1u - v15);
        }
      }
      __syncwarp();
    } else {
      if ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) < 2u)) {
        if ((v0 == 0u)) {
          unsigned v23 = 0u;
          asm volatile("{\n\t.reg .b32 rx;\n\t.reg .pred px;\n\telect.sync rx|px, 0xffffffff;\n\t@px mov.u32 %0, 1;\n\t}" : "+r"(v23) :  : "memory");
          if ((0u < v23)) {
            unsigned v16 = 0u;
            unsigned v17 = 0u;
            unsigned v9 = 0u;
            unsigned v10 = 0u;
            for (unsigned v24 = v1; v24 < v5; v24 += v2) {
              asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 24u) + (v9 * 8u))), "r"(v10) : "memory");
              asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
              {
                asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 230400u) + (v16 * 8u))), "r"(v17) : "memory");
                asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
                asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::2.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"((v8 + (v9 * 256u))), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v16 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 0ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v16 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 0ull)), "r"(272630928u), "r"(0u) : "memory");
                asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::2.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"((v8 + (v9 * 256u))), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v16 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 2ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v16 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 2ull)), "r"(272630928u), "r"(1u) : "memory");
                asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::2.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"((v8 + (v9 * 256u))), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v16 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 4ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v16 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 4ull)), "r"(272630928u), "r"(1u) : "memory");
                asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::2.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"((v8 + (v9 * 256u))), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v16 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 6ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v16 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 6ull)), "r"(272630928u), "r"(1u) : "memory");
                asm volatile("{\n\t.reg .b16 mask;\n\tmov.b16 mask, 3;\n\ttcgen05.commit.cta_group::2.mbarrier::arrive::one.shared::cluster.multicast::cluster.b64 [%0], mask;\n\t}" :  : "r"(((gpu_smem_base + 230448u) + (v16 * 8u))) : "memory");
                v16 = (v16 + 1u);
                if ((v16 == 6u)) {
                  v16 = 0u;
                  v17 = (1u - v17);
                }
              }
              for (unsigned v25 = 1u; v25 < ((63u + K) / 64u); ++v25) {
                asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 230400u) + (v16 * 8u))), "r"(v17) : "memory");
                asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
                asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::2.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"((v8 + (v9 * 256u))), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v16 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 0ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v16 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 0ull)), "r"(272630928u), "r"(1u) : "memory");
                asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::2.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"((v8 + (v9 * 256u))), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v16 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 2ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v16 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 2ull)), "r"(272630928u), "r"(1u) : "memory");
                asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::2.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"((v8 + (v9 * 256u))), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v16 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 4ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v16 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 4ull)), "r"(272630928u), "r"(1u) : "memory");
                asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::2.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"((v8 + (v9 * 256u))), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v16 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 6ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v16 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 6ull)), "r"(272630928u), "r"(1u) : "memory");
                asm volatile("{\n\t.reg .b16 mask;\n\tmov.b16 mask, 3;\n\ttcgen05.commit.cta_group::2.mbarrier::arrive::one.shared::cluster.multicast::cluster.b64 [%0], mask;\n\t}" :  : "r"(((gpu_smem_base + 230448u) + (v16 * 8u))) : "memory");
                v16 = (v16 + 1u);
                if ((v16 == 6u)) {
                  v16 = 0u;
                  v17 = (1u - v17);
                }
              }
              asm volatile("{\n\t.reg .b16 mask;\n\tmov.b16 mask, 3;\n\ttcgen05.commit.cta_group::2.mbarrier::arrive::one.shared::cluster.multicast::cluster.b64 [%0], mask;\n\t}" :  : "r"(((gpu_smem_base + 8u) + (v9 * 8u))) : "memory");
              v9 = (v9 + 1u);
              if ((v9 == 2u)) {
                v9 = 0u;
                v10 = (1u - v10);
              }
            }
            asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 24u) + (v9 * 8u))), "r"(v10) : "memory");
            v9 = (v9 + 1u);
            if ((v9 == 2u)) {
              v9 = 0u;
              v10 = (1u - v10);
            }
            asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 24u) + (v9 * 8u))), "r"(v10) : "memory");
            v9 = (v9 + 1u);
            if ((v9 == 2u)) {
              v9 = 0u;
              v10 = (1u - v10);
            }
          }
          __syncwarp();
        }
      }
      asm volatile("bar.sync %0, %1;" :  : "r"(1u), "r"(96u) : "memory");
    }
    asm volatile("bar.sync %0, %1;" :  : "r"(2u), "r"(128u) : "memory");
  } else {
    unsigned v11 = 0u;
    unsigned v12 = 0u;
    unsigned v13 = 0u;
    for (unsigned v26 = v1; v26 < v5; v26 += v2) {
      asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.acquire.cluster.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 8u) + (v11 * 8u))), "r"(v12) : "memory");
      asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
      for (unsigned v27 = 0u; v27 < 8u; ++v27) {
        float v28;
        float v29;
        float v30;
        float v31;
        float v32;
        float v33;
        float v34;
        float v35;
        float v36;
        float v37;
        float v38;
        float v39;
        float v40;
        float v41;
        float v42;
        float v43;
        float v44;
        float v45;
        float v46;
        float v47;
        float v48;
        float v49;
        float v50;
        float v51;
        float v52;
        float v53;
        float v54;
        float v55;
        float v56;
        float v57;
        float v58;
        float v59;
        __syncwarp();
        asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
        asm volatile("tcgen05.ld.sync.aligned.32x32b.x8.b32 {%0, %1, %2, %3, %4, %5, %6, %7}, [%8];" : "=f"(v28), "=f"(v29), "=f"(v30), "=f"(v31), "=f"(v32), "=f"(v33), "=f"(v34), "=f"(v35) : "r"(((((v8 + (v11 * 256u)) + (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 32u) << 16u)) + (v27 * 32u)) + 0u)) : "memory");
        asm volatile("tcgen05.ld.sync.aligned.32x32b.x8.b32 {%0, %1, %2, %3, %4, %5, %6, %7}, [%8];" : "=f"(v36), "=f"(v37), "=f"(v38), "=f"(v39), "=f"(v40), "=f"(v41), "=f"(v42), "=f"(v43) : "r"(((((v8 + (v11 * 256u)) + (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 32u) << 16u)) + (v27 * 32u)) + 8u)) : "memory");
        asm volatile("tcgen05.ld.sync.aligned.32x32b.x8.b32 {%0, %1, %2, %3, %4, %5, %6, %7}, [%8];" : "=f"(v44), "=f"(v45), "=f"(v46), "=f"(v47), "=f"(v48), "=f"(v49), "=f"(v50), "=f"(v51) : "r"(((((v8 + (v11 * 256u)) + (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 32u) << 16u)) + (v27 * 32u)) + 16u)) : "memory");
        asm volatile("tcgen05.ld.sync.aligned.32x32b.x8.b32 {%0, %1, %2, %3, %4, %5, %6, %7}, [%8];" : "=f"(v52), "=f"(v53), "=f"(v54), "=f"(v55), "=f"(v56), "=f"(v57), "=f"(v58), "=f"(v59) : "r"(((((v8 + (v11 * 256u)) + (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 32u) << 16u)) + (v27 * 32u)) + 24u)) : "memory");
        asm volatile("tcgen05.wait::ld.sync.aligned;" :  :  : "memory");
        if (((threadIdx.x % 32u) == 0u)) {
          asm volatile("cp.async.bulk.wait_group.read 1;" :  :  : "memory");
        }
        __syncwarp();
        const unsigned v60 = (((gpu_smem_base + 1024u) + ((((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 2u) + v13) * 4096u)) + ((threadIdx.x % 32u) * 128u));
        const unsigned v61 = ((threadIdx.x % 32u) & 7u);
        asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v60 + ((0u ^ v61) << 4u))), "f"(v28), "f"(v29), "f"(v30), "f"(v31) : "memory");
        asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v60 + ((1u ^ v61) << 4u))), "f"(v32), "f"(v33), "f"(v34), "f"(v35) : "memory");
        asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v60 + ((2u ^ v61) << 4u))), "f"(v36), "f"(v37), "f"(v38), "f"(v39) : "memory");
        asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v60 + ((3u ^ v61) << 4u))), "f"(v40), "f"(v41), "f"(v42), "f"(v43) : "memory");
        asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v60 + ((4u ^ v61) << 4u))), "f"(v44), "f"(v45), "f"(v46), "f"(v47) : "memory");
        asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v60 + ((5u ^ v61) << 4u))), "f"(v48), "f"(v49), "f"(v50), "f"(v51) : "memory");
        asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v60 + ((6u ^ v61) << 4u))), "f"(v52), "f"(v53), "f"(v54), "f"(v55) : "memory");
        asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v60 + ((7u ^ v61) << 4u))), "f"(v56), "f"(v57), "f"(v58), "f"(v59) : "memory");
        asm volatile("fence.proxy.async.shared::cta;" :  :  : "memory");
        __syncwarp();
        const unsigned v62 = ((gpu_smem_base + 1024u) + ((((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 2u) + v13) * 4096u));
        const unsigned v63 = ((((((v26 / v7) * v6) + ((v26 - ((v26 / v7) * v7)) % (((v4 - ((v26 / v7) * v6)) < v6) ? (v4 - ((v26 / v7) * v6)) : v6))) * 256u) + (v0 * 128u)) + ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 32u));
        if (((threadIdx.x % 32u) == 0u)) {
          asm volatile("cp.async.bulk.tensor.2d.global.shared::cta.bulk_group [%0, {%2, %3}], [%1];" :  : "l"(reinterpret_cast<unsigned long long>(&C_map)), "r"(v62), "r"(((((v26 - ((v26 / v7) * v7)) / (((v4 - ((v26 / v7) * v6)) < v6) ? (v4 - ((v26 / v7) * v6)) : v6)) * 256u) + (v27 * 32u))), "r"(v63) : "memory");
          asm volatile("cp.async.bulk.commit_group;" :  :  : "memory");
        }
        __syncwarp();
        v13 = (v13 + 1u);
        if ((v13 == 2u)) {
          v13 = 0u;
        }
      }
      asm volatile("tcgen05.fence::before_thread_sync;" :  :  : "memory");
      unsigned v64;
      asm volatile("mapa.shared::cluster.u32 %0, %1, %2;" : "=r"(v64) : "r"(((gpu_smem_base + 24u) + (v11 * 8u))), "r"(0u) : "memory");
      asm volatile("mbarrier.arrive.release.cluster.shared::cluster.b64 _, [%0];" :  : "r"(v64) : "memory");
      v11 = (v11 + 1u);
      if ((v11 == 2u)) {
        v11 = 0u;
        v12 = (1u - v12);
      }
    }
    if (((threadIdx.x % 32u) == 0u)) {
      asm volatile("cp.async.bulk.wait_group 0;" :  :  : "memory");
    }
    __syncwarp();
  }
  __syncthreads();
  __syncwarp();
  asm volatile("barrier.cluster.arrive.release.aligned;" :  :  : "memory");
  asm volatile("barrier.cluster.wait.acquire.aligned;" :  :  : "memory");
  if ((threadIdx.x == 0u)) {
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230400u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230408u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230416u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230424u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230432u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230440u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230448u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230456u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230464u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230472u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230480u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 230488u)) : "memory");
  }
  __syncwarp();
  asm volatile("barrier.cluster.arrive.release.aligned;" :  :  : "memory");
  asm volatile("barrier.cluster.wait.acquire.aligned;" :  :  : "memory");
  if ((threadIdx.x == 0u)) {
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 8u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 16u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 24u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 32u)) : "memory");
  }
  asm volatile("tcgen05.fence::before_thread_sync;" :  :  : "memory");
  __syncwarp();
  asm volatile("barrier.cluster.arrive.release.aligned;" :  :  : "memory");
  asm volatile("barrier.cluster.wait.acquire.aligned;" :  :  : "memory");
  asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
  if ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) == 0u)) {
    asm volatile("tcgen05.dealloc.cta_group::2.sync.aligned.b32 %0, %1;" :  : "r"(v8), "r"(512u) : "memory");
  }
}

// Launches gemm_pair on `stream`, encoding its tensor maps as its parameter types require.
extern "C" cudaError_t gemm_pair_launch(const __nv_bfloat16* A, const __nv_bfloat16* B, float* C, unsigned M, unsigned N, unsigned K, cudaStream_t stream) {
  if (!((static_cast<unsigned long long>(M) * N) < 4294967296ull)) {
    return cudaErrorInvalidValue;
  }
  if (!(M < 2147483648ull)) {
    return cudaErrorInvalidValue;
  }
  if (!(N < 2147483648ull)) {
    return cudaErrorInvalidValue;
  }
  if (!(K < 2147483648ull)) {
    return cudaErrorInvalidValue;
  }
  if (!((N % 4u) == 0u)) {
    return cudaErrorInvalidValue;
  }
  CUtensorMap A_map;
  {
    const cuuint64_t dims[2] = {K, M};
    const cuuint64_t strides[1] = {static_cast<cuuint64_t>(K) * 2u};
    const cuuint32_t box[2] = {64u, 128u};
    const cuuint32_t steps[2] = {1u, 1u};
    if (cuTensorMapEncodeTiled(&A_map, CU_TENSOR_MAP_DATA_TYPE_BFLOAT16, 2, const_cast<void*>(static_cast<const void*>(A)), dims, strides, box, steps,
        CU_TENSOR_MAP_INTERLEAVE_NONE, CU_TENSOR_MAP_SWIZZLE_128B, CU_TENSOR_MAP_L2_PROMOTION_L2_256B,
        CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE) != CUDA_SUCCESS) {
      return cudaErrorInvalidValue;
    }
  }
  CUtensorMap B_map;
  {
    const cuuint64_t dims[2] = {K, N};
    const cuuint64_t strides[1] = {static_cast<cuuint64_t>(K) * 2u};
    const cuuint32_t box[2] = {64u, 128u};
    const cuuint32_t steps[2] = {1u, 1u};
    if (cuTensorMapEncodeTiled(&B_map, CU_TENSOR_MAP_DATA_TYPE_BFLOAT16, 2, const_cast<void*>(static_cast<const void*>(B)), dims, strides, box, steps,
        CU_TENSOR_MAP_INTERLEAVE_NONE, CU_TENSOR_MAP_SWIZZLE_128B, CU_TENSOR_MAP_L2_PROMOTION_L2_256B,
        CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE) != CUDA_SUCCESS) {
      return cudaErrorInvalidValue;
    }
  }
  CUtensorMap C_map;
  {
    const cuuint64_t dims[2] = {N, M};
    const cuuint64_t strides[1] = {static_cast<cuuint64_t>(N) * 4u};
    const cuuint32_t box[2] = {32u, 32u};
    const cuuint32_t steps[2] = {1u, 1u};
    if (cuTensorMapEncodeTiled(&C_map, CU_TENSOR_MAP_DATA_TYPE_FLOAT32, 2, const_cast<void*>(static_cast<const void*>(C)), dims, strides, box, steps,
        CU_TENSOR_MAP_INTERLEAVE_NONE, CU_TENSOR_MAP_SWIZZLE_128B, CU_TENSOR_MAP_L2_PROMOTION_L2_256B,
        CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE) != CUDA_SUCCESS) {
      return cudaErrorInvalidValue;
    }
  }
  const cudaError_t status = cudaFuncSetAttribute(reinterpret_cast<const void*>(gemm_pair), cudaFuncAttributeMaxDynamicSharedMemorySize, 230496);
  if (status != cudaSuccess) {
    return status;
  }
  void* args[] = {&A_map, &B_map, &C_map, &M, &N, &K};
  int gpu_device = 0;
  int gpu_sms = 0;
  if (cudaGetDevice(&gpu_device) != cudaSuccess || cudaDeviceGetAttribute(&gpu_sms, cudaDevAttrMultiProcessorCount, gpu_device) != cudaSuccess) {
    return cudaErrorInvalidValue;
  }
  const unsigned gpu_tiles = (((M + 255u) / 256u) * ((N + 255u) / 256u));
  const unsigned gpu_pairs = static_cast<unsigned>(gpu_sms) / 2u;
  return cudaLaunchKernel(reinterpret_cast<const void*>(gemm_pair), dim3(2u * (gpu_tiles < gpu_pairs ? gpu_tiles : gpu_pairs)), dim3(256u), args, 230496u, stream);
}
