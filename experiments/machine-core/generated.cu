#include <cuda.h>
#include <cuda_bf16.h>
#include <cuda_runtime.h>

extern "C" __global__ void __launch_bounds__(256, 1) tinygemm(const __grid_constant__ CUtensorMap A_map, const __grid_constant__ CUtensorMap B_map, const __grid_constant__ CUtensorMap C_map, unsigned M, unsigned N, unsigned K) {
  extern __shared__ __align__(1024) unsigned char gpu_smem[];
  const unsigned gpu_smem_base = static_cast<unsigned>(__cvta_generic_to_shared(gpu_smem));
  if ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) == 0u)) {
    asm volatile("tcgen05.alloc.cta_group::1.sync.aligned.shared::cta.b32 [%0], %1;" :  : "r"((gpu_smem_base + 0u)), "r"(128u) : "memory");
    asm volatile("tcgen05.relinquish_alloc_permit.cta_group::1.sync.aligned;" :  :  : "memory");
  }
  asm volatile("tcgen05.fence::before_thread_sync;" :  :  : "memory");
  __syncthreads();
  asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
  const unsigned v0 = reinterpret_cast<unsigned*>(gpu_smem + 0)[0u];
  if ((threadIdx.x == 0u)) {
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 8u)), "r"(1u) : "memory");
    asm volatile("fence.mbarrier_init.release.cluster;" :  :  : "memory");
  }
  __syncthreads();
  if ((threadIdx.x == 0u)) {
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 164864u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 164872u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 164880u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 164888u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 164896u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 164904u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 164912u)), "r"(1u) : "memory");
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" :  : "r"((gpu_smem_base + 164920u)), "r"(1u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 164896u)), "r"(1u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 164904u)), "r"(1u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 164912u)), "r"(1u) : "memory");
    asm volatile("mbarrier.arrive.shared::cta.b64 _, [%0], %1;" :  : "r"((gpu_smem_base + 164920u)), "r"(1u) : "memory");
    asm volatile("fence.mbarrier_init.release.cluster;" :  :  : "memory");
  }
  __syncthreads();
  if ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) < 4u)) {
    if ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) < 1u)) {
      unsigned v6 = 0u;
      asm volatile("{\n\t.reg .b32 rx;\n\t.reg .pred px;\n\telect.sync rx|px, 0xffffffff;\n\t@px mov.u32 %0, 1;\n\t}" : "+r"(v6) :  : "memory");
      if ((0u < v6)) {
        unsigned v2 = 0u;
        unsigned v3 = 0u;
        {
          asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 164896u) + (v2 * 8u))), "r"(v3) : "memory");
          asm volatile("mbarrier.arrive.expect_tx.shared::cta.b64 _, [%0], %1;" :  : "r"(((gpu_smem_base + 164864u) + (v2 * 8u))), "r"(32768u) : "memory");
          asm volatile("cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes [%0], [%1, {%3, %4}], [%2];" :  : "r"(((gpu_smem_base + 33792u) + (v2 * 32768u))), "l"(reinterpret_cast<unsigned long long>(&A_map)), "r"(((gpu_smem_base + 164864u) + (v2 * 8u))), "r"((0u * 64u)), "r"((blockIdx.y * 128u)) : "memory");
          asm volatile("cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes [%0], [%1, {%3, %4}], [%2];" :  : "r"((((gpu_smem_base + 33792u) + (v2 * 32768u)) + 16384u)), "l"(reinterpret_cast<unsigned long long>(&B_map)), "r"(((gpu_smem_base + 164864u) + (v2 * 8u))), "r"((0u * 64u)), "r"((blockIdx.x * 128u)) : "memory");
          v2 = (v2 + 1u);
          if ((v2 == 4u)) {
            v2 = 0u;
            v3 = (1u - v3);
          }
        }
        for (unsigned v7 = 1u; v7 < ((63u + K) / 64u); ++v7) {
          asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 164896u) + (v2 * 8u))), "r"(v3) : "memory");
          asm volatile("mbarrier.arrive.expect_tx.shared::cta.b64 _, [%0], %1;" :  : "r"(((gpu_smem_base + 164864u) + (v2 * 8u))), "r"(32768u) : "memory");
          asm volatile("cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes [%0], [%1, {%3, %4}], [%2];" :  : "r"(((gpu_smem_base + 33792u) + (v2 * 32768u))), "l"(reinterpret_cast<unsigned long long>(&A_map)), "r"(((gpu_smem_base + 164864u) + (v2 * 8u))), "r"((v7 * 64u)), "r"((blockIdx.y * 128u)) : "memory");
          asm volatile("cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes [%0], [%1, {%3, %4}], [%2];" :  : "r"((((gpu_smem_base + 33792u) + (v2 * 32768u)) + 16384u)), "l"(reinterpret_cast<unsigned long long>(&B_map)), "r"(((gpu_smem_base + 164864u) + (v2 * 8u))), "r"((v7 * 64u)), "r"((blockIdx.x * 128u)) : "memory");
          v2 = (v2 + 1u);
          if ((v2 == 4u)) {
            v2 = 0u;
            v3 = (1u - v3);
          }
        }
        asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 164896u) + (v2 * 8u))), "r"(v3) : "memory");
        v2 = (v2 + 1u);
        if ((v2 == 4u)) {
          v2 = 0u;
          v3 = (1u - v3);
        }
        asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 164896u) + (v2 * 8u))), "r"(v3) : "memory");
        v2 = (v2 + 1u);
        if ((v2 == 4u)) {
          v2 = 0u;
          v3 = (1u - v3);
        }
        asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 164896u) + (v2 * 8u))), "r"(v3) : "memory");
        v2 = (v2 + 1u);
        if ((v2 == 4u)) {
          v2 = 0u;
          v3 = (1u - v3);
        }
        asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 164896u) + (v2 * 8u))), "r"(v3) : "memory");
        v2 = (v2 + 1u);
        if ((v2 == 4u)) {
          v2 = 0u;
          v3 = (1u - v3);
        }
      }
      __syncwarp();
    } else {
      if ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) < 2u)) {
        unsigned v8 = 0u;
        asm volatile("{\n\t.reg .b32 rx;\n\t.reg .pred px;\n\telect.sync rx|px, 0xffffffff;\n\t@px mov.u32 %0, 1;\n\t}" : "+r"(v8) :  : "memory");
        if ((0u < v8)) {
          unsigned v4 = 0u;
          unsigned v5 = 0u;
          {
            asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 164864u) + (v4 * 8u))), "r"(v5) : "memory");
            asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
            asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::1.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"(v0), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v4 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 0ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v4 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 0ull)), "r"(136316048u), "r"(0u) : "memory");
            asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::1.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"(v0), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v4 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 2ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v4 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 2ull)), "r"(136316048u), "r"(1u) : "memory");
            asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::1.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"(v0), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v4 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 4ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v4 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 4ull)), "r"(136316048u), "r"(1u) : "memory");
            asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::1.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"(v0), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v4 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 6ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v4 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 6ull)), "r"(136316048u), "r"(1u) : "memory");
            asm volatile("tcgen05.commit.cta_group::1.mbarrier::arrive::one.shared::cluster.b64 [%0];" :  : "r"(((gpu_smem_base + 164896u) + (v4 * 8u))) : "memory");
            v4 = (v4 + 1u);
            if ((v4 == 4u)) {
              v4 = 0u;
              v5 = (1u - v5);
            }
          }
          for (unsigned v9 = 1u; v9 < ((63u + K) / 64u); ++v9) {
            asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"(((gpu_smem_base + 164864u) + (v4 * 8u))), "r"(v5) : "memory");
            asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
            asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::1.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"(v0), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v4 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 0ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v4 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 0ull)), "r"(136316048u), "r"(1u) : "memory");
            asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::1.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"(v0), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v4 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 2ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v4 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 2ull)), "r"(136316048u), "r"(1u) : "memory");
            asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::1.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"(v0), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v4 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 4ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v4 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 4ull)), "r"(136316048u), "r"(1u) : "memory");
            asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::1.kind::f16 [%0], %1, %2, %3, p;\n\t}" :  : "r"(v0), "l"(((static_cast<unsigned long long>(((((gpu_smem_base + 33792u) + (v4 * 32768u)) & 262143u) >> 4u)) | 4611756662049472512ull) + 6ull)), "l"(((static_cast<unsigned long long>((((((gpu_smem_base + 33792u) + (v4 * 32768u)) + 16384u) & 262143u) >> 4u)) | 4611756662049472512ull) + 6ull)), "r"(136316048u), "r"(1u) : "memory");
            asm volatile("tcgen05.commit.cta_group::1.mbarrier::arrive::one.shared::cluster.b64 [%0];" :  : "r"(((gpu_smem_base + 164896u) + (v4 * 8u))) : "memory");
            v4 = (v4 + 1u);
            if ((v4 == 4u)) {
              v4 = 0u;
              v5 = (1u - v5);
            }
          }
          asm volatile("tcgen05.commit.cta_group::1.mbarrier::arrive::one.shared::cluster.b64 [%0];" :  : "r"((gpu_smem_base + 8u)) : "memory");
        }
        __syncwarp();
      }
      asm volatile("bar.sync %0, %1;" :  : "r"(1u), "r"(96u) : "memory");
    }
    asm volatile("bar.sync %0, %1;" :  : "r"(2u), "r"(128u) : "memory");
  } else {
    asm volatile("{\n\t.reg .pred P1;\n\tLAB_WAIT:\n\tmbarrier.try_wait.parity.shared::cta.b64 P1, [%0], %1;\n\t@P1 bra DONE;\n\tbra LAB_WAIT;\n\tDONE:\n\t}" :  : "r"((gpu_smem_base + 8u)), "r"(0u) : "memory");
    asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
    unsigned v1 = 0u;
    for (unsigned v10 = 0u; v10 < 4u; ++v10) {
      float v11;
      float v12;
      float v13;
      float v14;
      float v15;
      float v16;
      float v17;
      float v18;
      float v19;
      float v20;
      float v21;
      float v22;
      float v23;
      float v24;
      float v25;
      float v26;
      float v27;
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
      __syncwarp();
      asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
      asm volatile("tcgen05.ld.sync.aligned.32x32b.x8.b32 {%0, %1, %2, %3, %4, %5, %6, %7}, [%8];" : "=f"(v11), "=f"(v12), "=f"(v13), "=f"(v14), "=f"(v15), "=f"(v16), "=f"(v17), "=f"(v18) : "r"((((v0 + (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 32u) << 16u)) + (v10 * 32u)) + 0u)) : "memory");
      asm volatile("tcgen05.ld.sync.aligned.32x32b.x8.b32 {%0, %1, %2, %3, %4, %5, %6, %7}, [%8];" : "=f"(v19), "=f"(v20), "=f"(v21), "=f"(v22), "=f"(v23), "=f"(v24), "=f"(v25), "=f"(v26) : "r"((((v0 + (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 32u) << 16u)) + (v10 * 32u)) + 8u)) : "memory");
      asm volatile("tcgen05.ld.sync.aligned.32x32b.x8.b32 {%0, %1, %2, %3, %4, %5, %6, %7}, [%8];" : "=f"(v27), "=f"(v28), "=f"(v29), "=f"(v30), "=f"(v31), "=f"(v32), "=f"(v33), "=f"(v34) : "r"((((v0 + (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 32u) << 16u)) + (v10 * 32u)) + 16u)) : "memory");
      asm volatile("tcgen05.ld.sync.aligned.32x32b.x8.b32 {%0, %1, %2, %3, %4, %5, %6, %7}, [%8];" : "=f"(v35), "=f"(v36), "=f"(v37), "=f"(v38), "=f"(v39), "=f"(v40), "=f"(v41), "=f"(v42) : "r"((((v0 + (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 32u) << 16u)) + (v10 * 32u)) + 24u)) : "memory");
      asm volatile("tcgen05.wait::ld.sync.aligned;" :  :  : "memory");
      if (((threadIdx.x % 32u) == 0u)) {
        asm volatile("cp.async.bulk.wait_group.read 1;" :  :  : "memory");
      }
      __syncwarp();
      const unsigned v43 = (((gpu_smem_base + 1024u) + ((((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 2u) + v1) * 4096u)) + ((threadIdx.x % 32u) * 128u));
      const unsigned v44 = ((threadIdx.x % 32u) & 7u);
      asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v43 + ((0u ^ v44) << 4u))), "f"(v11), "f"(v12), "f"(v13), "f"(v14) : "memory");
      asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v43 + ((1u ^ v44) << 4u))), "f"(v15), "f"(v16), "f"(v17), "f"(v18) : "memory");
      asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v43 + ((2u ^ v44) << 4u))), "f"(v19), "f"(v20), "f"(v21), "f"(v22) : "memory");
      asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v43 + ((3u ^ v44) << 4u))), "f"(v23), "f"(v24), "f"(v25), "f"(v26) : "memory");
      asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v43 + ((4u ^ v44) << 4u))), "f"(v27), "f"(v28), "f"(v29), "f"(v30) : "memory");
      asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v43 + ((5u ^ v44) << 4u))), "f"(v31), "f"(v32), "f"(v33), "f"(v34) : "memory");
      asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v43 + ((6u ^ v44) << 4u))), "f"(v35), "f"(v36), "f"(v37), "f"(v38) : "memory");
      asm volatile("st.shared.v4.f32 [%0], {%1, %2, %3, %4};" :  : "r"((v43 + ((7u ^ v44) << 4u))), "f"(v39), "f"(v40), "f"(v41), "f"(v42) : "memory");
      asm volatile("fence.proxy.async.shared::cta;" :  :  : "memory");
      __syncwarp();
      const unsigned v45 = ((gpu_smem_base + 1024u) + ((((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 2u) + v1) * 4096u));
      const unsigned v46 = ((blockIdx.y * 128u) + ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) % 4u) * 32u));
      if (((threadIdx.x % 32u) == 0u)) {
        asm volatile("cp.async.bulk.tensor.2d.global.shared::cta.bulk_group [%0, {%2, %3}], [%1];" :  : "l"(reinterpret_cast<unsigned long long>(&C_map)), "r"(v45), "r"(((blockIdx.x * 128u) + (v10 * 32u))), "r"(v46) : "memory");
        asm volatile("cp.async.bulk.commit_group;" :  :  : "memory");
      }
      __syncwarp();
      v1 = (v1 + 1u);
      if ((v1 == 2u)) {
        v1 = 0u;
      }
    }
    if (((threadIdx.x % 32u) == 0u)) {
      asm volatile("cp.async.bulk.wait_group 0;" :  :  : "memory");
    }
    __syncwarp();
  }
  __syncthreads();
  if ((threadIdx.x == 0u)) {
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 164864u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 164872u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 164880u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 164888u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 164896u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 164904u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 164912u)) : "memory");
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 164920u)) : "memory");
  }
  if ((threadIdx.x == 0u)) {
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" :  : "r"((gpu_smem_base + 8u)) : "memory");
  }
  asm volatile("tcgen05.fence::before_thread_sync;" :  :  : "memory");
  __syncthreads();
  asm volatile("tcgen05.fence::after_thread_sync;" :  :  : "memory");
  if ((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) == 0u)) {
    asm volatile("tcgen05.dealloc.cta_group::1.sync.aligned.b32 %0, %1;" :  : "r"(v0), "r"(128u) : "memory");
  }
}

// Launches tinygemm on `stream`, encoding its tensor maps as its parameter types require.
extern "C" cudaError_t tinygemm_launch(const __nv_bfloat16* A, const __nv_bfloat16* B, float* C, unsigned M, unsigned N, unsigned K, cudaStream_t stream) {
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
  const cudaError_t status = cudaFuncSetAttribute(reinterpret_cast<const void*>(tinygemm), cudaFuncAttributeMaxDynamicSharedMemorySize, 164928);
  if (status != cudaSuccess) {
    return status;
  }
  void* args[] = {&A_map, &B_map, &C_map, &M, &N, &K};
  return cudaLaunchKernel(reinterpret_cast<const void*>(tinygemm), dim3(((N + 127u) / 128u), ((M + 127u) / 128u)), dim3(256u), args, 164928u, stream);
}
