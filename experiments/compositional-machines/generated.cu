extern "C" __global__ void __launch_bounds__(512, 1) compositional_protocol(unsigned n, bool flag, unsigned* __restrict__ out) {
  __shared__ unsigned v0[128];
  __shared__ unsigned v1[128];
  unsigned v2 = 0u;
  unsigned v3 = 0u;
  if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 0u)) {
    v0[(threadIdx.x % 128u)] = 1u;
  }
  if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 1u)) {
    v1[(threadIdx.x % 128u)] = 1u;
  }
  __syncthreads();
  for (unsigned v4 = 0u; v4 < n; ++v4) {
    if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 0u)) {
      asm volatile("setmaxnreg.inc.sync.aligned.u32 192;" :  :  : "memory");
      for (unsigned v5 = 0u; v5 < n; ++v5) {
        if (flag) {
          if ((v5 == 0u)) {
            v2 = (v2 + v0[(v5 % 128u)]);
            v2 = (v2 + v0[(v5 % 128u)]);
          } else {
            v2 = (v2 + v0[(v5 % 128u)]);
          }
        } else {
          v2 = (v2 + v0[(v5 % 128u)]);
        }
      }
    }
    if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 1u)) {
      asm volatile("setmaxnreg.inc.sync.aligned.u32 192;" :  :  : "memory");
      for (unsigned v6 = 0u; v6 < n; ++v6) {
        if (flag) {
          if ((v6 == 0u)) {
            v3 = (v3 + v1[(v6 % 128u)]);
            v3 = (v3 + v1[(v6 % 128u)]);
          } else {
            v3 = (v3 + v1[(v6 % 128u)]);
          }
        } else {
          v3 = (v3 + v1[(v6 % 128u)]);
        }
      }
    }
    if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 2u)) {
      asm volatile("setmaxnreg.dec.sync.aligned.u32 72;" :  :  : "memory");
    }
    if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 3u)) {
      asm volatile("setmaxnreg.dec.sync.aligned.u32 56;" :  :  : "memory");
    }
    __syncthreads();
    if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 0u)) {
      asm volatile("setmaxnreg.dec.sync.aligned.u32 128;" :  :  : "memory");
    }
    if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 1u)) {
      asm volatile("setmaxnreg.dec.sync.aligned.u32 128;" :  :  : "memory");
    }
    if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 2u)) {
      asm volatile("setmaxnreg.inc.sync.aligned.u32 128;" :  :  : "memory");
    }
    if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 3u)) {
      asm volatile("setmaxnreg.inc.sync.aligned.u32 128;" :  :  : "memory");
    }
    __syncthreads();
    if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 0u)) {
      v0[(threadIdx.x % 128u)] = 2u;
    }
    if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 1u)) {
      v1[(threadIdx.x % 128u)] = 2u;
    }
    __syncthreads();
  }
  if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 0u)) {
    out[threadIdx.x] = v2;
  } else {
    if (((__shfl_sync(0xffffffffu, threadIdx.x / 32u, 0) / 4u) == 1u)) {
      out[threadIdx.x] = v3;
    } else {
      out[threadIdx.x] = 0u;
    }
  }
}
