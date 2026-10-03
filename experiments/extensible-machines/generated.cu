extern "C" __global__ void __launch_bounds__(64, 1) machine_pipeline_core(const unsigned* __restrict__ A, const unsigned* __restrict__ B, unsigned* __restrict__ C, unsigned M, unsigned N, unsigned K) {
  __shared__ unsigned v0[64];
  __shared__ unsigned v1[64];
  unsigned v2 = 0u;
  unsigned v3 = 0u;
  for (unsigned v4 = 0u; v4 < K; ++v4) {
    v0[threadIdx.x] = (v4 + 1u);
    __syncthreads();
    const unsigned v5 = v0[((((threadIdx.x / 8u) * 8u) + (threadIdx.x % 8u)) % 64u)];
    const unsigned v6 = v2;
    v2 = (v6 + v5);
    const unsigned v7 = v0[((((threadIdx.x / 8u) * 8u) + (threadIdx.x % 8u)) % 64u)];
    const unsigned v8 = v2;
    v2 = (v8 + v7);
    __syncthreads();
    v1[threadIdx.x] = (v4 + 1u);
    __syncthreads();
    const unsigned v9 = v1[((((threadIdx.x / 8u) * 8u) + (threadIdx.x % 8u)) % 64u)];
    const unsigned v10 = v3;
    v3 = (v10 + v9);
    const unsigned v11 = v1[((((threadIdx.x / 8u) * 8u) + (threadIdx.x % 8u)) % 64u)];
    const unsigned v12 = v3;
    v3 = (v12 + v11);
    __syncthreads();
  }
  const unsigned v13 = v2;
  const unsigned v14 = v3;
  if (((((blockIdx.y * 8u) + (threadIdx.x / 8u)) < M) && (((blockIdx.x * 8u) + (threadIdx.x % 8u)) < N))) {
    C[((((blockIdx.y * 8u) + (threadIdx.x / 8u)) * N) + ((blockIdx.x * 8u) + (threadIdx.x % 8u)))] = (v13 + v14);
  }
}
