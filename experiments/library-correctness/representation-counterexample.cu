extern "C" __global__ void __launch_bounds__(32, 1) divergent_barrier() {
  if ((threadIdx.x == 0u)) {
    __syncthreads();
  }
}
