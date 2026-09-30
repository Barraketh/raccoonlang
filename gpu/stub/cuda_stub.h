// Just enough of CUDA for a host C++ compiler to type-check generated kernels and launchers, and the hardware test
// harnesses (`check.sh` force-includes it, and `cuda.h`, `cuda_runtime.h` and `cuda_bf16.h` here stand in for the
// real headers). Inline
// assembly becomes calls of `gpu_asm_out`/`gpu_asm_in` over its operands before checking: only ptxas can validate a
// template.
#include <algorithm>
#include <cmath>
#define __global__
#define __device__
#define __host__
#define __launch_bounds__(...)
#define __shared__
#define __restrict__
#define __grid_constant__
#define __forceinline__ inline
#define __align__(n) __attribute__((aligned(n)))
struct gpu_dim3 { unsigned x, y, z; };
extern gpu_dim3 threadIdx, blockIdx, blockDim, gridDim;
void __syncthreads();
void __syncwarp();
unsigned __shfl_sync(unsigned mask, unsigned value, int lane);
unsigned long long __cvta_generic_to_shared(const void *p);
long long clock64();
void __trap();
void __threadfence_system();
struct uint4 { unsigned x, y, z, w; };
using std::max;
template <class... T> void gpu_asm_out(T &...);
template <class... T> void gpu_asm_in(const T &...);
