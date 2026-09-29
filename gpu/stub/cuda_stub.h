// Just enough of CUDA for a host C++ compiler to type-check generated kernels (`check.sh` force-includes it). Inline
// assembly is stripped before checking: only ptxas can validate it.
#include <algorithm>
#include <cmath>
#define __global__
#define __device__
#define __shared__
#define __restrict__
#define __grid_constant__
#define __forceinline__ inline
#define __align__(n) alignas(n)
struct gpu_dim3 { unsigned x, y, z; };
extern gpu_dim3 threadIdx, blockIdx, blockDim, gridDim;
void __syncthreads();
void __syncwarp();
unsigned __shfl_sync(unsigned mask, unsigned value, int lane);
unsigned long long __cvta_generic_to_shared(const void *p);
using std::max;
