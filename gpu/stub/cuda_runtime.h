// Stub for check.sh: the runtime API that generated launchers and the harnesses use.
#include <cstddef>
enum cudaError_t { cudaSuccess = 0, cudaErrorInvalidValue = 1 };
enum cudaFuncAttribute { cudaFuncAttributeMaxDynamicSharedMemorySize = 8 };
enum cudaMemcpyKind { cudaMemcpyHostToDevice = 1, cudaMemcpyDeviceToHost = 2 };
typedef struct CUstream_st *cudaStream_t;
typedef struct CUevent_st *cudaEvent_t;
struct dim3 {
  unsigned x, y, z;
  dim3(unsigned x = 1, unsigned y = 1, unsigned z = 1) : x(x), y(y), z(z) {}
};
cudaError_t cudaFuncSetAttribute(const void *func, cudaFuncAttribute attr, int value);
cudaError_t cudaLaunchKernel(const void *func, dim3 gridDim, dim3 blockDim, void **args, size_t sharedMem,
                             cudaStream_t stream);
cudaError_t cudaMalloc(void **ptr, size_t size);
template <class T> cudaError_t cudaMalloc(T **ptr, size_t size) { return cudaMalloc(reinterpret_cast<void **>(ptr), size); }
cudaError_t cudaFree(void *ptr);
cudaError_t cudaMemcpy(void *dst, const void *src, size_t count, cudaMemcpyKind kind);
cudaError_t cudaMemset(void *ptr, int value, size_t count);
cudaError_t cudaDeviceSynchronize();
const char *cudaGetErrorString(cudaError_t error);
cudaError_t cudaEventCreate(cudaEvent_t *event);
cudaError_t cudaEventRecord(cudaEvent_t event, cudaStream_t stream = 0);
cudaError_t cudaEventSynchronize(cudaEvent_t event);
cudaError_t cudaEventElapsedTime(float *ms, cudaEvent_t start, cudaEvent_t end);
cudaError_t cudaEventDestroy(cudaEvent_t event);
