// Stub for check.sh: the driver API's tensor maps.
#pragma once
struct CUtensorMap { alignas(64) unsigned long long opaque[16]; };
typedef unsigned long long cuuint64_t;
typedef unsigned int cuuint32_t;
enum CUresult { CUDA_SUCCESS = 0, CUDA_ERROR_INVALID_VALUE = 1 };
enum CUtensorMapDataType {
  CU_TENSOR_MAP_DATA_TYPE_UINT8 = 0,
  CU_TENSOR_MAP_DATA_TYPE_UINT32 = 2,
  CU_TENSOR_MAP_DATA_TYPE_UINT64 = 4,
  CU_TENSOR_MAP_DATA_TYPE_FLOAT32 = 7,
  CU_TENSOR_MAP_DATA_TYPE_BFLOAT16 = 9
};
enum CUtensorMapInterleave { CU_TENSOR_MAP_INTERLEAVE_NONE = 0 };
enum CUtensorMapSwizzle { CU_TENSOR_MAP_SWIZZLE_128B = 3 };
enum CUtensorMapL2promotion { CU_TENSOR_MAP_L2_PROMOTION_L2_256B = 3 };
enum CUtensorMapFloatOOBfill { CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE = 0 };
CUresult cuTensorMapEncodeTiled(CUtensorMap *tensorMap, CUtensorMapDataType tensorDataType, cuuint32_t tensorRank,
                                void *globalAddress, const cuuint64_t *globalDim, const cuuint64_t *globalStrides,
                                const cuuint32_t *boxDim, const cuuint32_t *elementStrides, CUtensorMapInterleave interleave,
                                CUtensorMapSwizzle swizzle, CUtensorMapL2promotion l2Promotion,
                                CUtensorMapFloatOOBfill oobFill);
