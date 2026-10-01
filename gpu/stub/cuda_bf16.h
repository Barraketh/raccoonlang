// Stub for check.sh: bf16, and its conversion from float, which a kernel writing bf16 output uses (`static_cast`).
#pragma once
struct __nv_bfloat16 {
  unsigned short bits;
  __nv_bfloat16() = default;
  __nv_bfloat16(float);
};
__nv_bfloat16 __float2bfloat16(float);
