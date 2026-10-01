// Runs examples/attention_pingpong.rac's kernels (A3a: two query tiles per CTA, gpu/encoding/A3.md),
// `attention_pingpong` (non-causal, O in f32) and `attention_pingpong_causal` (causal, O in bf16), under the attention
// harness (`attention_harness.h`), whose sizes include query tiles of a CTA on both sides of `seq`. Needs an sm_100a
// GPU:
//
//   gpu/gen.sh gpu/encoding/examples/attention_pingpong.rac > attention_pingpong.cu
//   nvcc -std=c++17 -O2 -Xcompiler -pthread -gencode arch=compute_100a,code=sm_100a -o attention_pingpong_test \
//     attention_pingpong.cu gpu/encoding/harness/attention_pingpong_test.cu -lcuda
//   ./attention_pingpong_test
#define ATTENTION_KERNEL attention_pingpong
#include "attention_harness.h"
