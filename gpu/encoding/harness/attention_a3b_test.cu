// Runs examples/attention_a3b.rac's kernels (A3b: a correction warpgroup, a lazy rescale, an emulated exponential and a
// register split, gpu/encoding/A3B.md), `attention_a3b` (non-causal, O in f32) and `attention_a3b_causal` (causal, O in
// bf16), under the attention harness (`attention_harness.h`). Needs an sm_100a GPU:
//
//   gpu/gen.sh gpu/encoding/examples/attention_a3b.rac > attention_a3b.cu
//   nvcc -std=c++17 -O2 -Xcompiler -pthread -gencode arch=compute_100a,code=sm_100a -o attention_a3b_test \
//     attention_a3b.cu gpu/encoding/harness/attention_a3b_test.cu -lcuda
//   ./attention_a3b_test
#define ATTENTION_KERNEL attention_a3b
#include "attention_harness.h"
