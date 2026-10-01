// Runs examples/attention.rac's kernels, `attention` (non-causal, O in f32: A1's, for any `seq` since A2) and
// `attention_causal` (causal, O in bf16: A2), under the attention harness (`attention_harness.h`). Needs an sm_100a
// GPU:
//
//   gpu/gen.sh gpu/encoding/examples/attention.rac > attention.cu
//   nvcc -std=c++17 -O2 -Xcompiler -pthread -gencode arch=compute_100a,code=sm_100a -o attention_test attention.cu \
//     gpu/encoding/harness/attention_test.cu -lcuda
//   ./attention_test
#define ATTENTION_KERNEL attention
#include "attention_harness.h"
