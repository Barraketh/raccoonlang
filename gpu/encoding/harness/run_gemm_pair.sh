#!/bin/sh
# The persistent pair GEMM on hardware: its correctness run, then its timing run (gemm_pair_test.cu).
#
#   gpu/encoding/harness/run_gemm_pair.sh gen DIR    here: hw.sh's bundle in DIR, every example's generated CUDA
#                                                    (kernels/gemm_pair.cu among them), the harnesses and this script,
#                                                    so the box needs no JVM (needs $RACCOON, as gpu/gen.sh)
#   DIR/run_gemm_pair.sh run [runs [n …]]            on the box: build kernels/gemm_pair.cu with harness/gemm_pair_test.cu,
#                                                    check it, then time it: the median of `runs` runs (100) at each n³
#                                                    (8192³ and 4096³), the SM clock recorded before and after
#
# The box needs nvcc (CUDA 12.9, as nvidia/cuda:12.9.1-devel-ubuntu22.04 has it), the driver's libcuda and an sm_100a
# GPU; nothing else. Logs and the binary go to $OUT (default: a fresh directory under /tmp).
here=$(cd "$(dirname "$0")" && pwd)

case $1 in
  gen)
    exec sh "$here/hw.sh" gen "${2:?usage: run_gemm_pair.sh gen DIR}" ;;
  run)
    shift
    out=${OUT:-$(mktemp -d /tmp/gemm_pair.XXXXXX)}
    mkdir -p "$out"
    export CUDA_VISIBLE_DEVICES=${CUDA_VISIBLE_DEVICES:-0}
    clocks() { nvidia-smi --query-gpu=clocks.sm,clocks.mem,power.draw,temperature.gpu --format=csv,noheader 2>/dev/null | sed "s/^/$1: /"; }
    nvidia-smi --query-gpu=name,driver_version,clocks.max.sm --format=csv,noheader 2>/dev/null | sed 's/^/gpu: /'
    nvcc --version 2>/dev/null | tail -1 | sed 's/^/nvcc: /'
    # -arch=sm_100a would compile for plain sm_100, which has no tcgen05 (gpu/DESIGN.md §7).
    if ! nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a -o "$out/gemm_pair_test" \
        "$here/kernels/gemm_pair.cu" "$here/harness/gemm_pair_test.cu" -lcuda > "$out/build.log" 2>&1; then
      cat "$out/build.log"; echo "BUILD FAILED ($out/build.log)"; exit 1
    fi
    echo "######## correctness"
    { "$out/gemm_pair_test"; echo $? > "$out/correctness.exit"; } 2>&1 | tee "$out/correctness.log"
    [ "$(cat "$out/correctness.exit")" = 0 ] || { echo "FAILED: not timed (logs: $out)"; exit 1; }
    echo "######## timing"
    clocks before
    { "$out/gemm_pair_test" time "$@"; echo $? > "$out/timing.exit"; } 2>&1 | tee "$out/timing.log"
    clocks after
    echo "logs: $out"
    exit "$(cat "$out/timing.exit")" ;;
  *)
    sed -n '2,12p' "$0"; exit 2 ;;
esac
