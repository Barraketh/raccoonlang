#!/bin/sh
# The persistent pair GEMM on hardware: its correctness run, then its timing run (gemm_pair_test.cu).
#
#   gpu/encoding/harness/run_gemm_pair.sh gen DIR    here: hw.sh's bundle in DIR, every example's generated CUDA
#                                                    (kernels/gemm_pair.cu among them), the harnesses and this script,
#                                                    so the box needs no JVM (needs $RACCOON, as gpu/gen.sh)
#   DIR/run_gemm_pair.sh run [runs [n …]]            on the box: build kernels/gemm_pair.cu with the harness, check
#                                                    it, then time it: the median of `runs` runs (100) at each n³
#                                                    (8192³ and 4096³), the SM clock recorded before and after
#
# The box needs nvcc (CUDA 12.9, as nvidia/cuda:12.9.1-devel-ubuntu22.04 has it), the driver's libcuda, GNU timeout
# and an sm_100a GPU. Each run stops after $HW_TIMEOUT seconds (default 900), so a deadlock does not hang the box. Logs
# and the binary go to $OUT (default: a fresh directory under /tmp).
here=$(cd "$(dirname "$0")" && pwd)

case $1 in
  gen)
    exec sh "$here/hw.sh" gen "${2:?usage: run_gemm_pair.sh gen DIR}" ;;
  run)
    shift
    out=${OUT:-$(mktemp -d /tmp/gemm_pair.XXXXXX)}
    mkdir -p "$out"
    export CUDA_VISIBLE_DEVICES=${CUDA_VISIBLE_DEVICES:-0}
    limit=${HW_TIMEOUT:-900}
    smi() { nvidia-smi -i "$CUDA_VISIBLE_DEVICES" --format=csv,noheader --query-gpu="$1" 2>/dev/null | sed "s/^/$2: /"; }
    # Runs the harness with arguments under the time limit, logging to $out/$1.log; its exit code, or TIMEOUT, in $code.
    harness() {
      log=$1; shift
      { timeout -k 10 "$limit" "$out/gemm_pair_test" "$@"; echo $? > "$out/$log.exit"; } 2>&1 | tee "$out/$log.log"
      code=$(cat "$out/$log.exit"); [ "$code" = 124 ] && code=TIMEOUT
    }
    smi name,driver_version,clocks.max.sm gpu
    nvcc --version 2>/dev/null | tail -1 | sed 's/^/nvcc: /'
    # -arch=sm_100a would compile for plain sm_100, which has no tcgen05 (gpu/DESIGN.md §7).
    if ! nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a -o "$out/gemm_pair_test" \
        "$here/kernels/gemm_pair.cu" "$here/harness/gemm_pair_test.cu" -lcuda > "$out/build.log" 2>&1; then
      cat "$out/build.log"; echo "BUILD FAILED ($out/build.log)"; exit 1
    fi
    echo "######## correctness"
    harness correctness
    [ "$code" = 0 ] || { echo "FAILED ($code): not timed (logs: $out)"; exit 1; }
    echo "######## timing"
    smi clocks.sm,clocks.mem,power.draw,temperature.gpu before
    harness timing time "$@"
    smi clocks.sm,clocks.mem,power.draw,temperature.gpu after
    echo "timing: $code (logs: $out)"
    [ "$code" = 0 ] ;;
  *)
    sed -n '2,13p' "$0"; exit 2 ;;
esac
