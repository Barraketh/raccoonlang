#!/bin/sh
# One hardware session for gpu/encoding: every harness, built against its generated kernels, then the probes.
#
#   gpu/encoding/harness/hw.sh gen DIR    here: generate every example's CUDA into DIR, with the harnesses, their run
#                                         scripts and the probes, so that the GPU box needs no JVM (needs $RACCOON)
#   DIR/hw.sh run [name …]                on an sm_100a box with nvcc (CUDA 12.9) and GNU timeout: build and run every
#                                         harness, or those named, then the probes; print a summary
#
# Logs and binaries go to $OUT (default: a fresh directory under /tmp). Each harness runs under $HW_TIMEOUT seconds
# (default 900).
#
# The table: a harness's name, then the examples whose generated CUDA it links, in order.
suites='attention:attention
attention_pingpong:attention_pingpong
attention_a3b:attention_a3b
paged_attention:paged_attention
paged_decode:paged_append paged_decode paged_combine
tinygemm:tinygemm
tinygemm_pair:tinygemm_pair
gemm_pair:gemm_pair'

here=$(cd "$(dirname "$0")" && pwd)

case $1 in
  gen)
    dir=${2:?usage: hw.sh gen DIR}
    gpu=$(cd "$here/../.." && pwd)
    # A bundle's kernels are this checkout's: none is kept from an earlier gen.
    rm -rf "$dir/kernels"
    mkdir -p "$dir/kernels" "$dir/harness" "$dir/probes"
    printf '%s\n' "$suites" | while IFS=: read -r name examples; do
      for x in $examples; do
        [ -e "$dir/kernels/$x.cu" ] && continue
        echo "gen  $x"
        "$gpu/gen.sh" "$gpu/encoding/examples/$x.rac" > "$dir/kernels/$x.cu" || { echo "FAIL gen $x"; exit 1; }
      done
    done || exit 1
    cp "$here"/*.cu "$here"/*.h "$dir/harness/"
    cp "$gpu"/probes/*.cu "$gpu"/probes/*.h "$gpu"/probes/run.sh "$dir/probes/"
    cp "$here/hw.sh" "$here"/run_*.sh "$dir/"
    echo "bundle: $dir (copy it to the box, then: sh hw.sh run)"
    ;;
  run)
    shift
    out=${OUT:-$(mktemp -d /tmp/hw.XXXXXX)}
    mkdir -p "$out"
    export CUDA_VISIBLE_DEVICES=${CUDA_VISIBLE_DEVICES:-0}
    limit=${HW_TIMEOUT:-900}
    nvidia-smi -i "$CUDA_VISIBLE_DEVICES" --query-gpu=name,driver_version,clocks.max.sm --format=csv,noheader 2>/dev/null | sed 's/^/gpu: /'
    nvcc --version 2>/dev/null | tail -1 | sed 's/^/nvcc: /'
    summary=$(mktemp)
    printf '%s\n' "$suites" | while IFS=: read -r name examples; do
      if [ $# -gt 0 ]; then
        hit=no; for want in "$@"; do [ "$want" = "$name" ] && hit=yes; done
        [ $hit = yes ] || continue
      fi
      echo "######## $name"
      srcs=""; for x in $examples; do srcs="$srcs $here/kernels/$x.cu"; done
      if ! nvcc -std=c++17 -O2 -Xcompiler -pthread -gencode arch=compute_100a,code=sm_100a -o "$out/$name" \
          $srcs "$here/harness/${name}_test.cu" -lcuda > "$out/$name.build.log" 2>&1; then
        tail -20 "$out/$name.build.log"
        echo "$name|BUILD FAILED|$out/$name.build.log" >> "$summary"
        continue
      fi
      { timeout -k 10 "$limit" "$out/$name"; echo $? > "$out/$name.exit"; } 2>&1 | tee "$out/$name.log"
      code=$(cat "$out/$name.exit")
      [ "$code" = 124 ] && code="TIMEOUT"
      echo "$name|exit $code|$out/$name.log" >> "$summary"
    done
    if [ $# -eq 0 ]; then
      echo "######## probes"
      OUT="$out/probes" sh "$here/probes/run.sh" 2>&1 | tee "$out/probes.log" | tail -8
    fi
    echo
    echo "summary ($out):"
    column -t -s '|' "$summary" 2>/dev/null || cat "$summary"
    ;;
  *)
    sed -n '2,13p' "$0"; exit 2 ;;
esac
