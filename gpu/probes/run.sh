#!/bin/sh
# Builds and runs the hardware probes (README.md) on an sm_100a GPU, each under a time limit, and prints a summary.
#   gpu/probes/run.sh            all probes
#   gpu/probes/run.sh h1 h3      some, by prefix
# Binaries and full logs go to $OUT (default: a fresh directory under /tmp). Needs nvcc (CUDA 12.9) and GNU timeout.
here=$(cd "$(dirname "$0")" && pwd)
out=${OUT:-$(mktemp -d /tmp/probes.XXXXXX)}
mkdir -p "$out"
# One GPU: every case creates its own context, which is slow on a many-GPU node without persistence mode.
export CUDA_VISIBLE_DEVICES=${CUDA_VISIBLE_DEVICES:-0}
limit=${PROBE_TIMEOUT:-900}  # seconds per probe; each case also has its own 60-second alarm
probes="h1_tmem_a h2_mn_major_b h3_tmem_align h5_accum_error"
if [ $# -gt 0 ]; then
  sel=""
  for p in $probes; do for want in "$@"; do case $p in "$want"*) sel="$sel $p" ;; esac; done; done
  probes=$sel
fi
nvidia-smi --query-gpu=name,driver_version --format=csv,noheader 2>/dev/null | sed 's/^/gpu: /'
nvcc --version 2>/dev/null | tail -1 | sed 's/^/nvcc: /'
summary=""
status=0
for p in $probes; do
  echo "######## $p"
  if ! nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a "$here/$p.cu" -o "$out/$p" > "$out/$p.build.log" 2>&1; then
    cat "$out/$p.build.log"
    summary="$summary$p|BUILD FAILED|see $out/$p.build.log\n"
    status=1
    continue
  fi
  { timeout -k 10 "$limit" "$out/$p"; echo $? > "$out/$p.exit"; } 2>&1 | tee "$out/$p.log"
  code=$(cat "$out/$p.exit")
  verdict=$(sed -n 's/^-- [a-z0-9]* verdict: //p' "$out/$p.log" | tail -1)
  cases=$(grep -cE '^(PASS|FAIL|ERROR|TIMEOUT|CRASH) ' "$out/$p.log")
  passed=$(grep -cE '^PASS ' "$out/$p.log")
  [ "$code" = 124 ] && verdict="TIMED OUT after ${limit}s"
  [ -z "$verdict" ] && verdict="no verdict (exit $code; see $out/$p.log)"
  [ "$code" = 0 ] || status=1
  summary="$summary$p|$passed/$cases cases pass|exit $code: $verdict\n"
done
echo
echo "######## summary (logs in $out)"
printf '%b' "$summary" | awk -F'|' '{ printf "%-16s %-20s %s\n", $1, $2, $3 }'
exit $status
