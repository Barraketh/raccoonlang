#!/bin/sh
# Checks the spike: every example must generate code, every file under rejected/ must fail with the diagnostic
# kind named on its `// expect:` line (with a message that mentions the text of its `// mentions:` line, if it has
# one), every mutant in a rejected/*_mutants.py table must be refused as the table says (see mutate.py), and every file
# under checks/ and proofs/ must check without a diagnostic, and every model check (`*_model.py` under
# encoding/harness/) must pass. The same holds of encoding/ (the next core,
# encoding/README.md), whose examples/, rejected/ and checks/ are laid out as these.
#
# The per-file checks run in parallel, one per processor (CHECK_JOBS overrides the count), and report in a fixed
# order; each mutant table then runs its mutants in parallel itself.
#
# When the CUDA toolkit's container is there (toolkit/cuda.sh), every kernel an example of encoding/ generates is also
# compiled for sm_100a and its registers judged (toolkit/registers.py): within its budget, and no spill. So are the
# mutant tables' spill mutants. Without the container both are skipped, which the report's first line says.
here=$(cd "$(dirname "$0")" && pwd)
run() { ${RACCOON:?set RACCOON to a raccoon launcher} --prelude "$here/Prelude.rac" --root "$here" "$@"; }
# Generated C++ is compiled against stub headers when a host clang++ is available; each inline assembly statement is
# first replaced by stub calls over its operands (`stub/asm_calls.py`).
cxx() {
  command -v clang++ >/dev/null || return 0
  python3 "$here/stub/asm_calls.py" | clang++ -std=c++17 -fsyntax-only -Wall -Wno-unused-parameter -Wno-parentheses-equality -Werror \
    -I "$here/stub" -include "$here/stub/cuda_stub.h" -x c++ -
}
# The register check of generated kernels, when the toolkit is there.
registers() {
  [ -n "$CUDA_TOOLKIT" ] || return 0
  python3 "$here/toolkit/registers.py"
}
# A file's path below gpu/, which names it in the report.
name() { printf '%s' "${1#"$here"/}"; }

# One check of one file, by kind: prints its report and fails when the check fails.
one() {
  kind=$1; f=$2
  case $kind in
    example)
      out=$(run --raw "$f" 2>&1)
      if printf '%s' "$out" | grep -q "error:"; then echo "FAIL $(name "$f")"; printf '%s\n' "$out"; return 1
      elif ! printf '%s' "$out" | cxx; then echo "FAIL $(name "$f"): generated C++ does not compile"; return 1
      else echo "ok   $(name "$f")"
        case $f in "$here"/encoding/examples/*) printf '%s' "$out" | registers || return 1 ;; esac
      fi ;;
    rejected)
      want=$(sed -n 's#^// expect: ##p' "$f" | head -1)
      mentions=$(sed -n 's#^// mentions: ##p' "$f" | head -1)
      got=$(run --json "$f" 2>/dev/null | MENTIONS="$mentions" python3 -c 'import json,os,sys; d=json.load(sys.stdin); print(" ".join(x["kind"] for x in d if os.environ["MENTIONS"] in x["message"]))' 2>/dev/null || echo crashed)
      case " $got " in
        *" $want "*) echo "ok   $(name "$f") -> $got" ;;
        *) echo "FAIL $(name "$f"): expected $want${mentions:+ mentioning $mentions}, got '$got'"; return 1 ;;
      esac ;;
    # The checkers' unit tests (theorems about hand-built kernels, proved by evaluation) and their soundness proofs
    # against gpu/Spec.rac.
    clean)
      got=$(run --json "$f" 2>/dev/null | python3 -c 'import json,sys; [print("L%d %s: %s" % (x["startLine"], x["kind"], x["message"])) for x in json.load(sys.stdin)]' 2>/dev/null || echo crashed)
      if [ -z "$got" ]; then echo "ok   $(name "$f")"; else echo "FAIL $(name "$f")"; printf '%s\n' "$got"; return 1; fi ;;
    # Hardware test harnesses are host code: the same stubs check them.
    harness)
      if command -v clang++ >/dev/null && ! clang++ -std=c++17 -fsyntax-only -Wall -Werror -I "$here/stub" \
          -include "$here/stub/cuda_stub.h" -x c++ "$f"; then
        echo "FAIL $(name "$f") does not compile"; return 1
      else echo "ok   $(name "$f")"; fi ;;
    # The FA4 comparison needs a GPU and PyTorch, so it is only compiled.
    python)
      if python3 -c 'import sys; compile(open(sys.argv[1]).read(), sys.argv[1], "exec")' "$f"; then echo "ok   $(name "$f")"
      else echo "FAIL $(name "$f") does not compile"; return 1; fi ;;
    # Model checks (`*_model.py`) run, and fail with their program.
    model)
      if out=$(python3 "$f" 2>&1); then echo "ok   $(name "$f")"
      else echo "FAIL $(name "$f")"; printf '%s\n' "$out"; return 1; fi ;;
  esac
}

# `check.sh --task DIR INDEX KIND FILE`: one check, its report in DIR/INDEX.out, and DIR/INDEX.fail if it failed.
if [ "$1" = --task ]; then
  one "$4" "$5" > "$2/$3.out" 2>&1 || touch "$2/$3.fail"
  exit 0
fi

tasks() {
  for f in "$here"/examples/*.rac "$here"/encoding/examples/*.rac; do [ -e "$f" ] && echo "example $f"; done
  for f in "$here"/rejected/*.rac "$here"/encoding/rejected/*.rac; do [ -e "$f" ] && echo "rejected $f"; done
  for f in "$here"/checks/*.rac "$here"/proofs/*.rac "$here"/encoding/checks/*.rac; do [ -e "$f" ] && echo "clean $f"; done
  for f in "$here"/harness/*.cu "$here"/encoding/harness/*.cu; do [ -e "$f" ] && echo "harness $f"; done
  for f in "$here"/encoding/harness/*.py; do
    case $f in *_model.py) echo "model $f" ;; *) [ -e "$f" ] && echo "python $f" ;; esac
  done
}
if "$here/toolkit/cuda.sh" true < /dev/null > /dev/null 2>&1; then export CUDA_TOOLKIT=yes
else echo "skipped: no CUDA toolkit"; fi
status=0
results=$(mktemp -d)
tasks | awk '{ print NR, $0 }' > "$results/tasks"
jobs=${CHECK_JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)}
xargs -P "$jobs" -L 1 sh "$here/check.sh" --task "$results" < "$results/tasks"
n=$(wc -l < "$results/tasks")
i=1
while [ "$i" -le "$n" ]; do
  cat "$results/$i.out"
  [ -e "$results/$i.fail" ] && status=1
  i=$((i + 1))
done
rm -r "$results"
# So are the hardware probes, whose shared header's inline assembly is rewritten as a generated kernel's is.
if command -v clang++ >/dev/null; then
  probes=$(mktemp -d)
  python3 "$here/stub/asm_calls.py" < "$here/probes/probe.h" > "$probes/probe.h"
  for p in "$here"/probes/*.cu; do
    cp "$p" "$probes/"
    if clang++ -std=c++17 -fsyntax-only -Wall -Werror -I "$here/stub" -include "$here/stub/cuda_stub.h" -x c++ \
        "$probes/$(basename "$p")"; then echo "ok   probes/$(basename "$p")"
    else echo "FAIL probes/$(basename "$p") does not compile"; status=1; fi
  done
  rm -r "$probes"
fi
for t in "$here"/rejected/*_mutants.py "$here"/encoding/rejected/*_mutants.py; do
  [ -e "$t" ] || continue
  python3 "$here/mutate.py" "$t" || status=1
done
exit $status
