#!/bin/sh
# Checks the spike: every example must generate code, every file under rejected/ must fail with the diagnostic
# kind named on its `// expect:` line (with a message that mentions the text of its `// mentions:` line, if it has
# one), every mutant in a rejected/*_mutants.py table must be refused as the table says (see mutate.py), and every file
# under checks/ and proofs/ must check without a diagnostic. The same holds of encoding/ (the next core,
# encoding/README.md), whose examples/, rejected/ and checks/ are laid out as these.
here=$(cd "$(dirname "$0")" && pwd)
run() { ${RACCOON:?set RACCOON to a raccoon launcher} --prelude "$here/Prelude.rac" --root "$here" "$@"; }
status=0
# Generated C++ is compiled against stub headers when a host clang++ is available; each inline assembly statement is
# first replaced by stub calls over its operands (`stub/asm_calls.py`).
cxx() {
  command -v clang++ >/dev/null || return 0
  python3 "$here/stub/asm_calls.py" | clang++ -std=c++17 -fsyntax-only -Wall -Wno-unused-parameter -Wno-parentheses-equality -Werror \
    -I "$here/stub" -include "$here/stub/cuda_stub.h" -x c++ -
}
# A file's path below gpu/, which names it in the report.
name() { printf '%s' "${1#"$here"/}"; }
for f in "$here"/examples/*.rac "$here"/encoding/examples/*.rac; do
  out=$(run --raw "$f" 2>&1)
  if printf '%s' "$out" | grep -q "error:"; then echo "FAIL $f"; printf '%s\n' "$out"; status=1
  elif ! printf '%s' "$out" | cxx; then echo "FAIL $(name "$f"): generated C++ does not compile"; status=1
  else echo "ok   $(name "$f")"; fi
done
for f in "$here"/rejected/*.rac "$here"/encoding/rejected/*.rac; do
  [ -e "$f" ] || continue
  want=$(sed -n 's#^// expect: ##p' "$f" | head -1)
  mentions=$(sed -n 's#^// mentions: ##p' "$f" | head -1)
  got=$(run --json "$f" 2>/dev/null | MENTIONS="$mentions" python3 -c 'import json,os,sys; d=json.load(sys.stdin); print(" ".join(x["kind"] for x in d if os.environ["MENTIONS"] in x["message"]))' 2>/dev/null || echo crashed)
  case " $got " in
    *" $want "*) echo "ok   $(name "$f") -> $got" ;;
    *) echo "FAIL $(name "$f"): expected $want${mentions:+ mentioning $mentions}, got '$got'"; status=1 ;;
  esac
done
# The checkers' unit tests (theorems about hand-built kernels, proved by evaluation) and their soundness proofs
# against gpu/Spec.rac.
for f in "$here"/checks/*.rac "$here"/proofs/*.rac "$here"/encoding/checks/*.rac; do
  [ -e "$f" ] || continue
  what=$(name "$f")
  got=$(run --json "$f" 2>/dev/null | python3 -c 'import json,sys; [print("L%d %s: %s" % (x["startLine"], x["kind"], x["message"])) for x in json.load(sys.stdin)]' 2>/dev/null || echo crashed)
  if [ -z "$got" ]; then echo "ok   $what"; else echo "FAIL $what"; printf '%s\n' "$got"; status=1; fi
done
# Hardware test harnesses are host code: the same stubs check them. The FA4 comparison needs a GPU and PyTorch, so it
# is only compiled.
for h in "$here"/harness/*.cu "$here"/encoding/harness/*.cu; do
  if command -v clang++ >/dev/null && ! clang++ -std=c++17 -fsyntax-only -Wall -Werror -I "$here/stub" \
      -include "$here/stub/cuda_stub.h" -x c++ "$h"; then
    echo "FAIL $(name "$h") does not compile"; status=1
  else echo "ok   $(name "$h")"; fi
done
for p in "$here"/encoding/harness/*.py; do
  if python3 -c 'import sys; compile(open(sys.argv[1]).read(), sys.argv[1], "exec")' "$p"; then echo "ok   $(name "$p")"
  else echo "FAIL $(name "$p") does not compile"; status=1; fi
done
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
