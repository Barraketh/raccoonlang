#!/bin/sh
# Checks the spike: every example must generate code, and every file under rejected/ must fail with the diagnostic
# kind named on its `// expect:` line (or, for `#error`, generate a kernel carrying that generation-time error).
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
for f in "$here"/examples/*.rac; do
  out=$(run "$f" 2>&1)
  if printf '%s' "$out" | grep -q "error:"; then echo "FAIL $f"; printf '%s\n' "$out" | grep -v '^[0-9][0-9]:'; status=1
  elif ! printf '%s' "$out" | python3 "$here/render.py" | cxx; then echo "FAIL $(basename "$f"): generated C++ does not compile"; status=1
  else echo "ok   $(basename "$f")"; fi
done
for f in "$here"/rejected/*.rac; do
  want=$(sed -n 's#^// expect: ##p' "$f" | head -1)
  if [ "$want" = "#error" ]; then
    got=$(run "$f" 2>&1 | python3 "$here/render.py" | grep -c '#error')
    [ "$got" -gt 0 ] && echo "ok   $(basename "$f") -> generation error" || { echo "FAIL $(basename "$f"): no generation error"; status=1; }
  else
    got=$(run --json "$f" 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); print(" ".join(x["kind"] for x in d))' 2>/dev/null || echo crashed)
    case " $got " in
      *" $want "*) echo "ok   $(basename "$f") -> $got" ;;
      *) echo "FAIL $(basename "$f"): expected $want, got '$got'"; status=1 ;;
    esac
  fi
done
exit $status
