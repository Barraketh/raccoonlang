#!/bin/sh
# Generates CUDA from a kernel file:  gpu/gen.sh gpu/examples/gemm.rac > gemm.cu
# Uses $RACCOON as the raccoon launcher if set (anything taking the CLI's arguments; give it a large stack, e.g.
# `java -Xss64m`, since printing a large kernel recurses deeply), else `sbt run` with a 64MB stack.
here=$(cd "$(dirname "$0")" && pwd)
if [ -n "$RACCOON" ]; then
  $RACCOON --prelude "$here/Prelude.rac" --root "$here" "$@"
else
  (cd "$here/.." && sbt -J-Xss64m -batch -error "run --prelude gpu/Prelude.rac --root gpu $*")
fi | python3 "$here/render.py"
