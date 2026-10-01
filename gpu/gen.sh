#!/bin/sh
# Generates CUDA from a kernel file:  gpu/gen.sh gpu/encoding/examples/tinygemm.rac > tinygemm.cu
# Uses $RACCOON as the raccoon launcher if set (anything taking the CLI's arguments), else `sbt run`. `--raw` prints
# the generated String as its characters.
here=$(cd "$(dirname "$0")" && pwd)
if [ -n "$RACCOON" ]; then
  $RACCOON --prelude "$here/Prelude.rac" --root "$here" --raw "$@"
else
  (cd "$here/.." && sbt -batch -error "run --prelude gpu/Prelude.rac --root gpu --raw $*")
fi
