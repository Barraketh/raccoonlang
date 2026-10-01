#!/bin/sh
# Runs a CUDA toolkit command (nvcc, ptxas, cuobjdump, nvdisasm) in the raccoon-cuda container, on the repository
# mounted at its own path, from the current directory, with this script's standard input:
#   gpu/toolkit/cuda.sh nvcc -gencode arch=compute_100a,code=sm_100a -c -Xptxas -v kernel.cu -o /tmp/k.o
# Compiling needs no GPU. Build the image first (gpu/toolkit/Dockerfile); without it the command fails at once, and
# `cuda.sh true` says whether the toolkit is there. Paths outside the repository are not visible, except /tmp inside
# the container.
here=$(cd "$(dirname "$0")/../.." && pwd)
exec docker run --rm -i --pull never -v "$here:$here" -w "$PWD" raccoon-cuda:12.9 "$@"
