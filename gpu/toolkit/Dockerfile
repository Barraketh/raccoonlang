# The CUDA 12.9 compilers without a GPU: nvcc, ptxas, cuobjdump, nvdisasm and the headers the generated kernels and
# the harnesses include. NVIDIA ships no CUDA for macOS (none after 10.2, none for Apple Silicon), so on a Mac it runs
# in a Linux container; `sbsa` is NVIDIA's repository for arm64 Linux, `x86_64` for Intel. Build with
#   docker build -t raccoon-cuda:12.9 gpu/toolkit
# and use it through gpu/toolkit/cuda.sh.
FROM ubuntu:22.04
ARG REPO=sbsa
RUN apt-get update -qq \
 && apt-get install -y -qq --no-install-recommends wget ca-certificates gnupg g++ \
 && wget -q https://developer.download.nvidia.com/compute/cuda/repos/ubuntu2204/${REPO}/cuda-keyring_1.1-1_all.deb \
 && dpkg -i cuda-keyring_1.1-1_all.deb && rm cuda-keyring_1.1-1_all.deb \
 && apt-get update -qq \
 && apt-get install -y -qq --no-install-recommends cuda-nvcc-12-9 cuda-cuobjdump-12-9 cuda-nvdisasm-12-9 \
      cuda-cudart-dev-12-9 cuda-driver-dev-12-9 \
 && rm -rf /var/lib/apt/lists/*
ENV PATH=/usr/local/cuda-12.9/bin:$PATH
