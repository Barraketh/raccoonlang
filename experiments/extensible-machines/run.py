#!/usr/bin/env python3
"""Check open machine definitions, fresh identities, epochs, and the Core AST bridge."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from check_experiment import check_experiment


def smoke(cuda):
    if cuda.count("for (unsigned ") != 1 or "v4 < K" not in cuda or cuda.count("__syncthreads();") != 4:
        raise SystemExit("Expected one runtime loop and both publication/recycling barriers for each buffer.")
    if "v0[64]" not in cuda or "v1[64]" not in cuda:
        raise SystemExit("Expected two distinct allocations of identical shape.")


if __name__ == "__main__":
    check_experiment(HERE, [HERE, HERE.parent / "compositional-machines", HERE.parent.parent / "gpu"], smoke)
