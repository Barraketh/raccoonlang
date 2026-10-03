#!/usr/bin/env python3
"""Check compositional contracts, counterexamples, and certified CUDA lowering."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from check_experiment import check_experiment


def smoke(cuda):
    if cuda.count("for (unsigned ") != 3 or "v5 < n" not in cuda or "v6 < n" not in cuda:
        raise SystemExit("Expected one runtime outer loop and two runtime role loops.")


if __name__ == "__main__":
    check_experiment(HERE, [HERE, HERE.parent.parent / "gpu"], smoke)
