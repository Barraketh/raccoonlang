# Typechecker / Interpreter Benchmarks

This suite complements `typeclass_resolution.py`. It tracks proof-assistant-shaped costs that are not just typeclass search: conversion, local contexts, dependent matching, type-pattern capture, projections, transparent unfolding, and universe normalization.

## Scenarios

| scenario | stresses |
|---|---|
| `alias-defeq` | definitional equality through transparent aliases |
| `let-context` | large local environments and checked let bodies |
| `app-spine` | repeated checked applications under a growing body |
| `lambda-binders` | large Pi/lambda binders and full application |
| `match-width` | wide neutral match exhaustiveness and branch checking |
| `dependent-match` | dependent equality-style match refinement |
| `pattern-capture` | Raccoon type-pattern capture / Lean implicit parameter recovery |
| `projection-chain` | nested structure projections and selector typing |
| `transparent-chain` | transparent top-level unfolding and runtime evaluation |
| `universe-max` | large universe-parameter and `Level.max` terms |

## Running

From the repository root:

```bash
sbt -no-colors compile
python3 benchmarks/checker_interpreter.py --runner jvm --runner lean
```

Useful options:

- `--runner generate` writes benchmark sources without running them.
- `--scenario projection-chain` selects one scenario.
- `--sizes 0,128,512,1024` overrides the selected scenario sizes.
- `--csv /tmp/results.csv` appends machine-readable results.
- `--prelude src/main/resources/Init/TestPrelude.rac` controls the Raccoon prelude used by generated files.

## Current Results

Measured on June 7, 2026 on macOS arm64, branch `performance_iimprovements`.

- RaccoonJVM: Oracle GraalVM/OpenJDK 21.0.11
- Lean: `4.32.0-nightly-2026-06-06`, arm64, commit `9c38aeebc6b701e6adb1dd07659718974eeb0306`
- Repetitions: 1 per row
- Timing: process wall-clock time; JVM rows include JVM startup
- Raccoon generated files use `src/main/resources/Init/TestPrelude.rac`
- Lean generated files use the normal Lean nightly environment with `maxHeartbeats = 0`

### Raccoon JVM

| scenario | size | time |
|---|---:|---:|
| `alias-defeq` | 0 / 128 / 512 / 1024 | 0.368s / 0.433s / 0.492s / 0.560s |
| `let-context` | 0 / 1000 / 5000 / 10000 | 0.347s / 0.448s / 0.656s / 0.904s |
| `app-spine` | 0 / 1000 / 5000 / 10000 | 0.350s / 0.454s / 0.781s / 0.992s |
| `lambda-binders` | 0 / 128 / 512 / 1024 | 0.343s / 0.385s / 0.416s / 0.483s |
| `match-width` | 0 / 128 / 512 / 1024 | 0.366s / 0.393s / 0.478s / 0.586s |
| `dependent-match` | 0 / 100 / 500 / 1000 | 0.351s / 0.501s / 0.802s / 1.100s |
| `pattern-capture` | 0 / 16 / 64 / 128 / 256 | 0.348s / 0.404s / 0.504s / 0.615s / 0.930s |
| `projection-chain` | 0 / 128 / 512 / 1024 | 0.314s / 0.357s / 0.415s / 0.434s |
| `transparent-chain` | 0 / 1000 / 5000 / 10000 | 0.349s / 0.569s / 1.026s / 1.403s |
| `universe-max` | 0 / 16 / 64 / 128 / 256 | 0.394s / 0.404s / 0.466s / 0.547s / 0.722s |

### Lean Nightly

| scenario | size | time |
|---|---:|---:|
| `alias-defeq` | 0 / 128 / 512 / 1024 | 1.265s / 0.627s / 0.736s / 0.923s |
| `let-context` | 0 / 1000 / 5000 / 10000 | 0.641s / 0.928s / 13.078s / 58.049s |
| `app-spine` | 0 / 1000 / 5000 / 10000 | 0.579s / 1.061s / 15.114s / 75.315s |
| `lambda-binders` | 0 / 128 / 512 / 1024 | 0.624s / 0.634s / 0.963s / 2.373s |
| `match-width` | 0 / 128 / 512 / 1024 | 0.658s / 0.780s / 2.475s / 7.704s |
| `dependent-match` | 0 / 100 / 500 / 1000 | 0.641s / 0.815s / 1.807s / 3.103s |
| `pattern-capture` | 0 / 16 / 64 / 128 / 256 | 0.616s / 0.673s / 0.778s / 1.147s / 3.150s |
| `projection-chain` | 0 / 128 / 512 / 1024 | 0.589s / 0.678s / 5.897s / 44.054s |
| `transparent-chain` | 0 / 1000 / 5000 / 10000 | 0.919s / 0.950s / 2.730s / 4.216s |
| `universe-max` | 0 / 16 / 64 / 128 / 256 | 0.642s / 0.582s / 0.683s / 1.072s / 2.656s |

## Notes

The first projection-chain generator repeated nested `Box(Box(...))` type arguments and produced quadratic source files. The current generator uses a type-pattern constructor in Raccoon and inferred constructor parameters in Lean, so the source shape is linear in the depth.
