# Benchmarks

This directory contains generated benchmarks for raccoon vs Lean.

## Typechecker / Interpreter

`checker_interpreter.py` generates generic typechecker/interpreter stress tests for conversion, local contexts, application spines, lambdas/Pis, match refinement, type-pattern capture, projections, transparent unfolding, and universe normalization.

Current results are recorded in `checker_interpreter.md`.

## Nested Dependent Vec.zip

`nested_zip.py` generates a family of raccoon and Lean programs with a custom indexed `Vec`, a polymorphic `Pair`, and a polymorphic dependent `zip`.

The generated benchmark body has this shape:

```text
z1 := zip(v, v)
z2 := zip(v, z1)
...
zN := zip(v, zN-1)
consume(zN)
```

The final `consume(zN)` keeps the deeply nested indexed-vector type live. The benchmark is intended to stress parsing, elaboration, universe/type inference, type-pattern inference in raccoon, and dependent typechecking. The benchmark does not execute `bench`, so it is not measuring runtime vector construction.

The Lean version uses `Type u` rather than `Sort u` because Lean rejects this universe-polymorphic inductive when the result universe may be `Prop`.

## Running

From the repository root:

```bash
sbt -no-colors compile
python3 benchmarks/nested_zip.py --runner jvm
```

For the Scala Native binary:

```bash
sbt native/nativeLink
python3 benchmarks/nested_zip.py --runner native --native-bin native/target/scala-2.13/raccoon-release-full
```

For Lean:

```bash
python3 benchmarks/nested_zip.py --runner lean-raised --lean lean --lean-sizes 800,1600,3200
```

To reproduce the Lean 4.25 table below after installing that toolchain with `elan`, pass its exact binary:

```bash
python3 benchmarks/nested_zip.py --runner lean-raised \
  --lean ~/.elan/toolchains/leanprover--lean4-nightly---nightly-2025-10-06/bin/lean \
  --lean-sizes 800,1600,3200
```

Useful options:

- `--runner generate` writes benchmark sources without running them.
- `--runner` may be repeated, for example `--runner jvm --runner native`.
- `--raccoon-sizes 0,100,400,800,1600,6400,12800,51200` selects raccoon sizes.
- `--lean-sizes 800,1600,3200` selects Lean sizes.
- `--raccoon-kinds opaque`, `--raccoon-kinds transparent`, or `--raccoon-kinds opaque,transparent` selects raccoon `zip` transparency.
- `--out-dir /tmp/raccoonlang-benchmarks/nested-zip` controls where generated sources are written.

The runner prints process wall-clock times. JVM timings include JVM startup for each run.

## Current Results

Measured on April 15, 2026 on an Apple Silicon macOS machine. The repository working tree was based on commit `ddd805d`. Raccoon JVM used OpenJDK 19.0.1. The native binary was `native/target/scala-2.13/raccoon-release-full` (`arm64`). Lean was tested with arm64 `elan` and arm64 Lean toolchains.

### Raccoon JVM

Direct JVM CLI, including JVM startup per run. Values are medians.

| nested zips | opaque `zip` | transparent `zip` |
|---:|---:|---:|
| 0 | 0.298s | 0.291s |
| 100 | 0.340s | 0.361s |
| 400 | 0.398s | 0.416s |
| 800 | 0.420s | 0.465s |
| 1,600 | 0.466s | 0.558s |
| 6,400 | 0.716s | 0.889s |
| 12,800 | 0.931s | 1.169s |
| 51,200 | 2.175s | 3.435s |

### Raccoon Native

Scala Native binary, process startup included. Values are medians.

| nested zips | opaque `zip` | transparent `zip` |
|---:|---:|---:|
| 0 | 0.006s | 0.006s |
| 100 | 0.010s | 0.012s |
| 400 | 0.025s | 0.029s |
| 800 | 0.045s | 0.053s |
| 1,600 | 0.087s | 0.105s |
| 6,400 | 0.336s | 0.460s |
| 12,800 | 0.740s | 1.064s |
| 51,200 | 3.650s | 6.794s |


### Lean 4.31 Arm64

Lean `4.31.0-nightly-2026-04-15`, arm64.

| config | nested zips | result |
|---|---:|---|
| default limits | 400 | 1.146s, success |
| default limits | 800 | fails |
| raised `maxRecDepth`, disabled heartbeats | 800 | 2.872s, success |
| raised `maxRecDepth`, disabled heartbeats | 1,600 | 9.915s, success |
| raised `maxRecDepth`, disabled heartbeats | 3,200 | 41.274s, success |
| raised `maxRecDepth`, disabled heartbeats | 6,400 | failed after 178s |
