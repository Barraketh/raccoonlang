# Benchmarks

This directory contains generated benchmarks for raccoon vs Lean.

## Typechecker / Interpreter

`checker_interpreter.py` generates generic typechecker/interpreter stress tests for conversion, local contexts, application spines, lambdas/Pis, match refinement, type-pattern capture, projections, transparent unfolding, and universe normalization.

Current results are recorded in `checker_interpreter.md`.

## Nested Dependent Vec.zip

`nested_zip.py` generates a family of raccoon and Lean programs with a custom indexed `Vec`, a polymorphic `Pair`, and a polymorphic dependent `zip`. Raccoon uses the kernel-provided `Nat` and an ordinary `def zip`, producing one `nested_zip_<size>.rac` file per size.

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

For the GraalVM native binary:

```bash
./scripts/build-graal-native.sh
python3 benchmarks/nested_zip.py --runner native
```

For Lean:

```bash
python3 benchmarks/nested_zip.py --runner lean-raised --lean lean --lean-sizes 800,1600,3200
```

Use `--lean /path/to/lean` to select a particular Lean toolchain.

Useful options:

- `--runner generate` writes benchmark sources without running them.
- `--runner` may be repeated, for example `--runner jvm --runner native`.
- `--raccoon-sizes 0,100,400,800,1600,6400,12800,51200` selects raccoon sizes.
- `--lean-sizes 800,1600,3200` selects Lean sizes.
- `--prelude /path/to/prelude.rac` selects the prelude for both Raccoon runners; the default is `Init/TestPrelude.rac`, which provides the small set of definitions this benchmark needs.
- `--native-bin /path/to/raccoon` overrides the default `target/graalvm/raccoon` binary.
- `--out-dir /tmp/raccoonlang-benchmarks/nested-zip` controls where generated sources are written.

The runner prints process wall-clock times. JVM timings include JVM startup for each run.

## Results

Measured on October 26, 2026 on an Apple M1 Max running macOS 15.5. Raccoon JVM used Oracle GraalVM 21.0.12 as a JVM; the native binary was built by `scripts/build-graal-native.sh`. Lean was `4.37.0-nightly-2026-10-26`, arm64. Raccoon values are medians of five runs, or three at 51,200; Lean values are single runs.

### Raccoon JVM

Direct JVM CLI, including JVM startup per run.

| nested zips | time |
|---:|---:|
| 0 | 0.342s |
| 100 | 0.372s |
| 400 | 0.407s |
| 800 | 0.449s |
| 1,600 | 0.544s |
| 3,200 | 0.679s |
| 6,400 | 0.921s |
| 12,800 | 1.310s |
| 51,200 | 2.273s |

### Raccoon Native

GraalVM native binary, process startup included.

| nested zips | time |
|---:|---:|
| 0 | 0.012s |
| 100 | 0.013s |
| 400 | 0.022s |
| 800 | 0.033s |
| 1,600 | 0.051s |
| 3,200 | 0.086s |
| 6,400 | 0.159s |
| 12,800 | 0.320s |
| 51,200 | 1.266s |

### Lean

| config | nested zips | result |
|---|---:|---|
| default limits | 400 | 2.168s, success |
| default limits | 800 | fails after 0.66s |
| raised `maxRecDepth`, disabled heartbeats | 800 | 2.692s, success |
| raised `maxRecDepth`, disabled heartbeats | 1,600 | 8.662s, success |
| raised `maxRecDepth`, disabled heartbeats | 3,200 | 33.350s, success |
| raised `maxRecDepth`, disabled heartbeats | 6,400 | fails after 138s |
