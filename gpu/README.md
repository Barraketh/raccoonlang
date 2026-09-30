# GPU library spike

A feasibility spike of a GPU library written in Raccoon: a kernel is an ordinary Raccoon program over a sealed core,
and evaluating it builds a CUDA AST, which prints as CUDA C++. It runs on unmodified Raccoon with a custom trusted
prelude.

| File | Role |
|---|---|
| `Prelude.rac` | The bundled prelude, plus a `String` layout (for literals), native `Nat.div`/`Nat.mod`, and `Pair`, a pair that may hold linear values |
| `Text.rac` | Number printing |
| `Cuda.rac` | CUDA AST and printer; knows nothing about safety |
| `Gpu.rac` | The sealed core: emitter, values, registers, loops, branches, shared tiles, global matrices, launch; and the Blackwell layer (warp roles, `elect`, the TMA stage ring, tensor memory, `tcgen05` MMA, the tensor-core epilogue), designed in `DESIGN.md` |
| `examples/` | Kernels that must generate code: a tiled SIMT GEMM, ReLU, and TinyGEMM, a warp-specialized sm_100a GEMM |
| `rejected/` | Programs that must be refused, each naming the diagnostic on its `// expect:` line, and `*_mutants.py` tables of one-snippet mutations of an example (run by `mutate.py`) |
| `stub/` | Just enough of the CUDA headers for a host C++ compiler to check generated kernels, launchers and harnesses |
| `harness/` | Host programs that run a generated kernel on a GPU against a CPU reference (`DESIGN.md` §6) |

Generate a kernel, or check everything:

```bash
gpu/gen.sh gpu/examples/gemm.rac
```

```bash
RACCOON="java -cp <raccoon classpath> com.raccoonlang.Main" gpu/check.sh
```

`gen.sh` falls back to `sbt run`; `check.sh` needs a fast launcher in `RACCOON`. The CLI prints a computed `String`
as a constructor tree, and `render.py` turns it back into text; printing a large kernel recurses deeply, so give the
launcher a large stack (`java -Xss64m …`). When `clang++` is present, `check.sh` also compiles each generated kernel
against `stub/`.

## What the types guarantee

- **Ordering and participation.** The emitter `Ctx(l, g)` is linear and every operation threads it. `g` records
  whether the whole CTA runs the code, so a barrier or a full-tile store under a per-thread branch is rejected.
- **Scoping.** Values and registers live in the lifetime of the block that made them, so generated code is well scoped:
  a loop index cannot become loop state, and a shared-array handle cannot leave its allocation.
- **Authority.** `Tile` and `GOwn` are sealed, linear and fieldless. A shared tile moves `empty → written → ready →
  reading → empty` through stores, barriers and reads, which rules out reading before a barrier and overwriting
  before one. The output block is written exactly once.
- **Codegen soundness.** A loop body is generated once and captures no linear value, so all authority it uses travels
  in state whose type every iteration preserves. The same holds for branch arms, which are generated one after the
  other.

Index bounds are checked while generating, where every size is concrete: a read that is not provably in bounds turns
the kernel into an `#error`.

The Blackwell layer extends the same rules to asynchronous hardware (`DESIGN.md`): warp roles made by `split` and
`elect`; a stage ring whose endpoints an elected thread takes, so its per-thread stage and phase registers stay with
one thread; a one-shot tensor-memory permit; an accumulator whose typestate (`empty`, pending under one elected
thread, `ready`) orders the first MMA, the commit and the epilogue's loads; and tensor-map boxes that fix the layout
the TMA writes and the MMA descriptors read.
