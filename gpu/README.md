# GPU library spike

A feasibility spike of a GPU library written in Raccoon: a kernel is an ordinary Raccoon program over a sealed core,
and evaluating it builds a CUDA AST, which prints as CUDA C++. It runs on unmodified Raccoon with a custom trusted
prelude. Its two sm_100a GEMMs run correctly on a B200, the persistent one at 980 TFLOP/s against cuBLAS's 2147
(`DESIGN.md` §7).

| File | Role |
|---|---|
| `Prelude.rac` | The bundled prelude, whose `Pair` may hold linear values, plus a `String` layout (for literals) and native `Nat.div`/`Nat.mod` |
| `Text.rac` | Number printing |
| `Cuda.rac` | CUDA AST and printer; knows nothing about safety |
| `Check.rac` | Checkers of the structural invariants of a kernel's AST (`OBLIGATIONS.md` §4), and the certificate `Gpu.render` requires of a kernel it prints |
| `Spec.rac` | What the structural invariants mean, stated on the AST independently of `Check.rac`: the statements its soundness proofs prove |
| `Gpu.rac` | The sealed core: emitter, values, registers, loops, branches, shared tiles, global matrices, launch; and the Blackwell layer (warp roles, `elect`, the TMA stage ring, tensor memory, `tcgen05` MMA, the tensor-core epilogue), designed in `DESIGN.md` |
| `examples/` | Kernels that must generate code: a tiled SIMT GEMM, ReLU, TinyGEMM (a warp-specialized sm_100a GEMM), and a persistent version of it with a double-buffered accumulator |
| `rejected/` | Programs that must be refused, each naming the diagnostic on its `// expect:` line, and `*_mutants.py` tables of one-snippet mutations of an example (run by `mutate.py`) |
| `checks/` | Unit tests of `Check.rac`: what each checker finds in hand-built kernels, as theorems proved by evaluation |
| `proofs/` | Soundness proofs of `Check.rac`'s checkers against `Spec.rac`, and `NOTES.md`, what made them hard |
| `stub/` | Just enough of the CUDA headers for a host C++ compiler to check generated kernels, launchers and harnesses |
| `OBLIGATIONS.md` | The library's claim, the platform assumptions it rests on, and each sealed operation's obligations: the checklist for review and for verification |
| `REFERENCE_CUTLASS.md` | How CUTLASS's sm100 GEMM, the performance reference, differs from ours, what that means for the discipline, and the commands to benchmark it |
| `harness/` | Host programs that run a generated kernel on a GPU against a CPU reference (`DESIGN.md` §7) |

Generate a kernel, or check everything:

```bash
gpu/gen.sh gpu/examples/gemm.rac
```

```bash
RACCOON="java -cp <raccoon classpath> com.raccoonlang.Main" gpu/check.sh
```

`gen.sh` falls back to `sbt run`; `check.sh` needs a fast launcher in `RACCOON`. Both print the generated kernel with
the CLI's `--raw`, which prints a String result as its characters. When `clang++` is present, `check.sh` also compiles
each generated kernel against `stub/`.

## What the types guarantee

- **Ordering and participation.** The emitter `Ctx(l, g)` is linear and every operation threads it. `g` records
  whether the whole CTA runs the code, so a barrier or a full-tile store under a per-thread branch is rejected.
- **Scoping.** Values and registers live in the lifetime of the block that made them, so generated code is well scoped:
  a loop index cannot become loop state, and a shared-array handle cannot leave its allocation.
- **Authority.** `Tile` and `GOwn` are sealed, linear and fieldless. A shared tile moves `empty → written → ready →
  reading → empty` through stores, barriers and reads, which rules out reading before a barrier and overwriting
  before one. A tile is released only `empty`, since a loop body's shared array is reused by the next iteration.
  The output block is written exactly once.
- **Codegen soundness.** A loop body is generated once and captures no linear value, so all authority it uses travels
  in state whose type every iteration preserves. The same holds for branch arms, which are generated one after the
  other. That state must be `Fixed` (one value per type), so the code after a loop or branch cannot depend on which
  arm ran or how often the body did.
- **What is printed.** Only `Gpu.render` of a sealed `Program`, which only the kernel builders make, so every printed
  kernel came from the typed core, with its own shared memory and launcher. And only a well-formed one: `render`
  requires the certificate `Check.WellFormed` of its kernel, which the checker discharges by running `Check.rac`'s
  checkers on the concrete kernel where a program renders it. A kernel with a generation error, or that breaks a
  structural invariant the AST shows (`OBLIGATIONS.md` §4: scoping, shared memory, named barriers, literal widths,
  names, the launcher's parameters), is refused with `EvidenceNotDischarged`, naming the invariant and showing what
  its checker found (its messages, computed from numbers and names, show as string literals), and the kernel is never
  printed. So its name is a C identifier the printer does not declare itself, and only a kernel with a launcher
  (which asks for it) uses dynamic shared memory, never more than an SM has.

Index bounds are checked while generating, where every size is concrete: a read that is not provably in bounds is a
generation error, recorded in the kernel as an `#error` line, so `render` refuses the kernel. Preconditions on the
numbers a call is given (a positive tile or divisor, an aligned warpgroup) are evidence arguments instead
(`docs/PROOF_BY_EVALUATION.md`): the checker discharges each by evaluation where the call stands, and refuses a false
one with `EvidenceNotDischarged`, so the program never generates.

The Blackwell layer extends the same rules to asynchronous hardware (`DESIGN.md`): warp roles made by `split` and
`elect`; a stage ring whose endpoints an elected thread takes, so its per-thread stage and phase registers stay with
one thread; a one-shot tensor-memory permit; an accumulator whose typestate (`empty`, pending under one elected
thread, `ready`) orders the first MMA, the commit and the epilogue's loads; and tensor-map boxes that fix the layout
the TMA writes and the MMA descriptors read. The persistent kernel adds tile loops whose one owning loop writes each
tile once, and a ring of accumulators in tensor memory between the MMA thread and the epilogue warpgroup.
