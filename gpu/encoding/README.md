# gpu/encoding: the next GPU core

Status: started 2026-10-01; A1's core, example and unit checks built (step 1 and the first part of step 2 below),
not run on hardware; `NOTES.md` records what was awkward. A fresh copy of the typed core (`gpu/Gpu.rac`) in which the library grows the features it
lacks, starting with forward attention, then paged attention. `gpu/Gpu.rac` and its GEMM examples stay as they are, so
the kernels that ran on a B200 keep running while this design settles.

## Why a copy

Sealing is per file: only the file that declares `Ctx`, `Val` and the authority tokens can build them. So new
operations cannot live in a module that imports `Gpu`. They need a core of their own. `Core.rac` starts as `Gpu.rac`
(with the PTX 9.4 fixes: `await` fences `after_thread_sync`; producers' first waits are on a real, init-completed
phase) under the namespace `Core`. It imports `Cuda`, `Check` and `Text` from `gpu/`, which it shares with the GEMM
library.

How the code is judged: once it works, by reviewing it for readability and incidental complexity. What its tokens mean,
and why each operation is safe, is argued on paper in `docs/SEPARATION_PILOT.md`.

## Plan

**A1, forward attention** (`gpu/ATTENTION.md`, stage A1: non-causal, `seq` a multiple of 128, head dimension 128, one
query tile per CTA, a CTA of 256 threads). It is built as `ATTENTION.md` §3 designs it, with one deviation:

- **Two-dimensional tensor maps.** Q, K and V are addressed as `[BH·seq, 128]` with rank-2 maps (rows `BH·seq`,
  columns 128), and a CTA's rows start at `blockIdx.y · seq`. A1's `seq` is a multiple of 128, so no box crosses into
  the next head, and nothing needs the per-head zero-fill a rank-3 map gives. That keeps `Cuda.MapEncoding`,
  `Check.launcher` and its soundness proof unchanged.
  - The launcher takes `rows` and `dim` as scalars and refuses a launch unless `rows = BH · seq` and `dim = 128`.
  - Rank-3 maps come with A2's tails (`ATTENTION.md` §3.7).

Steps:
1. **Core.** Copy `Gpu.rac` to `Core.rac`, then add `ATTENTION.md` §3: tensor-memory offsets and `splitTmem`
   (§3.1), `holdStage` (§3.2), `mmaScores` (§3.3), the exchange (§3.4), `loadAcc8` (§3.5), the f32 math (§3.6),
   `fillHead` over rank-2 maps (§3.7, as above), `storeO` (§3.8) and `attentionKernel` (§3.10).
2. **Example and checks.**
   - `examples/attention.rac`, the schedule of `ATTENTION.md` §2.5.
   - `harness/attention_test.cu`, T1–T4 of §1.3, with FA4 as reference and benchmark.
   - `checks/`, unit tests of emitted code (§6).
   - `rejected/`, the mutants of §5.
   - `gpu/check.sh` runs all of it.
3. **Review.** Hostile review for races and protocol errors, then a code review for readability.

**Paged attention.** A1 over a paged KV cache:
- K and V are `[pages · 128, 128]`, with one page per 128-key block;
- a `block_table [B, maxPages]` (u32) gives each sequence's physical pages;
- the loader reads the table entry for block `j` and loads that page's rows.

TMA clipping keeps reads inside the cache whatever the table holds. That the entry is a valid page of the sequence is a
fact about the table, argued in `docs/SEPARATION_PILOT.md` §6.

**Hardware.** Nothing runs on a GPU until a kernel is expected to be competitive with CUTLASS or FA4 (the user's rule,
2026-10-01). A1 by design is not (`ATTENTION.md` §2.1), so A1 and paged A1 are checked by generation, the checkers,
the mutants and a C++ compile against `gpu/stub/`.

## Layout

- `Core.rac`: the core.
- `examples/`: kernels.
- `checks/`: unit tests of emitted code.
- `rejected/`: programs and mutant tables the core must refuse.
- `harness/`: host test programs for hardware runs.

`gpu/check.sh` covers this directory like the rest.
