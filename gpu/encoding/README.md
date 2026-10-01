# gpu/encoding: the next GPU core

Status: started 2026-10-01; steps 1 and 2 below done for A1, paged attention (P1) and A2 (causal and non-causal
masking, any `seq` ≥ 1, bf16 output, for both kernels) except the hardware runs: the core, the examples, the unit
checks, the mutants of `ATTENTION.md` §5 (`rejected/`), the host harnesses and the FA4 comparison (`harness/`), and
`OBLIGATIONS.md` (A19–A33, M12–M14, §6.10, §7); then the readability review's library changes (below). Nothing has
run on a GPU; `NOTES.md` records what was awkward, and what the review removed. A
fresh copy of the typed core (`gpu/Gpu.rac`) in which the library grows the features it lacks, starting with forward
attention, then paged attention. `gpu/Gpu.rac` and its GEMM examples stay as they are, so the kernels that ran on a
B200 keep running while this design settles.

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
  - The launcher takes `rows` and `dim` as scalars and refuses a launch unless `rows = BH · seq` and `dim = 128`
    (and, in A1, unless 128 divides `seq`).
  - A2 keeps the rank-2 maps (a decision of 2026-10-01, against `ATTENTION.md` §3.7's rank-3 maps), below.

Steps:
1. **Core.** Copy `Gpu.rac` to `Core.rac`, then add `ATTENTION.md` §3: tensor-memory offsets and `splitTmem`
   (§3.1), `holdStage` (§3.2), `mmaScores` (§3.3), the exchange (§3.4), `eachChunk` (§3.5), the f32 math (§3.6),
   `fillBlock` over rank-2 maps (§3.7, as above), `storeO` (§3.8) and `attentionKernel` (§3.10).
2. **Example and checks.**
   - `examples/attention.rac`, the schedule of `ATTENTION.md` §2.5.
   - `harness/attention_test.cu`, T1–T4 of §1.3 and the launcher's refusals; `harness/fa4_compare.py`, FA4 as
     reference and benchmark.
   - `checks/`, unit tests of emitted code (§6).
   - `rejected/`, the mutants of §5.
   - `gpu/check.sh` runs all of it.
3. **Review.** Hostile review for races and protocol errors, then a code review for readability, whose library
   proposals are built (2026-10-01):
   - protocols close without `…Done` tokens: a side is linear and belongs to its opener's scope, so the callback uses
     it up, and only its finisher does so without handing it on;
   - `eachChunk` and `writeP` loop over S's and P's chunks inside the core, so the per-chunk `loadAcc8` and `storeP`,
     their evidence and their chunk indices, are internal;
   - `mmaPV` and `rescaleO` read `OState`, so each role passes one loop body as both the peeled first iteration and
     the rest (which changes the first block's softmax code, `NOTES.md`);
   - the roles both attention kernels share live in `Attention.rac`, the CTA layout in `Layout.rac`;
   - `fillBlock`, one head map and one row for both halves of a stage, replaces `fillHead`.

**A2, masks, tails and bf16 output** (`ATTENTION.md` stage A2), for both the contiguous and the paged kernel. Causal
and O's element type (f32 or bf16) are generation-time choices of the kernel builders, one kernel each; the examples
generate the non-causal f32 kernel and the causal bf16 one of each. Masks are values (`maskedScores`, §3.9), and the
launchers accept any `seq` ≥ 1, the grid's x being `ceil(seq/128)`. With the rank-2 maps a sequence tail works so:
- a last K/V block that runs past `seq` reads the next head's rows (contiguous kernel), a last page's unused rows
  (paged kernel), or zeros past the matrix: `kv < seq` masks those keys, so their scores are −∞ and their `p` are 0;
- the rows of a last query tile past `seq` read the next head's Q rows (or zeros past the matrix); they are computed
  but never stored, since `storeO` guards on `seq`.

What this cannot refuse: a non-finite value in those rows of V (the next head's, or a last page's unused rows) turns
the masked keys' 0 · V into NaN, in every query row whose keys include that block, not only the tail's. That is a
correctness hazard under non-finite inputs, not a safety one (a packed variable-length kernel that loads whole blocks
across sequence boundaries shares it); the launch contracts ask for V finite in every row a block reads.

**Paged attention.** A1 over a paged KV cache:
- K and V are `[pages · H · 128, 128]`: a page holds 128 consecutive keys of every head;
- a `block_table [B, maxPages]` (u32) gives each sequence's physical pages;
- the loader reads the table entry for block `j` and loads that page's rows.

TMA clipping keeps reads inside the cache whatever the table holds. That the entry is a valid page of the sequence is a
fact about the table, argued in `docs/SEPARATION_PILOT.md` §6.

**Hardware.** Nothing runs on a GPU until a kernel is expected to be competitive with CUTLASS or FA4 (the user's rule,
2026-10-01). A1 by design is not (`ATTENTION.md` §2.1), nor are A2 and paged attention, built on its schedule, so they
are checked by generation, the checkers, the mutants and a C++ compile against `gpu/stub/`; the harnesses have run
against a host mock of the runtime (`NOTES.md`).

## Layout

- `Core.rac`: the core.
- `Layout.rac`: the CTA of eight warps that the attention and GEMM examples share (`roles4`).
- `Attention.rac`: the roles and CTA of forward attention, which `examples/attention.rac` and
  `examples/paged_attention.rac` run with their own loaders.
- `examples/`: kernels.
- `checks/`: unit tests of emitted code.
- `rejected/`: programs and mutant tables the core must refuse.
- `harness/`: host test programs for hardware runs.

`gpu/check.sh` covers this directory like the rest.
