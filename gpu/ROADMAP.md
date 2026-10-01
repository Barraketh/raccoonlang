# GPU library and language: state and roadmap

Status: **handoff** (2026-10-01). It is written for a new thread, and says where the work stands, what remains, the
proposed order and the decisions that are open. The branch is `lemur_gpu`; its tip when this was written was the
commit that added this file.

## 1. Where things stand

**The aim** (the user's):
- Find the cleanest safe encoding of the GPU algebra in Raccoon, which leans on linearity and scopes, judged by reading
  working code for readability and incidental complexity.
- Support kernels like paged attention, competitive with CUTLASS and open FlashAttention (FA4), not cuBLAS.
- Later, establish what it takes to prove the encoding correct without changing it.

**The library** is `gpu/encoding/` (`README.md` lists its files). The old core, `gpu/Gpu.rac` and `gpu/examples/`, is
retired (§2, A5).

**Built, each with a hostile review; all of it ran on a B200 on 2026-10-01:**

| Area | What | Document |
|---|---|---|
| Attention | A1, A2 (causal, tails, bf16) | `gpu/ATTENTION.md` |
| Attention | A3a: two query tiles in ping-pong | `encoding/A3.md` |
| Attention | A3b: correction warpgroup, lazy rescale, emulated exp2, register split | `encoding/A3B.md` |
| Paged attention | P1: prefill | `encoding/PAGED.md` |
| Paged attention | P2: decode with a checked append, and a combine kernel | `encoding/P2.md` |
| CTA pairs (`cta_group::2`) | pair TinyGEMM; persistent pair GEMM | `encoding/TWO_CTA.md`, `encoding/TWO_CTA_FACTS.md` |
| Registers | a modelled resource, plus a `ptxas` spill check | `encoding/REGISTERS.md` |
| Instructions | typed PTX instructions in the CUDA AST, range-checked | `gpu/EVALUATOR.md` §3 |

**Hardware results** (`encoding/NOTES.md`, "Hardware session"; `gpu/REFERENCE_CUTLASS.md` §8.9):
- **Every harness and probe passes.** The first run failed four ways; each was fixed and re-run on the box:
  - P2's append wrote past its row;
  - a harness compared bf16 values wrongly;
  - A3b deadlocked in `setmaxnreg`;
  - A3a's causal kernel used too many registers to launch.
- **The pair GEMM** is level with CUTLASS's 2-SM 256×256 kernel at 8192³ (0.649 ms against 0.658), and 10% slower at
  4096³.
- **Attention** non-causal at BH = 16, seq = 4096: A1 343, A3a 462 and A3b 441 TFLOP/s. These are single runs, not yet
  compared with FA4.

**Unrun on hardware since then:**
- A3b's added barrier after its register split;
- the launch bounds every builder now prints, which raised several kernels' register counts (A1 from 44 to 160);
- typed instructions (generated CUDA byte-identical, so expected unchanged).

## 2. What remains

### A. Library safety
1. **Evaluator v0** (`gpu/EVALUATOR.md` §4), in Raccoon, after a performance spike (EVALUATOR.md §8 step 2).
   - **What it does:** it runs generated kernels on the host, with bounds, race, deadlock and exit checks, under
     explored schedules. It replaces the hand-written host mocks.
   - **Why:** two of the four hardware bugs, and every race the reviews found, were generated code doing other than
     what was meant.
   - **Size:** a few thousand lines.
2. **The hardware battery** (EVALUATOR.md §5): per-instruction tests that hold the evaluator to the B200, bit-exact
   where PTX states results. Each assumption in `OBLIGATIONS.md` §3 becomes a test.
3. **Placement checks in `Check.rac`**, first for `setmaxnreg` (EVALUATOR.md §3 lists what it needs: the kernel records
   its threads, residency and split groups), then one per resource family.
4. **Per-resource sealed modules** (`REGISTERS.md` §2), one family at a time. This partly waits on the sealing decision
   (§4, C2).
5. **Retire the old core** (`Gpu.rac`, `gpu/examples/`). **Done.** It went with its harness, its programs and mutants
   that had to be refused, the raw-asm statement `Stmt.asm` (and its cases in `Check.rac`, `Spec.rac` and the
   proofs), and its second descriptor packer. Its refused programs, its TinyGEMM mutants and its generic-render check
   moved to `encoding/`.
6. **Optional: index arithmetic through layouts** (CuTe-style shape and stride). The core's row, column and wrap
   formulas would become generation-time facts. Discussed and judged library work; not scheduled.

### B. Kernels and performance, toward paged attention
1. **Pair attention**: A3b's schedule on a CTA pair (TWO_CTA.md §6 step 3), the prefill path to FA4's default kernel.
2. **A real FA4 comparison**: realistic sizes, medians over many runs. `encoding/harness/fa4_compare.py` exists but
   covers A2 only.
3. **A decode benchmark** against FA4's decode (`pack_gqa`, `num_splits`). Decode is memory-bound, and FA4 runs it on
   one CTA.
4. **Re-validate on hardware** the items listed under "Unrun on hardware since then" (§1).
5. **Later:**
   - persistent attention, and a TMA-store epilogue for attention;
   - the GEMM's 4096³ gap (its static schedule against CUTLASS's dynamic one);
   - speculative decode, a fused append, and paged prefill on A3b's schedule.

### C. Language (the user's thread, and joint design)
1. Soundness holes and interpreter speed. Generating an attention example takes 23–44 s, and `check.sh` takes over two
   minutes.
2. The design problems in `docs/proposals/SAFETY_PROBLEMS.md`:
   - the library's meaning in Raccoon (propositions about linearity and scope);
   - globally unique names;
   - deadlocks.
   Also sealing shared across modules (`REGISTERS.md` §9) and, later, an ergonomics brainstorm. Lambda headers are 22%
   of the attention code (`docs/proposals/NAMED_IMPLICITS.md` is one item).
3. The kernel specs `docs/proposals/PROP_SEPARATION.md`, `NOMINAL_FAMILIES.md` and `REFINEMENT_CERTIFICATES.md`. Then
   land the spike on `clean_history`.

## 3. Proposed order

**Phase 1, now, in parallel.** These touch different files.
- **A1:** the evaluator, in its own directory. It should come before more complex kernels: pair attention is the most
  bug-prone kernel we would write next.
- **B1 and B2:** pair attention, with the FA4 comparison at realistic sizes.
- **A5:** retire the old core (done).
- **C1:** the user's language thread.

**Phase 2: hardware session 2**, once pair attention passes review and runs clean under the evaluator:
- correctness of everything, including B4;
- pair attention against FA4's default, and decode against FA4's decode;
- the GEMM rechecks;
- the battery (A2), to validate the evaluator.

The results choose the next performance items (B5).

**Phase 3, after the language design settles:**
- per-resource modules and branded values (A4), then placement checks (A3) in their final form;
- the proof research: an adequacy argument stated against the evaluator's semantics;
- landing on `clean_history` after the kernel specs.

## 4. Open decisions (the user's)
1. **The evaluator's language:** settled: the evaluator is written in Raccoon (2026-10-01; EVALUATOR.md §9).
2. **FMA contraction:** compile with `-fmad=false`, or have the printer emit explicit `fma` (EVALUATOR.md §9).
3. **Hardware timing:** does the next session wait for pair attention, or come earlier to measure the launch-bounds
   change?
4. **Sealing across modules** (REGISTERS.md §9): which remedy, or typed instructions plus `Check.rac` placement rules.
5. **Earlier, still open:**
   - the `match h : e` equation using the prelude's `Eq` (`docs/implemented/MATCH_EQUATION.md`);
   - lambda result-type synthesis, which is not done, since it would need readback;
   - named implicit instantiation (`docs/proposals/NAMED_IMPLICITS.md`).

## 5. How the work has been run

**Workers:**
- Implementers are `opus-medium` agents in their own worktrees; each spawns one `opus-high` hostile reviewer,
  read-only.
- A reviewer's completion notice often arrives in the coordinator's session, not the worker's: forward it.
- A worker's worktree may start on an old commit. Have it `git reset --hard` to the base it was given and confirm with
  `git log`.
- Land a worker's commits with `git cherry-pick` onto `lemur_gpu`, then run the full check. Never stash: the stash is
  shared with other sessions.

**Checks:**
- Run the checks with `RACCOON=$PWD/target/graalvm/raccoon sh gpu/check.sh` (about 130 s; 186 ok at this commit).
- The register check needs the CUDA toolkit. NVIDIA ships none for macOS, so it runs in a container: `colima start`,
  then `docker build -t raccoon-cuda:12.9 gpu/toolkit`, then `gpu/toolkit/cuda.sh nvcc …`. Without it, `check.sh`
  prints one "skipped" line.

**Hardware:**
- `gpu/encoding/harness/hw.sh gen DIR` builds a bundle locally. `sh hw.sh run` and `sh run_gemm_pair.sh run` run on
  the box.
- vast.ai's CLI is at `~/.local/bin/vastai`. Use `create instance <offer> --image nvidia/cuda:12.9.1-devel-ubuntu22.04
  --disk 80 --ssh --direct`.
- SSH needs the key attached per instance (`attach ssh`); sshd takes a few minutes to come up.
- `destroy instance` asks for confirmation (`echo y |`). Destroy the instance when done.
- The user's rule: rent hardware only for kernels expected to be competitive, and batch the work into one session.

**The shell is zsh.** It does not word-split unquoted variables. Pass ssh arguments literally, and match process names
exactly (`pkill -x`), since `pkill -f` can kill the shell running the command.

**Conventions:**
- Specs go in `docs/` (language) or `gpu/` (library), in house style: short declarative sentences, lists, and a
  decisions section.
- Typing is local: derive from arguments, never from the expected type.
- State rules in their own terms.
- Define a term before using it.
