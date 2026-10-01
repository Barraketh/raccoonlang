# Attention A3b: a correction warpgroup, a lazy rescale, an emulated exponential, a register split

Status: built (2026-10-01), not run on hardware: `Core.rac`'s correction-warpgroup section, `Layout.rolesCorrected`,
`examples/attention_a3b.rac`, `harness/attention_a3b_test.cu`, `rejected/attention_a3b_mutants.py`; `NOTES.md` §"A3b"
records what was awkward. §7 lists where the build departs from the design as first written. It is the second
performance step of `gpu/ATTENTION.md` §6 A3, on A3a as built (`gpu/encoding/A3.md` §6). FA4 facts are from `flash_attn/cute/flash_fwd_sm100.py` and `softmax.py` at
`616b0e8`.

## 1. Why

A3a's softmax warpgroups do all of this on their critical path:
- **the rescale of Ô:** 16 loads and 16 stores of 8 columns per thread per block;
- **every exponential** on the special-function unit: 128 per thread per block;
- **their work at 168 registers**, the share 384 threads leave.

FA4 takes each off:
- a correction warpgroup rescales Ô;
- the rescale is skipped unless a row's maximum grew by more than 8 (log₂ units);
- a fraction of the exponentials runs as a polynomial on the FMA units;
- `setmaxnreg` gives the softmax warpgroups 192 registers.

A3b takes those four. The MMA order, the score buffers, the rings and the epilogue stay as A3a has them. A3b alone is
FA4's `cta_group::1` kernel without persistence and without the TMA-store epilogue. It is not the hardware bar, which
is the pair (`gpu/encoding/TWO_CTA.md`).

## 2. The CTA

FA4's 16 warps, 512 threads (`flash_fwd_sm100.py` 307–313):

| Warps | Role | Registers |
|---|---|---|
| 0–3 | softmax, tile 0 | 192 |
| 4–7 | softmax, tile 1 | 192 |
| 8–11 | correction, both tiles | 72 |
| 12 | MMA (one elected thread) | 56 |
| 13 | idle (FA4's epilogue warp; the TMA-store epilogue's later) | 56 |
| 14 | load (one elected thread) | 56 |
| 15 | idle | 56 |

**Registers.** `(2 · 192 + 72 + 56) · 128 = 65536`, the SM's 65,536 registers. `setmaxnreg` is warpgroup-collective
(`.sync.aligned`, A30). Warps 12–15 form one warpgroup, which decreases to 56. The correction warpgroup decreases to
72. The softmax warpgroups increase to 192. A decrease never waits; an increase waits until registers are free. The
kernel is compiled with `__launch_bounds__(512, 1)`. These counts are FA4's for the causal `cta_group::1` kernel
(line 107).

## 3. Protocols

### 3.1 The row ring: α from softmax to correction

Per tile, a ring of one slot in shared memory, 128 f32, one per row. Thread `r` of the softmax warpgroup writes row
`r`'s value, and thread `r` of the correction warpgroup reads it. `r = 32 · (warp mod 4) + lane` in both warpgroups
(M12).
- **Barriers.** Full and empty barriers of 128 arrivals each: all generic proxy, no fence beyond the barriers'
  release and acquire.
- **Messages.** Per block `i ≥ 1`, α. After the loop, nothing: the softmax keeps the epilogue (§3.4).
- **One slot.** At most one α per tile is in flight. The correction arrives on α empty before it arrives on P full;
  P full gates `PVt_i`; `PVt_i` precedes `St_{i+1}`; and the softmax sends `α_{i+1}` only after it observed `St_{i+1}`.
  A second slot would never be used.
- **Both barriers stay.** The empty barrier orders each write after the read before it, so the ring's correctness
  needs nothing outside the ring.

FA4 passes `scale` through shared memory with a named barrier per warp pair, and returns the slot with a second
barrier (`mbar_softmax_stats`).

It is a new kind of ring: its producer and consumer are warpgroups writing and reading registers through shared
memory, not TMA and MMA. Its pieces are the slots, one row each per thread.

### 3.2 The rescale moves

For tile `t`, block `i`:
- **Softmax:**
  1. await St and load the row (A3a);
  2. compute the new maximum and α (§3.3);
  3. write P;
  4. send α on the row ring;
  5. publish: arrive on Pt full.
- **Correction, warp `q` of warps 8–11**, rows `32q` to `32q + 31` of Ôt:
  1. await α;
  2. if any of its 32 rows has α < 1, rescale its quadrant of Ôt: `tcgen05.ld`, multiply, `tcgen05.st`;
  3. `wait::st`, `fence::before_thread_sync`;
  4. arrive on Pt full.
- **Pt full counts 256 arrivals**: the softmax warpgroup's and the correction warpgroup's. The MMA thread's
  `PVt_i` waits for both: P written and Ô rescaled. That is FA4's `P_full_O_rescaled`.
- **Ordering.** The correction's access to Ôt must follow `PVt_{i−1}`'s completion. The softmax observed it, since
  St full's phase `i` covers `PVt_{i−1}` (A3a). The correction is ordered after the softmax's wait by the row ring's
  full barrier (release, acquire), then fences `after_thread_sync` before its `tcgen05.ld`. This is M13's chain
  passed through a second thread: assumption **"chained completion"** (§4).
- **Block 0.** The correction zeroes its quadrant of Ôt by stores of 0, unconditionally (A3a's "Ô starts at 0").
  Multiplying by α = 0 would turn a NaN in uninitialized tensor memory into NaN.

### 3.3 The lazy rescale

The softmax keeps `m` unless the block's maximum exceeds it by more than 8:
- `m_cand = max(m, max_c s_c · scale)`;
- if `m_cand − m > 8`: `m ← m_cand` and `α = 2^(m_old − m)`;
- else α = 1 and `m` stays.

So `p = 2^(s − m) ≤ 2⁸`. bf16 holds values up to 2⁸ with the same relative precision as up to 1: rounding p to bf16
costs 2⁻⁸ relative either way. `l` accumulates in f32.
O = Ô/l and LSE = (m + log₂ l)·ln 2 are unchanged in form. This is FA4's `rescale_threshold = 8.0` for 16-bit inputs
(`flash_fwd_sm100.py` 2199; `softmax.py` 341–360).

**The correction's skip** is warp-uniform: `vote.sync.any` of `α < 1` over the warp (A31). A warp whose rows all have
α = 1 skips its rescale. In a warp that rescales, rows with α = 1 multiply by 1.

**The group `warpwise(8, 4)`.** Inside the skip, each warp is converged but the warpgroup is not. Warp collectives
on the warp's own quadrant are allowed: `tcgen05.ld/st/wait`. Warpgroup protocol operations (take, await, arrive) are
not, because every thread of the warpgroup must run them together (M6). The correction's arrival on Pt full is
outside the skip. This is `gpu/ATTENTION.md` §6's `warpwise`: a grain `warp` for values uniform within a warp, and
`Group.arm(warps(8, 4), warp)` as the branch's group.

### 3.4 What stays where

- **The epilogue stays in the softmax warpgroups**, which hold `m` and `l`. So `OOwn(l, t, f)` and the store's row
  stay as A3a has them.
- **A persistent kernel** moves the epilogue to the correction warpgroup, as FA4 does, to free the softmax for the
  next tile. That needs the row ring to carry `(m, l)` at the end, and the store's rows to come from the tile rather
  than the warpgroup (the A3a review's first option, `A3.md` §6).

### 3.5 The emulated exponential

A generation-time set of columns computes `2^x` on the FMA units:
- `x ← max(x, −127)`;
- `j = ⌊x⌋` by `add.rm` of `1.5 · 2²³` and its subtraction, `f = x − j`;
- `2^f ≈ c₀ + f(c₁ + f(c₂ + f c₃))`;
- the result's bits are the polynomial's plus `j << 23`.

FA4's set for its `cta_group::1` kernels (`softmax.py` 421–460; `ex2_emu_freq = 16` from the tuning table for the
causal kernel, `flash_fwd_sm100.py` 107, and by default for the non-causal one; `ex2_emu_res = 4`,
`ex2_emu_start_frg = 1`): in fragments of 32 columns other than the first and the last, the pairs `k` with
`k mod 16 ≥ 12`, so 16 of 128 columns, chunks 5, 7, 9 and 11, columns 4 to 7 of each. (`ex2_emu_freq = 10`, 24
columns, is the 2-CTA kernel's, line 106.) The coefficients are FA4's `POLY_EX2[3]` (`utils.py`).

The error bound is computed once, exhaustively over every f32 in `[−127, 8]` on the host, with the device's rounding
modes, and added to T1's budget. It is well under bf16's 2⁻⁸, but it is measured, not assumed: 2⁻¹³·⁴⁷ relative where
2^x is normal (x ≥ −126), 2⁻¹²⁷ absolute below (`NOTES.md` §"A3b"). The host mock evaluates the same operations, so a
mock run checks the instruction sequence too.

## 4. New assumptions

- **Chained completion.** A `tcgen05` operation whose completion thread A observes through an mbarrier, followed by A's
  release arrive on a second mbarrier, then B's acquire wait on it and B's `tcgen05.fence::after_thread_sync`, is
  complete before B's later `tcgen05` operations (PTX §9.7.18.6.3, §9.7.18.11.1: the fences compose with execution
  ordering instructions "to establish an ordering between the tcgen05 operations across threads"). OBLIGATIONS A57.
- **Warp votes**, A31, become load-bearing: `vote.sync.any` gives every lane of a converged warp the same result.
- **`setmaxnreg`**, A30: a warpgroup-collective `.inc` or `.dec` changes the warpgroup's per-thread register count.
  `ptxas` allocates each role's code within it, and every warp starts with 128 (OBLIGATIONS A59).
- **FMA rounding.** `add.rm.f32`, `sub.rn.f32` and `fma.rn.f32` round as PTX specifies, with no flush to zero for the
  values in range (§9.7.3). OBLIGATIONS A58.

## 5. Plan

1. **Core:**
   - the grain `warp`, `vote.any`, and `warpwise` arms;
   - the row ring;
   - the correction's per-quadrant zero and rescale on a held Ô, under `warpwise`;
   - Pt full at 256 arrivals;
   - `setmaxnreg` on `warps(f, 4)`;
   - `ex2emu`;
   - a 512-thread builder and a 16-warp layout.
2. **Example:** `examples/attention_a3b.rac`. A3a's example stays, as the baseline the hardware session measures
   against.
3. **Harness:** the shared harness, with the new launcher name. The mock emulates the lazy rescale and the polynomial.
4. **Mutants:**
   - a rescale before the row ring's full wait;
   - a protocol operation inside a `warpwise` arm;
   - a rescale of another warp's quadrant;
   - a softmax writing a slot before its empty wait;
   - `setmaxnreg` outside a warpgroup;
   - a rescale skip decided per thread rather than per warp.
5. **Hostile review**, especially of the chained completion and `warpwise`.

## 6. Decisions

1. **FA4's 16-warp layout** and register split.
2. **The correction warpgroup only rescales.** The epilogue stays in the softmax warpgroups while the kernel is not
   persistent.
3. **A row ring with mbarriers** both ways, rather than a named barrier one way and an mbarrier back.
4. **Threshold 8** (log₂ units), FA4's for 16-bit inputs.
5. **FA4's emulation pattern and polynomial**, with the error bound measured on the host.
6. **A3a's example stays** as the measured baseline.

## 7. As built

Where the build departs from the design above as first written (2026-10-01):
- **The emulated columns** (§3.5): FA4's `cta_group::1` set, 16 columns, not the 2-CTA kernel's 24. The design had
  taken `ex2_emu_freq = 10` from the 2-CTA row of FA4's tuning table. Which columns are emulated is the example's
  choice (`emulated`); the core provides `ex2emu`.
- **Block 0's zeroing does not wait** (§3.1 sends α for blocks i ≥ 1 only; §3.2's correction steps are for those).
  The correction warpgroup zeroes its quadrants in block 0 at once: no product has touched Ô, and the first waits for
  the zeroing's publish. `publishAlpha` sends α only when the softmax side's Ô is `held`, so the ring carries `n − 1`
  messages per tile.
- **The row ring is part of the buffer.** `withCorrectedBuffer` opens a score buffer (`openScoreBuffer`, which
  `withScoreBuffer` also runs) whose P full counts 256 arrivals and which carries the α ring (`AlphaRing`): its two
  barriers and its one slot follow the buffer's barriers, and its two phase registers the buffer's phases. Sending is
  one operation with the publish (`publishAlpha`: wait for the slot, write, arrive, then publish P); receiving is one
  operation (`awaitAlpha`: wait, fence `after_thread_sync`, read, free the slot). The slot's element is
  `threadIdx.x mod 128` on both sides, which is M12's row in an aligned warpgroup. The first build had two slots,
  which the hostile review showed are never both used (§3.1).
- **Who rescales is in the buffer's type.** `ScoreBuffer(x, h)` with `h : Rescaler`: A3a's `rescaleRow` and
  `publishProbs` take a buffer whose rescaler is the softmax warpgroup, A3b's operations one whose rescaler is the
  correction warpgroup. Without it, A3b's softmax warpgroup could rescale Ô as A3a's does, racing the correction
  warpgroup on the same lanes (`rejected/attention_a3b_mutants.py`, `softmax_rescales_quadrant`).
- **`setmaxnreg`** (§2): not an operation on `warps(f, 4)` but part of `splitWarpgroups`, which splits a 512-thread CTA
  into its four warpgroups (`withShare`), as the client of the CTA's register pool (`Registers.rac`,
  `REGISTERS.md` §3):
  - each warpgroup's branch starts with `setmaxnreg` from 128 to its count, so the count covers all of the role's
    code, as `ptxas` needs to allocate it;
  - after the split's join, each warpgroup's `setmaxnreg` back to 128, so every warp holds 128 for the code after the
    split (the invalidations, the deallocation). Going back at the end of each branch, as first built, deadlocked on
    the B200: a warpgroup that finished early increased back to 128 with registers the softmax warpgroup's first
    increase to 192 still needed;
  - then a CTA barrier, so every warp holds 128 before anything after the split runs;
  - the shares exist only between the split and the join, so this is each warpgroup's only change from 128.
  Its counts must fit the pool (multiples of 8 from 24 to 256, at most 65536 registers in all; evidence). The kernel
  prints `__launch_bounds__(512, 1)`, which caps a thread at 128 registers; that every warp enters at 128 is A59's
  claim, and the register check verifies it on every build.
- **Registers:** 192, 192, 72 and 56 for both kernels. FA4's non-causal `cta_group::1` kernel uses 192, 80 and 48
  (`flash_fwd_sm100.py` 380–385); A3b keeps one split.
- **Shared roles.** The loader and the MMA issuer are A3a's, moved to `Attention.rac` (`pairLoader`, `pairIssuer`),
  generic in the warp they run on and the buffers' rescaler; A3a's example generates byte-identical CUDA.
- **The quadrant operations** take the warpgroup or warps of it under a warp vote (`ownQuadrants`), so a rescale
  without a skip needs no vote.
- **Mutants** (§5 item 4): "a softmax writing a slot before its empty wait" is not expressible, since `publishAlpha`
  waits, writes and arrives in one operation. "A rescale of another warp's quadrant" is the softmax warpgroup
  rescaling Ô (`softmax_rescales_quadrant`): its warp 0 shares quadrant 0 with the correction warpgroup's warp 8.

