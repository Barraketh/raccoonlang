# GPU library: design of a forward-attention kernel

Status: design; stages A1 and A2 built in `gpu/encoding/` (`encoding/README.md`), with the deviations it records,
none run on hardware. It extends the Blackwell layer of `DESIGN.md` to a FlashAttention-4-style forward kernel, states
what the core lacks, and plans the work in stages. `OBLIGATIONS.md` is the contract this design adds
to (§4). The lemur2 fixture `FLASH_ATTENTION_4_FORWARD.md` supplied the schedule and the correctness pressures; the
design differs from it where §2.6 says.

PTX citations are to the PTX ISA 9.4 document (docs.nvidia.com, read 2026-09-30), by section number and title.
Where the text of a section does not settle a claim (several layouts are given only as figures), the claim is marked
as such and has a hardware experiment (§4.4).

## 1. The target

### 1.1 Scope

| | A1 (first) | A2 | A3 |
|---|---|---|---|
| Masking | non-causal | causal | both |
| Sequence length | a multiple of 128, ≥ 128 | any ≥ 1 (tails masked) | any |
| Heads | a grid of `BH` heads (batch × heads), `BH` ≤ 65535 | same | same, persistent |
| Head dimension | 128 | 128 | 128 |
| Inputs | Q, K, V bf16, `[BH, seq, 128]`, 128 contiguous | same | same |
| Output | O f32 `[BH, seq, 128]`, LSE f32 `[BH, seq]` | O bf16 or f32 | same |
| Accumulation | f32 | f32 | f32 |

One CTA computes one 128-row query tile of one head (`blockIdx.x` the tile, `blockIdx.y` the head) and streams over
the head's 128-row key/value blocks. Q, K and V have the same sequence length (self-attention).

### 1.2 The math

For head `h` and query row `i`, with `scale = 1/√128`:

```text
s[i][j]  = scale · Σ_d Q[i][d] · K[j][d]
LSE[i]   = ln Σ_j exp(s[i][j])
O[i][d]  = Σ_j exp(s[i][j] − LSE[i]) · V[j][d]
```

The kernel works in base 2. The caller passes `c = scale · log₂e` as the f32 kernel parameter `scale_log2` (§3.10),
and the kernel computes `t[i][j] = c · (Q·Kᵀ)[i][j]`, so `2^t = e^s`. Over the key blocks `b = 0, 1, …` each thread
keeps its row's running maximum `m` and sum `l` in f32 registers, and tensor memory keeps the unnormalized output
`Ô`:

```text
m_b   = max(m_{b-1}, max_{j ∈ b} t[i][j])              m_{-1} = −∞
α_b   = 2^(m_{b-1} − m_b)                              (not computed for b = 0)
p[j]  = 2^(t[i][j] − m_b)                  for j ∈ b
l_b   = α_b · l_{b-1} + Σ_{j ∈ b} p[j]                l_0 = Σ p[j]
Ô_b   = α_b · Ô_{b-1} + Σ_{j ∈ b} bf16(p[j]) · V[j]    Ô_0 = Σ bf16(p[j]) · V[j]
O     = Ô_last / l_last
LSE   = (m_last + log₂ l_last) · ln 2
```

`p` enters the second product rounded to bf16 (the tensor cores take bf16 operands), while `l` sums the f32 values,
as FlashAttention does. Every `p ≤ 1` up to `ex2`'s 2 ulp, and the row's maximum contributes `p = ex2(0) = 1`
exactly (a special case of PTX §9.7.3.21), so `l_b ≥ 1`. No row of any block that A1–A2 process is fully masked
(§6), so `m_b` is finite from the first block on and no `−∞ − (−∞)` arises; A2 still guards the case (§3.9) because
it costs one select.

### 1.3 The numerical contract

The harness (`harness/attention_test.cu`, §6) computes a reference in double precision from the same bf16 inputs:
`s`, `LSE` and `O` exactly as in §1.2's first block, with `scale_log2` as passed, and rounds it to f32 before
comparing. The bounds below are worst-case bounds for the harness's range: `seq` ≤ 2¹⁴, |Q| ≤ 8, |K| ≤ 1, |V| ≤ 1.
A run passes when:

| Check | Inputs | Bound |
|---|---|---|
| T1, O | random bf16, Q in [−1, 1] and (peaked rows) in [−8, 8], K and V in [−1, 1] | every element: \|O − O_ref\| ≤ 2⁻⁷ · max\|V\| |
| T1, LSE | same | every row: \|LSE − LSE_ref\| ≤ 2⁻⁸ + 2⁻²⁰ · \|LSE_ref\| |
| T2, exact canaries | K = 0 (uniform attention); one-hot attention (below); V in multiples of 1/4; `seq` a power of two | O exactly equal to the f32-rounded reference; LSE within 2⁻²⁰ relative |
| T3, rescale canary | `scale_log2 = 1`, integer scores whose row maximum grows by 1 per block, V in [0, 1], `seq` ≤ 4096 | every element: \|O − O_ref\| ≤ 2⁻¹⁵ · max\|V\| |
| T4, hygiene | all | no NaN or Inf; guard bands around O and LSE untouched; three runs agree bit for bit |

The T1 bound for O adds four terms, each relative to `max|V|`:
- **P's rounding.** bf16 has 8 significant bits, so its unit roundoff is 2⁻⁸ and `|bf16(p) − p| ≤ 2⁻⁸ · p`; hence
  `|Σ (bf16(p) − p) · V| / l ≤ 2⁻⁸ · max|V|`. This is the dominant term, and it is not a pessimistic one: a row of
  equal scores whose `p` all round the same way comes close to it.
- **The scores.** `t = c · Σ_d q·k` summed in f32 over 128 products has absolute error at most about
  `c · 128 · 2⁻²⁴ · Σ|q·k|` ≤ `0.1275 · 2⁻¹⁷ · 1024` ≈ 10⁻³ for peaked rows (c = log₂e/√128 ≈ 0.1275), which
  perturbs each `p`, and the row maximum, by at most about 2 · 10⁻³ · ln 2 ≈ 2⁻⁹·⁵ relative. This assumes the tensor
  cores' f32 accumulation is no worse than a sequential f32 sum; how it rounds is not specified (H5).
- **The sums.** `l` and Ô accumulate at most 2¹⁴ terms, in 128 blocks of 128: at most about (127 + 128) · 2⁻²⁴
  ≈ 2⁻¹⁶ relative.
- **The approximations.** `ex2.approx` is within 2 ulp (PTX §9.7.3.21) and `rcp.rn` is IEEE (§9.7.3.13): about 2⁻²¹.

An error δ in every `p` moves O by at most 2δ · max|V| (numerator and `l` both move), so together about
2⁻⁸ + 2 · 2⁻⁹·⁵ + 2⁻¹⁵ ≈ 0.0067 · max|V|, below 2⁻⁷ ≈ 0.0078 · max|V|.

For LSE, in log₂ units: the maximum is off by at most 10⁻³, `log₂ l` by at most the relative error of `l` over ln 2
(about 2⁻⁹·⁵ / ln 2 ≈ 2⁻⁹), and `lg2.approx` by 2⁻²² (§9.7.3.20); times ln 2, below 2⁻⁸, plus the f32 rounding of
the result. Random inputs are expected to land far inside both bounds; the
bounds are what the text can defend, not an estimate of typical error.

The canaries are exact because every intermediate is. With K = 0 every score is 0, every `p` is `ex2(0) = 1`
exactly, `l = seq`, and O is the column mean of V, exact for small multiples of 1/4 and `seq` a power of two. In the
one-hot canary Q row `i` is `2048 · e_{i mod 128}` (2048 is exact in bf16) and K row `j` is `e_{j mod 128}`: query
`i` scores `2048 · c ≈ 261` (log₂ units, an exact product) against the keys with `j ≡ i (mod 128)` and 0 against the
rest, so every other `p` is `ex2` of a number near −261, which underflows to +0, and O is the mean of the matched V
rows. The reference is compared after rounding to f32: in double, `exp(−ln seq)` is not exactly `1/seq`, and
cancelled terms leave residues near 10⁻⁷⁹. The two canaries test different things. The uniform one makes O
independent of the order of V's key rows, so it checks the head-dimension placement of V (the LBO half of the
MN-major descriptor and the transpose bit) and nothing about P or the key order. The one-hot one makes P an identity
per block, so it checks P's layout in tensor memory (A23), its packing (A25), and the key order of V (SBO) exactly.
T3 checks the rescale path. `ex2` of an integer is not guaranteed to be exact (only `ex2(±0) = 1` is), so every `α`
and `p` is within 2 ulp of a power of two; bf16 rounds each `p` to that power exactly, but the f32 `α`s compound
over up to 32 blocks, about 2⁻¹⁷ in the worst case, and with V ≥ 0 no cancellation can amplify it; the bound allows
four times that.

## 2. The schedule

### 2.1 Roles

A1 keeps TinyGEMM's CTA: 256 threads, eight warps.

| Warps | Role | Per key/value block `j` |
|---|---|---|
| 0 | load (one elected thread) | TMA K_j into the K ring, V_j into the V ring (Q once, before the loop) |
| 1 | MMA (one elected thread) | `S_{j+1} = Q·K_{j+1}ᵀ` into the S ring (when `j + 1 < n`), then `Ô += P_j·V_j` |
| 2–3 | idle | |
| 4–7 | softmax, an aligned warpgroup | read S_j, update `m`, `l`, write P_j, rescale Ô, publish P_j; after the loop, the epilogue |

Thread `t` of warp `w` in the softmax warpgroup owns row `r = 32·(w mod 4) + t` of the tile: the 32x32b shape reads
and writes lane `r` of tensor memory from that thread only (PTX §9.7.18.8.1 Access restrictions, §9.7.18.2.3.1.1
Matrix fragments for shape .32x32b). Its row maximum and sum are therefore thread-local: no shuffles, no shared
memory.

The MMA thread issues `S_0` before the loop, and in iteration `j` issues `S_{j+1}` before `PV_j`, so the tensor
cores compute the next scores while the softmax warpgroup reads the current ones. The overlap is partial: with one P
buffer, pass 2 of block `j` (the exponentials) waits for `PV_{j-1}`, so the exponentials never overlap a `PV`
product. A1 does not aim at performance; FA4 gets its overlap from two query tiles instead (§2.7).

### 2.2 Where each operand lives

Shared memory (dynamic, 1024-byte aligned stages as in `DESIGN.md` §3):

| Buffer | Contents | Bytes |
|---|---|---|
| Q ring, 1 stage | Q tile: box `d 0–63` × 128 rows, then box `d 64–127` × 128 rows | 32768 |
| K ring, 2 stages | K block, same two boxes | 65536 |
| V ring, 2 stages | V block, same two boxes | 65536 |
| barriers, TMEM slot | 16 mbarriers, one word | 132 |

With the padding `withRing` leaves between one ring's barriers and the next ring's 1024-byte-aligned stages, about
166000 of 232448 bytes. A third K and V stage would bring it to about 231500, which still fits, by under 1 KB; A1 uses
two.

Tensor memory (512 columns, all 128 lanes, one allocation):

| Columns | Region | Written by | Read by |
|---|---|---|---|
| 0–127 | S buffer 0 (f32, 128 × 128) | MMA (`S = Q·Kᵀ`) | softmax (`tcgen05.ld`) |
| 128–255 | S buffer 1 | MMA | softmax |
| 256–383 | Ô (f32, 128 × 128) | MMA (`Ô += P·V`), softmax (rescale) | softmax (rescale, epilogue) |
| 384–447 | P (bf16, 128 × 128, two per column) | softmax (`tcgen05.st`) | MMA (A operand) |
| 448–511 | unused | | |

In A1 P has its own columns rather than overlaying S (the fixture overlays them; §2.6).

### 2.3 How P reaches the second product

P stays in tensor memory, and the second MMA reads its A operand from there: `tcgen05.mma.cta_group::1.kind::f16
[d-tmem], [a-tmem], b-desc, idesc, enable-input-d` (PTX §9.7.18.10.10.1 `tcgen05.mma`, the `[a-tmem]` variant of syntax 1). B is V
in shared memory. The alternative, P through shared memory, needs 32 KB more shared memory, a manual 128-byte swizzle
of the stores, and a generic-to-async proxy fence (`fence.proxy.async`, PTX §9.7.18.6.5 Shared Memory Accesses) before
the MMA may read what threads wrote. It is the fallback if experiment H1 (§4.4) cannot settle P's layout.

V needs no transpose. The second product is `Ô[i][n] = Σ_k P[i][k] · V[k][n]`, so B's element `(k, n)` is `V[k][n]`,
stored with `n` (the head dimension) contiguous: B is MN-major. The instruction descriptor's "Transpose B" bit
(bit 16, PTX §9.7.18.4.2 Instruction descriptor, Table 51) selects that, and 16-bit B may be MN-major with the plain
128-byte swizzle (§9.7.18.10.3, Table 65). The shared-memory descriptor then describes the canonical MN-major layout
`((T,8,m),(8,k)):((1,T,LBO),(8T,SBO))` (§9.7.18.3.3 Canonical Layouts), with T = 8 bf16 elements: LBO is the distance
between the two 64-element halves of the head dimension (the two boxes, 16384 bytes apart) and SBO the distance
between groups of 8 key rows (1024 bytes). Each MMA step of K = 16 key rows advances the start address by 2048 bytes,
a whole number of 1024-byte swizzle atoms, so the descriptor's base offset stays 0 (§9.7.18.4.1 Shared memory
descriptor, Table 49).

The first product needs no new descriptor kind: `S = Q·Kᵀ` is TinyGEMM's `A·Bᵀ` with both operands K-major, but its
K dimension (the head dimension, 128) spans the two 64-wide boxes of each stage, so one S is 8 MMAs, 4 per box pair.

### 2.4 Barriers

| Barrier | Count | Arrives | Waits | Its completion means |
|---|---|---|---|---|
| Q full, Q empty | 1, 1 | TMA bytes; MMA commit | MMA; loader | Q landed; every MMA reading Q completed |
| K full[2], K empty[2] | 1, 1 | TMA bytes; MMA commit after `S_j` | MMA; loader | as the stage ring |
| V full[2], V empty[2] | 1, 1 | TMA bytes; MMA commit after `PV_j` | MMA; loader | as the stage ring |
| S full[2] | 1 | MMA commit after `S_j` | softmax | `S_j` complete and visible |
| S empty[2] | 128 | softmax, after its last load of `S_j` | MMA | the buffer may be overwritten |
| P full | 128 | softmax, after `wait::st` | MMA | P_j written and Ô rescaled |
| P empty | 1 | MMA commit after `PV_j` | softmax | `PV_j` complete: P free, Ô quiescent |

Q, K and V are three instances of the existing stage ring (`withRing`), and S is an instance of the accumulator ring
(`withAccRing`). P full and P empty form one new protocol, the exchange (§3.4). Every row is a FIFO between one
producer and one consumer, so M11 (deadlock, not race) carries over.

### 2.5 One block, in order

MMA thread, iteration `j` (the first peeled, §3.4):

1. if `j + 1 < n`: await K_{j+1}; acquire S buffer `(j+1) mod 2` (wait S empty, `after_thread_sync`); 8 MMAs;
   commit to K empty; commit to S full.
2. await P full (`after_thread_sync`); await V_j; 8 MMAs `Ô (+)= P·V_j`, the first of the first block
   overwriting; commit to V empty; commit to P empty.

Softmax warpgroup, iteration `j`:

1. await S full (`after_thread_sync`) for buffer `j mod 2`.
2. Pass 1: 16 loads of 8 columns, each followed by `tcgen05.wait::ld`; `m_new = max(m, max c·s)`.
3. Acquire the exchange: wait P empty (`PV_{j-1}` complete; for `j = 0`, the phase 0 that initialization completes), `after_thread_sync`.
4. Pass 2: 16 loads again; `p = ex2(c·s − m_new)`; sum; pack pairs to bf16; 16 stores of 4 columns into P.
5. Release S (`before_thread_sync`, arrive on S empty).
6. `α = ex2(m − m_new)`; for `j > 0`, rescale Ô's row: 16 × (load 8, `wait::ld`, multiply, store 8). For `j = 0`, Ô
   holds nothing yet and the rescale emits no code.
7. Publish: `__syncwarp`, `tcgen05.wait::st`, `before_thread_sync`, arrive on P full.
8. `l = α·l + sum`; `m = m_new`. `m` starts at −∞ and `l` at 0, so for `j = 0` `α = ex2(−∞) = +0` (A26) and
   `l = sum` exactly: the first block runs the same code as the others, with no special case but the rescale's.

After the loop the softmax warpgroup waits P empty once more (the last `PV` complete), fences, loads Ô's row,
multiplies it by `rcp(l)`, and stores the row of O and its LSE, guarded by `row < seq`.

The dependencies form no cycle: `S_{j+1}` waits for the release of `S_{j-1}`, which the softmax gave in iteration
`j − 1`; `PV_j` waits for P_j, whose iteration `j` waits for `S_j` (issued in MMA iteration `j − 1`) and `PV_{j-1}`
(issued there too). The loader fills K and V in the order K_0, V_0, K_1, V_1, …; K_{j+2} waits for the release after
`S_j`, and V_{j+2} for the release after `PV_j`, both issued earlier by the MMA thread. The protocol-verification
track should check this per configuration (§7.2).

### 2.6 Deviations from the fixture

The fixture (`lemur2/fixtures/FLASH_ATTENTION_4_FORWARD.md`) runs two query tiles in ping-pong with two softmax
warpgroups and a correction warpgroup (its §1 partition and §4 protocol), P overlaid on S in tensor memory (§3), a
threshold that skips small rescales (§2 `appliedMax`, §5), an exponential split between the MUFU unit and a polynomial
(§6), and an `exp` turn between the softmax groups (§4). A1 keeps the fixture's shapes (128 × 128 tiles, head dimension 128, `cta_group::1`) and its
dataflow (§2.3), and drops the rest for one query tile:

| Fixture | A1 | Why |
|---|---|---|
| two query tiles, ping-pong | one | halves the protocol instances; the ping-pong adds no new kind of protocol (§6, A3) |
| correction warpgroup | the softmax warpgroup rescales Ô itself | P full and P empty then order both P and Ô, so Ô needs no protocol of its own |
| P overlaid on S | P in its own 64 columns | one tile needs 448 of 512 columns, so overlay buys nothing, and an overlay needs a per-column typestate (§6, A3) |
| rescale only past a threshold | always rescale (from the second block) | a skipped rescale is correct only with the deferred-scale bookkeeping; the always path is the reference |
| MUFU/polynomial exponential | `ex2.approx.ftz.f32` only | numerics fixed by one PTX statement |
| one ring for K and V | two rings | the MMA consumes K_{j+1} before V_j, which one FIFO of alternating stages would have to encode in the loader's order; two rings keep each FIFO in its consumer's order (FA4 shares one ring because its MMA order differs, §2.7). Their types differ only by the ring's lifetime, not by what the stages hold: loading V into the K ring typechecks (§5, "the wrong data in a ring") |
| the fixture's `exp` turn between the softmax groups | none | a scheduling device between two groups; with one group there is no turn |

### 2.7 The open-source reference: FA4

The performance and cross-check reference is the open-source FlashAttention-4 forward kernel for Blackwell in
Dao-AILab's `flash-attention` repository, the CuTe DSL path: `flash_attn/cute/flash_fwd_sm100.py`, called through
`flash_attn.cute.interface.flash_attn_func` (`flash_attn/cute/interface.py`). Line numbers below are at commit
`616b0e8` (2026-09-30). Closed-source libraries are not used as references.

**Matching configurations.** Our target is bf16, head dimension 128, one Q/K/V head per `(batch, head)` (no GQA
packing), no split-KV, no paging, no softcap, fixed `seq`.
- Causal: FA4 runs `cta_group::1` (`interface.py` 1080–1094 enables 2-CTA instructions only when not causal), with two
  query tiles per CTA when `seq > 128` (`interface.py` 385). That is our A2 target at A3's schedule.
- Non-causal: FA4's default for head dimension 128 and `seq > 256` uses 2-CTA instructions (`cta_group::2`, a
  cluster of two CTAs, `interface.py` 1080–1094; tuning key `(True, False, 128, False)`, `flash_fwd_sm100.py` 106).
  Setting `FA_DISABLE_2CTA=1` (`utils.py` 65, read at `interface.py` 932) gives the `cta_group::1` kernel, which is
  the configuration our design targets. The harness reports both: FA4 with 2-CTA disabled is the like-for-like
  comparison; FA4's default is the target for a later 2-CTA stage, which depends on the GEMM track's 2-CTA work
  (§7.1).

**Where FA4's source settles questions this design leaves open**, mostly for A3:

| Question | FA4 | Where |
|---|---|---|
| Roles and warps | 16 warps: softmax 0–3 and 4–7 (one per query tile), correction 8–11, MMA 12, epilogue 13, load 14, one spare | `flash_fwd_sm100.py` 307–313 |
| Tensor-memory map | S tiles at columns 0 and 128, Ô tiles at 256 and 384; P overlays the upper half of its S tile (S + 64), 64 columns of packed bf16 pairs | 351–364, 2083–2087 |
| How P is stored | `tcgen05.st.32x32b` of 32-bit registers, each two bf16 (16 repetitions per 64 columns); the PV MMA takes P from tensor memory, K-major, and V MN-major | 2105–2112, 540–547 |
| MMA order | per block: await `V_{i-1}`; then tile by tile, await that tile's P, issue its `PV_{i-1}`, then its `S_i` (tile 0 awaits `K_i` first), each `S_i` committed to its tile's barrier; the first `PV` overwrites (`zero_init`) | 1888–1955 |
| Reusing S's columns for the next S while P overlays them | no barrier: the next `S_i` is issued after the `PV` that reads P, and PTX orders an MMA's A reads before a later MMA's D writes from the same thread (§9.7.18.6.2, pipelined pair "A and metadata reads → D writes") | comment at 1933–1935 |
| One K/V ring or two | one ring (`pipeline_kv`), K and V alternating, since the MMA consumes K_0, then V_{i-1}, K_i | 1031–1041, 1851–1990 |
| P ready and Ô rescaled | one barrier phase, `P_full_O_rescaled`, which the MMA acquires before `PV` | 1900, 1966 |
| The rescale threshold | 8.0 (log₂ units) for 16-bit inputs; the correction warps skip a warp's rescale by `vote.ballot` on `scale < 1` | 2199, 2697 |
| Per-row scale between softmax and correction | shared memory (`sScale`, indexed by thread), ordered by a named barrier | 2690–2696, 2299 |
| Register split | `setmaxnreg`: softmax 192, correction 72 for causal (per the tuning table) | 79–127 |
| The polynomial exponential | on for head dimension ≤ 128 on sm_100 (`ex2_emu_freq` 10–16) | 79–127, 251–254; `softmax.py` 425–460 |

Two of these bear on A1. FA4's P store confirms the packing A23 assumes (two bf16 per 32-bit column, 64 columns for
128 keys) in a kernel that runs; it does not document which half holds the lower key index, which H1 still settles.
And FA4's MMA order would let A1 share one ring for K and V, but only by giving up A1's `S_{j+1}`-before-`PV_j`
overlap, which with one query tile is the only overlap there is. A1 keeps its order and two rings. A3, with two
query tiles, takes FA4's order and relies on the pipelined-pair rule for the overlay (a new assumption for A3, A33).
It keeps two rings, because FA4's one ring needs a consumer holding two stages at once (`gpu/encoding/A3.md` §2).

## 3. What the core needs

Each item gives its PTX form, its interface in the library's style (implicit binders elided as `{…}`), and how it
fits the discipline of `OBLIGATIONS.md` §5. Names are proposals.

### 3.1 Tensor-memory regions

Today `withTmem` hands out one `Acc` over all its columns, and `withAccRing` splits it into equal buffers from column
0. Attention needs the S ring in columns 0–255 and the exchange in 256–511.

```raccoon
// A region's handle carries its first column within the allocation.
sealed struct Tmem (a: Lifetime)(cols: Nat) : Type { scope = a }
 | mk (addr: Nat)(offset: Nat) : Tmem(a, cols)

// Splits a region into its first `k` columns and the rest, for the callback, which must hand both back with no
// tensor-core work in flight (as `Acc` always is); the whole comes back `empty`.
def splitTmem {l}{w}{a}{cols}{kx}{Sx}{kf}{Sf}
    (e: Ctx(l, Group.cta(w)))(t: Tmem(a, cols))(acc: Acc(a, AccState.empty))(k: Nat)(X: Type { kind = kx, scope = Sx })
    (body: { kind = kf, scope = Sf } (b: Lifetime) -> (c: Lifetime) -> Tmem(b, k) -> Acc(b, AccState.empty)
      -> Tmem(c, Nat.sub(cols, k)) -> Acc(c, AccState.empty) -> Ctx(l, Group.cta(w))
      -> Pair(Ctx(l, Group.cta(w)), Pair(Pair(Acc(b, AccState.empty), Acc(c, AccState.empty)), X)))
    : Pair(Ctx(l, Group.cta(w)), Pair(Acc(a, AccState.empty), X))
```

PTX: none; addresses are `(lane << 16) | column` (§9.7.18.1.1 Tensor Memory Addressing). The split is a
generation-time check that `k` is a positive multiple of 32 below `cols` (the allocation unit, §9.7.18.1.2); whether
MMA and `tcgen05.ld/st` addresses need more alignment than that is not stated in the text, so A1 uses offsets that
are multiples of 64 (assumption A27). Discipline: the halves live in fresh lifetimes `b` and `c`, and their `Acc`
tokens are linear, so they are rejoined only when both are handed back, which is when no role holds either.

The offset must reach every use of a region's address, or a half would alias the other. Today `mmaFirst`,
`mmaNext` and `storeAcc` read `Expr.var(t.addr)` directly, and `withAccRing` passes `t.addr` on to `accBuffer`. So the
fields become private in effect: one accessor, `tmemBase(t) = addr + offset`, is the only way the core reads a
region's address (every current use is rewritten to it), and only `withTmem`'s own `dealloc` names the allocation's
address, which it keeps itself. `storeRows` takes an address expression and needs no change once its callers pass
`tmemBase`. A mutant runs `mmaFirst` on the upper half of a split and checks, in a `checks/` unit test of the emitted
code, that its address carries the offset.

### 3.2 Holding a stage across a loop

Q is loaded once and read by every `S_j`. Its ring has one stage; the MMA thread awaits it once and keeps it until
the loop ends.

```raccoon
def holdStage {r}{m}(rd: Ready(r, m)): ReadyUsed(r, m)
def fixedReadyUsed (r: Lifetime)(m: Lifetime): Fixed(ReadyUsed(r, m))
```

PTX: none (`releaseByMma` commits at the end). Discipline: `ReadyUsed(r, m)` already means "a stage that MMAs issued
by the thread of `m` read, to be released by that thread's commit"; more MMAs reading it change nothing, and
releasing a stage no MMA read commits nothing new. The ring's consumer endpoint stays consumed while the stage is
held (`await` took it), so the same ring cannot hand out a second stage meanwhile. `Fixed` lets the held stage travel
in loop state (M5).

### 3.3 The first product: two K-major rings into an accumulator buffer

```raccoon
// S = A·Bᵀ over K = 128, A from the held stage of ring `ra`, B from the ready stage of ring `rb`, each stage two
// 64-wide boxes of 128 rows; overwrites the accumulator buffer (the first of 8 MMAs has enable-input-d = 0).
def mmaScores {k}{m}{ra}{ca}{rb}{cb}{q}
    (e: Ctx(k, Group.lane))(w: Elected(m))(ringA: Ring(ra, ca))(a: ReadyUsed(ra, m))(ringB: Ring(rb, cb))(b: Ready(rb, m))
    (accs: AccRing(q, 128))(acc: AccFree(q, m))
    : Pair(Ctx(k, Group.lane), Pair(ReadyUsed(ra, m), Pair(ReadyUsed(rb, m), AccFilling(q, m))))
```

PTX: `tcgen05.mma.cta_group::1.kind::f16 [d], a-desc, b-desc, idesc, p` (§9.7.18.10.10.1), with the existing
K-major descriptors (A11). Generation checks: both rings' boxes are 64 × 128 and the buffer has 128 columns.
Discipline: as `mmaFirstInto`; the result is committed by the existing `commitAcc`, and K is released by the
existing `releaseByMma`. The existing `mmaStage` generalizes to take the A and B stage bases and a box count; TinyGEMM
is the case of one box pair from one stage.

### 3.4 The exchange: P and Ô between the softmax warpgroup and the MMA thread

A one-buffer protocol over a 256-column tensor-memory region (Ô at +0, P at +128), whose writer is an aligned
warpgroup and whose reader is the MMA thread. It is the stage ring turned around: threads fill a tensor-memory buffer
and the tensor cores release it.

```raccoon
inductive OState : Type
 | fresh : OState   // no MMA has written Ô: its contents are undefined
 | held : OState    // Ô holds the sum of the products so far

sealed struct Exchange (x: Lifetime) : Type { scope = x }
 | mk (base: Expr)(bars: Nat)(wPhase: Nat)(rPhase: Nat) : Exchange(x)

// Endpoints before they are taken, and taken.
sealed inductive ExWriter (x: Lifetime) : Type { kind = lin, scope = x }
sealed inductive ExReader (x: Lifetime) : Type { kind = lin, scope = x }
sealed inductive ExWriterAt (x: Lifetime)(m: Lifetime)(f: Nat)(o: OState) : Type { kind = lin, scope = union(x, m) }
sealed inductive ExReaderAt (x: Lifetime)(m: Lifetime)(o: OState) : Type { kind = lin, scope = union(x, m) }

// The writer's buffer: P free to write, chunks 0 to `next - 1` written; Ô's rows the warpgroup's to rescale.
sealed inductive PFree (x: Lifetime)(m: Lifetime)(f: Nat)(o: OState)(next: Nat) : Type { kind = lin, scope = union(x, m) }
// The reader's buffer: P and Ô visible to the tensor cores; P and Ô read or written by MMAs not yet committed.
sealed inductive PReady (x: Lifetime)(m: Lifetime)(o: OState) : Type { kind = lin, scope = union(x, m) }
sealed inductive PUsed (x: Lifetime)(m: Lifetime) : Type { kind = lin, scope = union(x, m) }
// Ô after the last product completed, visible to the warpgroup.
sealed inductive OFinal (x: Lifetime)(m: Lifetime)(f: Nat) : Type { kind = lin, scope = union(x, m) }

def withExchange {l}{w}{a}{kx}{Sx}{kf}{Sf}
    (e: Ctx(l, Group.cta(w)))(t: Tmem(a, 256))(acc: Acc(a, AccState.empty))(X: Type { kind = kx, scope = Sx })
    (body: { kind = kf, scope = Sf } (x: Lifetime) -> Exchange(x) -> ExWriter(x) -> ExReader(x) -> Ctx(l, Group.cta(w))
      -> Pair(Ctx(l, Group.cta(w)), X))
    : Pair(Ctx(l, Group.cta(w)), Pair(Acc(a, AccState.empty), X))

// Writer side: the aligned warpgroup `warps(f, 4)`, all 128 threads together.
def takeExWriter (e: Ctx(m, warps(f, 4)))[aligned: Eq(Nat, Nat.mod(f, 4), 0)](ex: Exchange(x))(p: ExWriter(x))
    : Pair(Ctx(m, warps(f, 4)), ExWriterAt(x, m, f, OState.fresh))
def acquireP (e: Ctx(k, warps(f, 4)))(ex: Exchange(x))(at: ExWriterAt(x, m, f, o)): Pair(Ctx(k, warps(f, 4)), PFree(x, m, f, o, 0))
// All of P from S: per chunk c of 8 columns, in order, load chunk c of S, run `step`, store its 8 values as chunk c of P.
def writeP (e: Ctx(k, warps(f, 4)))(ring: AccRing(q, 128))(full: AccFull(q, m, f))(ex: Exchange(x))(p: PFree(x, m, f, o, 0))
    (step: (c: Nat) -> F32x8(k, Grain.thread) -> Ctx(k, warps(f, 4)) -> Pair(Ctx(k, warps(f, 4)), F32x8(S, u)))
    : Pair(Ctx(k, warps(f, 4)), Pair(AccFull(q, m, f), PFree(x, m, f, o, 16)))
// No code while Ô is `fresh`.
def rescaleO (e: Ctx(k, warps(f, 4)))(ex: Exchange(x))(p: PFree(x, m, f, o, c))(alpha: Val(S, u, DType.f32))
    : Pair(Ctx(k, warps(f, 4)), PFree(x, m, f, o, c))
def publishP (e: Ctx(k, warps(f, 4)))(ex: Exchange(x))(p: PFree(x, m, f, o, 16)): Pair(Ctx(k, warps(f, 4)), ExWriterAt(x, m, f, OState.held))
def finishExWriter (e: Ctx(k, warps(f, 4)))(ex: Exchange(x))(at: ExWriterAt(x, m, f, OState.held)): Pair(Ctx(k, warps(f, 4)), OFinal(x, m, f))
def closeExWriter (e: Ctx(k, warps(f, 4)))(o: OFinal(x, m, f)): Ctx(k, warps(f, 4))

// Reader side: the elected MMA thread.
def takeExReader (e: Ctx(m, Group.lane))(w: Elected(m))(ex: Exchange(x))(r: ExReader(x)): Pair(Ctx(m, Group.lane), ExReaderAt(x, m, OState.fresh))
def awaitP (e: Ctx(k, Group.lane))(ex: Exchange(x))(at: ExReaderAt(x, m, o)): Pair(Ctx(k, Group.lane), PReady(x, m, o))
// Overwrites Ô when `o` is `fresh`, accumulates when `held`.
def mmaPV (e: Ctx(k, Group.lane))(w: Elected(m))(ex: Exchange(x))(p: PReady(x, m, o))(ring: Ring(r, c))(v: Ready(r, m))
    : Pair(Ctx(k, Group.lane), Pair(PUsed(x, m), ReadyUsed(r, m)))
def commitPV (e: Ctx(k, Group.lane))(w: Elected(m))(ex: Exchange(x))(u: PUsed(x, m)): Pair(Ctx(k, Group.lane), ExReaderAt(x, m, OState.held))
def finishExReader (e: Ctx(k, Group.lane))(at: ExReaderAt(x, m, OState.held)): Ctx(k, Group.lane)
```

What each emits:

| Operation | Code |
|---|---|
| `withExchange` | P full (count 128) and P empty (count 1), initialized as `withAccRing` does (thread 0 then completes P empty's phase 0, so the writer starts at phase 0); `inval` at close |
| `takeExWriter` / `takeExReader` | the side's phase register: writer 0, reader 0 (one buffer, so no stage register) |
| `acquireP` | wait P empty at the writer's phase; `tcgen05.fence::after_thread_sync` |
| `writeP` | per chunk c, in order: S's chunk as §3.5 loads it; `step`'s code; 4 × `cvt.rn.bf16x2.f32` (pairs `2i+1, 2i` so element `2i` is in the low half); `__syncwarp`; `tcgen05.st.sync.aligned.32x32b.x4.b32` at P + 4c, the warp's lane quadrant |
| `rescaleO` | `held`: per 8 columns of Ô: `__syncwarp`; `tcgen05.ld.32x32b.x8`; `tcgen05.wait::ld`; 8 multiplies; `tcgen05.st.32x32b.x8`. `fresh`: nothing |
| `publishP` | `__syncwarp`; `tcgen05.wait::st`; `tcgen05.fence::before_thread_sync`; arrive on P full; flip the phase |
| `finishExWriter` | wait P empty at the writer's phase; `tcgen05.fence::after_thread_sync` |
| `awaitP` | wait P full at the reader's phase; `tcgen05.fence::after_thread_sync` |
| `mmaPV` | 8 × `tcgen05.mma.cta_group::1.kind::f16 [Ô], [P + 8s], vdesc(s), idesc, p`; the first with `p` false when `fresh` |
| `commitPV` | `tcgen05.commit` to P empty; flip the phase |

PTX: `tcgen05.st` (§9.7.18.8.4), `tcgen05.wait::st` (§9.7.18.8.5), the A-in-tensor-memory form of `tcgen05.mma`
(§9.7.18.10.10.1), `cvt.rn.bf16x2.f32` (§9.7.10.24 `cvt`: "the value converted from input a is stored in the upper
half"), the MN-major descriptor (§2.3). The publish and consume sequences are PTX's canonical pattern "Non-pipelined
instructions, different thread" (§9.7.18.6.4.4): the producer waits for its own asynchronous tensor-memory accesses
(`wait::st` here, `wait::ld` in PTX's example), fences `before_thread_sync`, and arrives; the consumer waits, fences
`after_thread_sync`, and issues. PTX's example has an `ld` before the MMA (an anti-dependence); ours is a `st` before
the MMA (a true dependence), which the fence rules of §9.7.18.6.3 cover the same way (A20). §9.7.18.8.5's Example 2
(`st`, `wait::st`, then an MMA in the same thread) shows `wait::st` is what keeps an MMA from racing ahead of a store.

Discipline:
- **Linear sealed fieldless tokens.** P and Ô may be touched by the warpgroup only while it holds `PFree`, and by the
  MMA thread only while it holds `PReady`/`PUsed`. The only way from one to the other is through a barrier phase.
- **Typestate.** `OState` records whether an MMA has written Ô, and the core reads it so that neither side touches
  Ô's undefined contents: `mmaPV` overwrites when `fresh` and accumulates when `held`, and `rescaleO` emits nothing
  when `fresh`. So each role writes one loop body for every block. The first `publishP` and the first `commitPV` move
  their sides to `held`. `PFree`'s index `next` is 0 after `acquireP` and 16 after `writeP`, which writes every chunk
  of P, in order, once, and `publishP` requires 16: a skipped chunk would feed the previous block's probabilities to
  the MMA.
- **`Fixed`.** `fixedExWriterAt` and `fixedExReaderAt`; the first iteration of each side is peeled (`loopPeeled`),
  so the loop state after it is `held` on both sides. Peeled, not copied: each role passes one body, generic in
  `OState`, as both the first iteration and the rest.
- **Thread-bound registers (M6).** The writer's phase register is declared by the whole aligned warpgroup, which runs
  every writer operation together, as `takeAccConsumer` does; the reader's by the elected thread.
- **Groups.** Writer operations need `warps(f, 4)` with the alignment proof, so a diverged or misaligned group cannot
  issue the `.sync.aligned` loads and stores, and each warp stays in its lane quadrant. Every writer operation that
  emits a `.sync.aligned` instruction starts it with `__syncwarp`, as `storeRows` does: `writeP` and `rescaleO` before
  each load or store, and `publishP` before `tcgen05.wait::st`. The last matters because the types allow a spin loop
  just before `publishP`: after `releaseAcc` the warpgroup holds its S-ring endpoint again and may `awaitAcc` the next
  S first (which does not deadlock, since `S_{j+1}` is issued before the MMA waits for P_j), and a barrier wait's spin
  loop may leave a warp diverged (`DESIGN.md` §4).
- **Releasing only quiescent storage (M7).** Each side is linear and belongs to the exchange's scope, which the
  callback's result cannot name, so both are used up before `withExchange` closes, and only their finishers use them
  up without handing them on. The writer's finish waits for the last commit, so no MMA reads P or writes Ô when the
  region goes back to `splitTmem`; the reader's emits nothing, since its every product was committed to that wait.
- **`Key`-guarded internals.** The new templates are `Stmt` builders, unsealed data that reach a kernel only through
  sealed operations (`OBLIGATIONS.md` §7).

### 3.5 Reading an accumulator buffer into registers

The softmax warpgroup reads S; today an `AccFull` only authorizes `storeTile`.

```raccoon
// Eight f32 values, one per column, of this thread's row.
struct F32x8 (l: Lifetime)(u: Grain) : Type { scope = l }
 | mk (v0: Val(l, u, DType.f32)) … (v7: Val(l, u, DType.f32)) : F32x8(l, u)

// `step` on each chunk c of 8 columns of this thread's row of the consumer's current buffer, columns 8c to 8c+7,
// in order: n / 8 loads, unrolled at generation.
def eachChunk (e: Ctx(k, warps(f, 4)))(ring: AccRing(q, n))(full: AccFull(q, m, f))
    (step: (c: Nat) -> F32x8(k, Grain.thread) -> Ctx(k, warps(f, 4)) -> Ctx(k, warps(f, 4)))
    : Pair(Ctx(k, warps(f, 4)), AccFull(q, m, f))
```

`writeP` (§3.4) reads S's chunks the same way, and stores what its step returns as P's. As first built, a public
`loadAcc8` took the chunk index and its bound as evidence, and a public `storeP` likewise; the client then spelled out
the 16 calls of each pass, since evidence is discharged only at literal indices. Both are internal now.

PTX: `__syncwarp`; `tcgen05.ld.sync.aligned.32x32b.x8.b32`; `tcgen05.wait::ld` (§9.7.18.8.3, §9.7.18.8.5), as
`chunks` emits today. Discipline: needs `AccFull`, so it cannot precede `awaitAcc` or follow `releaseAcc` (which
consumes it). The row is the executing thread's (§4.1, M12). The values are thread-grain `Val`s of the context's
lifetime, so they cannot outlive the block that loaded them.

### 3.6 Fp32 math and constants

The AST needs no change: float arithmetic prints through the untyped `BinOp`s (`Val` carries the type), and the
instructions without a C operator print as inline assembly with an output operand, as `tmemLoad8` does.

| Operation | Emits | PTX |
|---|---|---|
| `fadd`, `fsub`, `fmul` (pure) | `(a + b)`, `(a - b)`, `(a * b)` | — |
| `fmax` (pure) | `max(a, b)` (CUDA's float overload) | §9.7.3.12 `max` |
| `fma` (exists) | `fmaf(a, b, c)` | — |
| `select` (pure, new public wrapper) | `(c ? a : b)` | — |
| `lt` (exists, generic in the type) | `(a < b)` on f32 values too | — |
| `fconst(e, bits)` | `mov.b32 %0, bits;` into a fresh f32 (`bits` < 2³², else a generation error) | §9.7.10.3 `mov` |
| `ex2(e, x)` | `ex2.approx.ftz.f32` | §9.7.3.21 `ex2` |
| `lg2(e, x)` | `lg2.approx.ftz.f32` | §9.7.3.20 `lg2` |
| `rcp(e, x)` | `rcp.rn.f32` | §9.7.3.13 `rcp` |

`ex2`, `lg2`, `rcp` and `fconst` take the emitter because they declare a register; their result has the grain of
their input (`fconst`: uniform). None is collective, so any group may use them, including `diverged`. The asm-value
builder is `Key`-guarded (M8): a client cannot emit an arbitrary template. The conversion to bf16 is not a public
operation: `writeP` packs, so a client cannot swap halves (A25), and A2's bf16 output converts inside `storeO`.

nvcc contracts `(a * b) - c` into an FMA by default (`-fmad=true`), so the printed arithmetic is not bit-for-bit the
sequence of roundings §1.2 writes. That is within §1.3's bounds, and the canaries are unaffected (their products are
exact). Where the rounding sequence matters the example should call `fma` itself; the library does not pass
`-fmad=false`.

### 3.7 Rank-3 tensor maps for heads

Q, K and V are `[BH, seq, 128]`. A rank-3 map (dimensions 128, `seq`, `BH`; box 64 × 128 × 1) zero-fills rows past
`seq` within each head (A28), which A2's tails need, and the box lands in shared memory exactly as the rank-2 box
does, so rings and descriptors are unchanged.

```raccoon
// A tensor map parameter over [BH, seq, 128] bf16 whose box is `spec` × 1 head.
sealed struct HeadMap (l: Lifetime)(spec: TmaSpec) : Type { scope = l }
 | mk (name: String) : HeadMap(l, spec)

// The 128-row block at row `row` of this CTA's head (blockIdx.y, which the caller cannot choose): both 64-wide halves,
// one box each, through the one map at the one row.
def fillBlock {…}(e: Ctx(n, Group.lane))(ring: Ring(r, cfg))(s: Slot(r, m))(map: HeadMap(L, RingCfg.a(cfg)))(row: Val(S, u, DType.u32))
    : Pair(Ctx(n, Group.lane), ProducerAt(r, m))
```

PTX: `cp.async.bulk.tensor.3d.shared::cluster.global.mbarrier::complete_tx::bytes` (§9.7.10.28.5.3). Host:
`cuTensorMapEncodeTiled` with rank 3. This changes `Cuda.MapEncoding`, which today prints a rank-2 encoding from two
scalar names, and `Check.launcher` (I6), which checks that shape; §7.1 proposes one change shared with the GEMM
track's TMA store.

As built, A1 and A2 keep rank-2 maps over `[BH·seq, 128]` (`encoding/README.md`), so `Cuda.rac`, `Check.rac`,
`Spec.rac` and the launcher proof are unchanged. A2's tails do without the zero-fill: a last key block that runs past
`seq` reads the next head's rows (or zeros past the matrix), which the mask's `kv < seq` turns into −∞ scores and
`p = 0`, and the rows of a last query tile past `seq` read the next head's Q rows and are never stored (§3.8). The
cost is a hazard rank-3 maps would not have: a non-finite value in those rows of V makes the masked `0 · V` NaN (§5).
As first built, the fill was `fillHead`, `fill`'s shape with head maps: two maps and four coordinates, so one half of a
stage could come from another map or row; `fillBlock` takes one map and one row, as `fillPage` does.

### 3.8 Output

```raccoon
// Where this CTA's 128 rows of O and LSE lie, and the authority to write them once.
sealed struct AttnOut (l: Lifetime)(t: DType) : Type { scope = l }
 | mk (o: String)(lse: String)(seq: Expr) : AttnOut(l, t)
sealed inductive OOwn (l: Lifetime)(t: DType) : Type { kind = lin, scope = l }

// Each thread stores its own row: Ô's 128 columns times `inv`, and `lse`, if the row is inside the sequence.
def storeO (e: Ctx(k, warps(f, 4)))(ex: Exchange(x))(o: OFinal(x, m, f))(inv: Val(S, u, DType.f32))(lse: Val(S2, u2, DType.f32))
    (out: AttnOut(L, t))(own: OOwn(L, t)): Pair(Ctx(k, warps(f, 4)), OFinal(x, m, f))
```

The row is `blockIdx.y · seq + 128 · blockIdx.x + 32 · (warp mod 4) + lane`, computed by the core, and the guard is
`128 · blockIdx.x + 32 · (warp mod 4) + lane < seq`. The guard is against `seq`, not the array's rows: with a tail,
a row past `seq` is the next head's first row, which another CTA writes (S5). O's elements are written with scalar
stores in A1 (f32) and A2 (bf16 through `static_cast`); A3 may take the GEMM track's TMA store (§7.1).

As built, the conversion is `static_cast<__nv_bfloat16>` of the f32 product, cuda_bf16.h's conversion from float
(`__float2bfloat16`, round to nearest even), chosen by O's type: `storeO` is generic in `t`, and the builders accept
f32 and bf16 only. A kernel built with `__CUDA_NO_BFLOAT16_CONVERSIONS__` does not compile.

### 3.9 Masks

A2's masks are values, not branches: `t' = select(kv < seq ∧ (¬causal ∨ kv ≤ q), t, −∞)`, with `kv` and `q` computed
by the core from the chunk, the block and the thread (`maskedScores(e, launch, block, c, v: F32x8) → F32x8`). A
per-thread branch would make the warpgroup `diverged`, which the next `tcgen05.ld` refuses (M3). The `−∞ − (−∞)`
guard is `m_use = select(lt(m_new, lowest), 0, m_new)`, with `lowest = fconst(0xff7fffff)` (the most negative finite
f32).

As built (`encoding/Core.rac`): `maskedScores(e, mask, block, c, v)` takes, in place of the launch, a sealed `Mask` that
only the builders make (the kernel's `seq`, whether it is causal, and −∞, which the builder declares once). It
requires a `warps(f, 4)` context, converged (the causal row's `__shfl_sync` is a warp collective), and c < 16 (a
generation error otherwise), and emits `kv0 = 128·block + 8c`, the
limit `min(seq, q + 1)` (causal; the row `q` declared first, after `__syncwarp`, since the select of the minimum would
evaluate it in part of the warp) or `seq`, and eight `t'_j = (kv0 + j < limit) ? t_j : −∞`. The guard is the
example's (`usable`), applied to the maximum each block's exponents and rescale use; the running maximum keeps the
unguarded value. No row of a launch the launcher accepts is masked whole in its first block, since key 0 is inside the
sequence and at or before every query, so with finite scores the guard never fires; it costs one select per block. For `seq` a multiple
of 128 the non-causal kernel computes A1's values, every mask being true, up to nvcc's contraction: the select between
`c · s` and the subtraction of the maximum likely keeps `(c · s) − m` from becoming one FMA, a rounding of `p` well
inside §1.3's bounds.

### 3.10 The kernel builder

```raccoon
struct AttnLaunch (l: Lifetime)(spec: TmaSpec) : Type { scope = l }
 | mk (q: HeadMap(l, spec))(k: HeadMap(l, spec))(v: HeadMap(l, spec))(out: AttnOut(l, DType.f32))
      (seq: Val(l, Grain.uniform, DType.u32))(blocks: Val(l, Grain.uniform, DType.u32))(q0: Val(l, Grain.uniform, DType.u32))
      (scale: Val(l, Grain.uniform, DType.f32)) : AttnLaunch(l, spec)

// Forward attention over BH heads of `seq` rows, one CTA of 256 threads per 128 query rows of one head, with its
// host launcher. The launcher refuses (cudaErrorInvalidValue) seq = 0, seq not a multiple of 128 (A1), BH = 0,
// BH > 65535, and BH·seq·128 ≥ 2³¹.
def attentionKernel (name: String)
    (body: (l: Lifetime) -> Ctx(l, Group.cta(256)) -> AttnLaunch(l, TmaSpec.mk(64, 128)) -> OOwn(l, DType.f32)
      -> TmemPermit(l) -> Ctx(l, Group.cta(256)))
    : Program
```

Parameters: `Q_map`, `K_map`, `V_map`, `O`, `LSE`, `BH`, `seq`, `scale_log2` (f32). `blocks` is `seq / 128` in A1
and `min(ceil(seq/128), blockIdx.x + 1)` for causal A2, computed once by the builder so that every role runs the
same trip count from one value. `scale_log2` is the caller's; any value is memory-safe.

As built for A2: `attentionKernel(name, causal, t, body)`, with causal and O's element type `t` generation-time
choices (one kernel each), `AttnLaunch(l, spec, t)` carrying the `Mask`, and `blocks = ceil(seq/128)` (non-causal) or
`min(ceil(seq/128), blockIdx.x + 1)` (causal). The launcher accepts any `seq ≥ 1` (grid `(ceil(seq/128), BH)`) and
keeps A1's other refusals; `BH·seq·128 < 2³¹` also keeps `seq + 127` from wrapping.

The launch contract that remains to the caller, as for `tmaGemmKernel`: Q, K and V are device arrays of `BH·seq·128`
bf16 elements, O one of `BH·seq·128` elements of its type, LSE one of `BH·seq` f32 elements, and O and LSE are
distinct from each other and from the inputs.

## 4. New obligations

### 4.1 Discipline

- **M12, row affinity.** Every per-row access (tensor-memory loads and stores of the 32x32b shape, `storeO`'s global
  row, A3's shared-memory row channels) computes its row from the executing thread (`warp mod 4`, lane), never from
  an argument. Per-row data (the statistics registers) never crosses threads except through a core protocol that
  indexes both sides the same way. So each thread's `m` and `l` describe the row its loads read. The statistics
  registers are data, not protocol state: they choose no barrier, phase or buffer, so they need no endpoint token and
  M6 does not apply to them; a wrong value is a wrong result, not a race. They are thread-bound anyway, by M2: they
  are declared in the warpgroup's side of a split, so no other role can name them.
- **M13, thread-written tensor memory.** A thread-written tensor-memory operand is published only by the sealed
  sequence `__syncwarp`, `wait::st`, `fence::before_thread_sync`, arrive, and consumed only after wait,
  `fence::after_thread_sync` (PTX §9.7.18.6.4.4). This extends M9 to the opposite direction.
- **M14, coverage indices.** Where a buffer must be written whole before it is published (P), its token counts the
  chunks written, and the publishing operation requires the full count.

### 4.2 Rows for `OBLIGATIONS.md` §6

A new §6.9, and additions to §6.1 and §6.6:

| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `fadd`, `fsub`, `fmul`, `fmax`, `select` | argument values | nothing (pure) | the value, grain the join of its inputs' | — |
| `fconst`, `ex2`, `lg2`, `rcp` | a context; `fconst`: bits < 2³² | a declaration and one instruction | the value, grain of the input (`fconst` uniform) | A26 |
| `splitTmem` | `Acc(a, empty)`, `cta` context, 0 < k < cols, 64 ∣ k (A27 is stated for multiples of 64) | nothing | two disjoint regions; closes on both `Acc`s, handing back `Acc(a, empty)` | A27, S4 |
| `holdStage` | `Ready(r, m)` | nothing | `ReadyUsed(r, m)`: the stage stays unreleased until `releaseByMma` | A12 |
| `mmaScores` | `ReadyUsed(ra, m)`, `Ready(rb, m)`, `AccFree(q, m)`, `Elected(m)`; boxes 64 × 128, n = 128 | 8 `tcgen05.mma`, the first overwriting | `ReadyUsed` of both, `AccFilling` | A11 |
| `eachChunk` | `AccFull(q, m, f)`, aligned warpgroup | per chunk c < n / 8: `__syncwarp`, `tcgen05.ld.32x32b.x8`, `wait::ld`, then the step's code | the step sees the thread's row, columns 8c–8c+7 | A13, A14 |
| `withExchange` | `Acc(a, empty)` of 256 columns, `cta` context | P full (128), P empty (1), thread 0 completing P empty's phase 0 with one arrive at initialization; `inval` at close | writer and reader, linear and of the exchange's scope, so finished before the close; hands back `Acc(a, empty)` | A6–A8 |
| `takeExWriter` / `takeExReader` | aligned warpgroup / elected lane | the side's phase register | the side, bound to that warpgroup or thread | M6 |
| `acquireP` | writer side | wait P empty, `after_thread_sync` | `PFree(…, 0)`: the last product completed, P and Ô quiescent and visible | A6, A13, A21 |
| `writeP` | `AccFull(q, m, f)` of a 128-column buffer, `PFree(…, 0)` | per chunk c < 16: S's chunk loaded as by `eachChunk`, the step's code, 4 `cvt.rn.bf16x2.f32`, `__syncwarp`, `tcgen05.st.32x32b.x4` | `PFree(…, 16)`: every chunk of the thread's row of P written once, in order (pending `wait::st`) | A13, A14, A19, A23, A25 |
| `rescaleO` | `PFree(…, o, c)` | `held`: 16 × (`__syncwarp`, `ld.x8`, `wait::ld`, 8 `mul`, `st.x8`); `fresh`: nothing | the thread's row of Ô scaled (pending `wait::st`) | A14, A19, A22 |
| `publishP` | `PFree(…, 16)` | `__syncwarp`, `wait::st`, `before_thread_sync`, 128 arrivals on P full, flip | P and Ô handed to the reader | A19, A20 |
| `awaitP` | reader side | wait P full, `after_thread_sync` | `PReady`: P and Ô written and visible to the tensor cores | A6, A20 |
| `mmaPV` | `PReady(x, m, o)`, `Ready(r, m)` of a 64 × 128-box ring, `Elected(m)` | 8 `tcgen05.mma` with A in tensor memory, MN-major B; the first overwriting when `o` is `fresh` | `PUsed`, `ReadyUsed` | A23, A24 |
| `commitPV` | `PUsed(x, m)`, `Elected(m)` | `tcgen05.commit` to P empty, flip | the buffer returns to the writer when the MMAs complete | A12, A21 |
| `finishExWriter` | writer side, `held` | wait P empty, `after_thread_sync` | `OFinal`: every product completed; none in flight | A6, A13 |
| `storeO` | `OFinal`, `OOwn`, aligned warpgroup | fence, per 8 columns `ld`, `wait::ld`, scale, guarded stores; guarded LSE store | the CTA's rows of O and LSE written once | A14, S5 |
| `maskedScores` (A2) | 8 scores, the chunk, the block | `select`s against the core's `kv`, `q` and `seq` | the masked scores | — |
| `fillBlock` | as `fill`; one `HeadMap` with the ring's first box, stages of two 64 × 128 boxes | `arrive.expect_tx`, two TMA loads at this CTA's head, columns 0 and 64 of one row | as `fill` | A9 |
| `attentionKernel` | a body | the kernel and its launcher (extent checks, three rank-3 encodings, grid `(seq/128, BH)`) | a `Program` | A17, I6 |

The public-surface audit of `OBLIGATIONS.md` §7 gains:
- the pure math operations and `maskedScores`, and the unsealed `F32x8.mk`: they build values from the library's own
  `Val`s, and a `Val` carries no authority;
- `holdStage`: it mints no authority, only renames a stage already held;
- `fixedReadyUsed`, `fixedExWriterAt`, `fixedExReaderAt`: evidence for fieldless one-valued families only;
- `splitTmem`: it mints two `Acc` tokens from one, over disjoint columns (the core's arithmetic), and takes back both
  before it returns the one; that is sound only while every address use goes through `tmemBase` (§3.1);
- `fillBlock`: as `fill`, with the head coordinate and the columns the core's;
- `eachChunk` and `writeP`: they run the client's step on values only, loaded under the buffer's `AccFull`;
- `closeExWriter` and `finishExReader`: they consume authority.

### 4.3 Platform assumptions

| # | Assumption | Source | Confidence |
|---|---|---|---|
| A19 | `tcgen05.st.sync.aligned.32x32b.xN.b32 [taddr], {…}` is warp-collective, every thread giving the same `taddr`; warp w of a warpgroup may access only lanes 32·(w mod 4) to +31 (text), and thread t writes lane 32·(w mod 4)+t, N consecutive columns (Figure 186 only; exercised for `ld` by the GEMMs). It is asynchronous; `tcgen05.wait::st` waits for every earlier `tcgen05.st` of the thread. | PTX §9.7.18.8.1, §9.7.18.8.4, §9.7.18.8.5, §9.7.18.6.2.1.2 | high (text); not exercised |
| A20 | A tensor-memory write by one thread (`st`, `wait::st`, `fence::before_thread_sync`, `mbarrier.arrive`) is visible to a `tcgen05.mma` issued by another thread after it observes that phase and fences `after_thread_sync`. | PTX §9.7.18.6.3, §9.7.18.6.4.4 (whose examples are `ld` → `mma` and `mma` → `ld`), §9.7.18.8.5 Example 2 (`st`, `wait::st`, `mma` in one thread) | medium-high |
| A21 | The barrier arrival of `tcgen05.commit` happens after the tracked MMAs have finished reading their tensor-memory A operand, so a thread that observes it and fences `after_thread_sync` may overwrite A. | PTX §9.7.18.12.1 ("track the completion of all the prior asynchronous tcgen05 operations"), §9.7.18.6.2.1.1 | medium-high |
| A22 | Within one warp, `tcgen05.ld` then `tcgen05.st` to the same address is ordered (the rescale's read-modify-write), as is `st` then `ld`. | PTX §9.7.18.6.2 (pipelined pairs `ld → st`, `st → ld`) | high |
| A23 | With `tcgen05.mma.cta_group::1.kind::f16 [d], [a], b-desc, idesc, p`, M = 128, A bf16 and not transposed: row i of A is lane i, K elements are packed two per 32-bit column with the lower K index in the low 16 bits, and each K = 16 step reads 8 columns from the given address. | PTX §9.7.18.10.10.1 (the form); the layout only in Figure 217 (§9.7.18.10.5.4) and CUTLASS's `SM100_MMA_F16BF16_TS` | **low-medium; H1** |
| A24 | B MN-major with 128-byte swizzle: instruction-descriptor bit 16 set; shared-memory descriptor LBO = 16384 (between 64-element halves of N), SBO = 1024 (between groups of 8 K rows), start advanced 2048 bytes per K step, base offset 0. | PTX §9.7.18.3.1–3, §9.7.18.4.1–2, §9.7.18.10.3 | **medium; H2** |
| A25 | `cvt.rn.bf16x2.f32 d, a, b` rounds to nearest even and puts `a` in the upper half of `d`. | PTX §9.7.10.24 `cvt` | high |
| A26 | `ex2.approx.ftz.f32` is within 2 ulp and maps −∞ to +0; `lg2.approx.ftz.f32` is within 2⁻²² absolute on (0.5, 2) and 2⁻²² relative for other positive inputs; `rcp.rn.f32` is IEEE. Functional only. | PTX §9.7.3.21, §9.7.3.20, §9.7.3.13 | high |
| A27 | MMA D and A addresses and `tcgen05.ld/st` addresses may start at any column that is a multiple of 64 within the allocation. | PTX §9.7.18.1.1 (addressing); no alignment rule found in the text | **medium; H3** |
| A28 | `cp.async.bulk.tensor.3d` with a rank-3 map zero-fills (and counts) elements outside the tensor in every dimension, and a 64 × 128 × 1 box lands as the rank-2 box does. | PTX §9.7.10.28.5.3; CUDA driver `cuTensorMapEncodeTiled` | high |
| A29 | All `tcgen05` instructions of a kernel must use one `.cta_group`. | PTX §9.7.18.7.1, §9.7.18.10.10.1 | high (text) |
| A30 | (A3) `setmaxnreg.{inc,dec}.sync.aligned.u32` must be executed by every warp of a warpgroup, identically, with a synchronization between two of them. | PTX §9.7.21.5 | high (text) |
| A31 | (A3) `vote.sync.any.pred` / `vote.sync.ballot.b32` with a full mask in a converged warp gives every lane the same result. | PTX §9.7.15.10 | high |
| A32 | *Withdrawn in review.* `tcgen05.ld.red` (load with a row maximum) is not available on sm_100a: PTX §9.7.18.8.3 lists it for sm_101a/sm_110a and the sm_101f, sm_103f and sm_110f families only. FA4 uses it on sm_103 only (`use_ldred_rowmax`, `flash_fwd_sm100.py` 245–250). | PTX §9.7.18.8.3 | — |
| A33 | (A3) An MMA's reads of its tensor-memory A operand are ordered before a later MMA's writes of D to the same columns when one thread issues both (P overlaid on S, then the next S). | PTX §9.7.18.6.2 (pipelined pair "A and metadata reads → D writes"); FA4 relies on it (§2.7) | high (text) |

### 4.4 Hardware experiments

| # | Question | Experiment | Settles |
|---|---|---|---|
| H1 | The layout of a bf16 A operand in tensor memory (A23) | A one-CTA probe: write a known matrix to tensor memory with `tcgen05.st` (packed as A23 says), multiply by an identity B from shared memory, read D back with `tcgen05.ld`; compare. Variants swap the halves and the column step. T2's one-hot canary checks the same thing inside the kernel. | A23; if no variant works, P goes through shared memory (§2.3) |
| H2 | The MN-major B descriptor (A24) | T2's uniform canary (K = 0) checks the head-dimension half (LBO, the transpose bit): O is the column mean of V, which a wrong LBO scrambles. It cannot see the key order, since the mean does not depend on it; the one-hot canary, where P is an identity per block, checks SBO and the K step exactly. A probe with B a permutation matrix localizes a failure. | A24 |
| H3 | Column alignment of MMA and ld/st addresses (A27) | The A1 kernel itself (offsets 0, 128, 256, 384); a probe at offsets 32 and 96 for completeness. | A27 |
| H4 | The ordering of A20 and A21 | Stress runs of the A1 kernel under compute-sanitizer, and a mutant (built with the Key, never printable by a client) that omits `wait::st` in `publishP`, run to see whether the hardware exposes the missing wait at all. A pass does not prove A20; a failure of the mutant shows the harness can see the hazard. | supports A20, A21 |
| H5 | Tensor-core f32 accumulation error (T1's margin) | Compare S alone (a debug build storing S) with a double reference over random inputs. | the T1 bound |

## 5. Mutations to refuse

`encoding/rejected/attention_mutants.py` holds the roles (`encoding/Attention.rac`) with one mistake each:

| Mutant | Refused by |
|---|---|
| reading S before the MMA commits it (`eachChunk` without `awaitAcc`) | `eachChunk` needs `AccFull` |
| releasing S, then loading it again in pass 2 | `releaseAcc` consumes `AccFull` (`LinearReused`) |
| issuing `S_{j+1}` into a buffer the softmax is still reading | `mmaScores` needs the `AccFree` of `acquireAcc`, which waits for the 128 releases |
| writing P while `PV_{j-1}` still reads it (`writeP` without `acquireP`) | `writeP` needs `PFree`, which only `acquireP`'s wait makes |
| rescaling Ô while a product accumulates into it | `rescaleO` needs `PFree` (same wait) |
| rescaling Ô in the first block, when no MMA has written it | not a mistake: `rescaleO` emits nothing while Ô is `fresh` |
| accumulating the first product into undefined Ô | not expressible: `mmaPV` overwrites exactly when its `PReady` is `fresh` |
| issuing `PV_j` before the softmax publishes P_j | `mmaPV` needs `PReady`, which only `awaitP` makes |
| publishing P unwritten | `publishP` needs `PFree(…, 16)`, which only `writeP` makes from `acquireP`'s `PFree(…, 0)` |
| publishing P with a chunk unwritten or written twice | not expressible: `writeP` writes all 16 chunks, once each, in order; the per-chunk store is internal |
| publishing without `tcgen05.wait::st`, or without the fences | not expressible: `publishP` and `awaitP` emit them (M13) |
| spinning in `awaitAcc` between `writeP` and `publishP` | allowed, and safe: `publishP` reconverges the warp before `wait::st` (§3.4) |
| using the upper half of a `splitTmem` as if it started at column 0 | not expressible: every address use adds the offset through `tmemBase` (§3.1) |
| storing O before the last product completes | `storeO` needs `OFinal`, which only `finishExWriter`'s wait makes |
| storing O twice, or rows another CTA owns | `OOwn` is linear; rows come from the block and thread indices |
| the exchange writer taken by one thread, or by warps 3–6 | `takeExWriter` needs `warps(f, 4)` and `f mod 4 = 0` |
| a causal or tail mask by per-thread `if` around the loads | the arm is `diverged`, which `eachChunk` does not accept |
| a mask of the caller's own (non-causal in a causal kernel, or another `seq`) | `Mask` is sealed; only the builders make one |
| releasing the Q stage inside the loop, then using it | `releaseByMma` consumes `ReadyUsed` |
| closing tensor memory with a product in flight, or the S ring or a stage ring undrained | each side is linear and of its protocol's scope, so it is used up before the close (`LinearUnused` otherwise), and only its finisher uses it up without handing a side back: the waiting finishers `finishProducer`, `finishAccProducer`, `finishStores` and `finishExWriter` (whose `OFinal` only `closeExWriter` ends), and the code-free `finishConsumer`, `finishAccConsumer`, `finishExReader` and `closeExWriter` (`OBLIGATIONS.md` M15) |
| loading one half of a stage from another map or row | not expressible: `fillBlock` takes one map and one row for both halves |

What the design cannot refuse. None of these is a race, a broken collective or a protocol error; each is a wrong
result, a deadlock, or a question the types do not ask. The harness (§1.3) is what catches the first kind.

- **Omitting or corrupting the rescale.** Nothing forces `rescaleO` before `publishP` (A3's threshold legitimately
  skips it), nor that its `α` is `2^(m_old − m_new)`. T3 catches it.
- **Stale or misused statistics.** Not updating `m` or `l`, computing `p` against the old maximum, or dividing by
  the wrong sum. T1 and T3 catch these.
- **The wrong data in a ring.** Loading V into the K ring (both are `Ring(r, cfg)` with equal boxes), or a K block at
  the wrong row. A tensor tag on `HeadMap` and `RingCfg` would refuse the first; it is cheap, but it changes
  `TmaSpec`, which the GEMM track shares, so it is left to that merge (§7.1).
- **A block row at or past `seq`.** With the rank-2 maps over `[BH·seq, 128]` (`encoding/README.md`), `fillBlock`
  adds the caller's row to the head's first row unbounded, so a row ≥ `seq` loads the next heads' rows (or zeros past
  the matrix, which TMA clips). The maps are only read, so it is a wrong result, not a race. A2's tails rely on it:
  the part of a last block past `seq` is masked.
- **Non-finite values in the rows a tail block reads past `seq`** (the next head's V, or a paged cache's unused rows
  of a last page). The masked keys' `p` are 0, but `0 · ∞` and `0 · NaN` are NaN, so such a value makes O NaN in every
  query row whose keys include that block. A correctness hazard under non-finite inputs, not a safety one; the launch
  contracts ask for finite V there, and rank-3 maps (§3.7) would remove it for the contiguous kernel.
- **Storing P chunk c from S chunk c′ ≠ c.** `writeP` hands each step its own chunk of S; another chunk's values
  could reach it only through a register.
- **Omitting the causal or tail mask** (A2), or masking with the wrong comparison. T1's causal and tail sizes catch
  it.
- **Trip counts that differ between roles.** A deadlock (M11), not a race, as for the GEMMs. The builder's single
  `blocks` value makes it unlikely rather than impossible.
- **The row-affinity rule itself** (M12) is kept by construction in the core; a future operation that took a row
  index from its caller would break it, and only review of §4.2's rows would notice.

## 6. A staged plan

**A1: non-causal, correct on hardware.**
- Core: `Tmem` offset and `splitTmem` (§3.1); `holdStage`, `fixedReadyUsed` (§3.2); `mmaScores` and the generalized
  `mmaStage` (§3.3); the exchange (§3.4); `eachChunk` and `F32x8` (§3.5); the math of §3.6; `HeadMap`, `fillBlock`,
  and rank-3 encodings in `Cuda.MapEncoding` and `Check.launcher`, with `Spec.rac` and the launcher checker's proof
  updated (§3.7); `AttnOut`, `OOwn`, `storeO` (§3.8); `attentionKernel` (§3.10).
- Example: `examples/attention.rac`, the schedule of §2.
- Harness: `harness/attention_test.cu` (`seq` ∈ {128, 256, 1024, 4096}, `BH` ∈ {1, 3, 16}); T1–T4; launcher
  refusals (`seq` = 0, `seq` = 200, `BH` = 0, `BH` = 65536, `BH·seq·128` ≥ 2³¹).
- Reference and benchmark: FA4 (§2.7) on the same GPU, same inputs, through `flash_attn_func` with `causal=False`,
  bf16, head dimension 128, `(batch, heads) = (1, BH)`, once with `FA_DISABLE_2CTA=1` (the like-for-like
  `cta_group::1` kernel) and once by default (2-CTA). Its O is a second numerical cross-check (|O_ours − O_FA4|
  within twice T1's bound plus FA4's bf16 rounding of its output, 2⁻⁸ · |O_FA4|, since both are approximate); its time is the performance reference. Throughput is
  reported (TFLOP/s at 4·BH·seq²·128 FLOPs, CPU time under load noted), not judged, in A1. No closed-source library is
  benchmarked.
- Checks: `check.sh` generates and compiles it against `stub/` (adding `tcgen05.st` and the rank-3 copy to the stub
  headers); `attention_mutants.py` (§5); `checks/` unit tests of the emitted code: rank-3 encodings, `mmaFirst` on the
  upper half of a `splitTmem` carrying the offset (§3.1), and a program that spins in `awaitAcc` between writing P
  and `publishP` emitting `__syncwarp` before `wait::st` (§3.4); OBLIGATIONS.md §3, §5, §6 and §7 updated.
  On hardware: ptxas, the harness, compute-sanitizer, and experiments H1–H5, H1 and H2 first.

**A2: causal, tails, bf16 output.** Built (2026-10-01) for the contiguous and the paged kernel, with rank-2 maps
(§3.7, `encoding/README.md`); not run on hardware. As built: §3.7–§3.10's "as built" paragraphs; the examples generate
a non-causal f32 and a causal bf16 kernel each; the harnesses run both at the sizes below (the contiguous one
also at A1's), and have run against a host mock of the runtime (`encoding/NOTES.md`).
- Core: masks (§3.9); `blocks` for causal; `storeO` for bf16; the launcher accepts any `seq` ≥ 1.
- Example: `examples/attention_causal.rac`, or one example with a `causal` parameter.
- Harness: causal and non-causal at `seq` ∈ {1, 127, 129, 1000, 4096}, `BH` ≥ 3 so that every head has neighbours;
  bf16 output with T1's bound plus bf16 rounding of O (2⁻⁸ · |O_ref| more). In the contiguous `[BH, seq, 128]` layout
  there are no rows past `seq` to guard with sentinels: row `seq` of one head is row 0 of the next. A store past a
  head's end would overwrite the next head's first rows, racing with the CTA that owns them, so T1 on every head and
  T4's bit-for-bit agreement across runs are what check the guard.
- Reference and benchmark: FA4 with `causal=True`, which is FA4's `cta_group::1` path whatever the flag (§2.7).
- Checks: a mutant masking by a per-thread branch (refused, §5). A store guarded by the array's rows instead of
  `seq` is not expressible, since `storeO` computes its guard.

**A3: performance.** In order of expected return, each measured against the previous:
- Two query tiles per CTA in ping-pong with two softmax warpgroups (the fixture's schedule): two S rings and two
  exchanges; a CTA of 384 or 512 threads; the tensor memory is then full (2 × 128 for Ô, 2 × 128 for S), so P
  overlays S. The overlay needs a new token: a buffer of the S ring whose consumer converts it in place, reading
  chunk c of S before writing the P column that overlaps it, with a per-chunk index in the type as in M14, and whose
  release is the MMA's commit after `PV` rather than 128 arrivals. It also needs the fixture's `exp` turn, a
  one-token protocol between the two warpgroups (scheduling only).
- A correction warpgroup that rescales Ô off the softmax's critical path, fed the per-row `α` through a shared-memory
  row channel (a ring of 128-float buffers, full and empty barriers of 128 arrivals, indexed by M12's row on both
  sides), and the exchange split into a P handoff and an Ô handoff.
- The rescale only past a threshold: a warp-uniform condition from `vote.sync.any` (A31) and a new group,
  `warpwise(f, c)`, in which each warp is converged but not the warpgroup: warp collectives (`tcgen05.ld/st` of the
  warp's own quadrant) are allowed, warpgroup protocol operations (take, acquire, publish, release: every thread must
  run them together, M6) are not. Without that distinction some warps would advance a ring's registers and others
  not, and 128-arrival barriers could complete a phase with arrivals from different steps.
  A branch that skips `rescaleO` carries the writer's `PFree` in its state, so `PFree` needs a `Fixed` family too
  (`fixedPFree`), with the chunk index fixed at 16 for the branch.
- FA4's MMA order (§2.7), relying on A33 for the overlay; with A1's two rings rather than FA4's one, since the
  stage ring's consumer holds one stage at a time (`gpu/encoding/A3.md` §2).
- `setmaxnreg` per role (A30), a warpgroup-collective that fits `warps(f, 4)`.
- One pass over S instead of two, keeping the row in registers (128 registers of S per thread; FA4's softmax runs at
  192 registers). `tcgen05.ld.red` would give the maximum for free but is not on sm_100a (A32, withdrawn).
- The polynomial `exp2` on the FMA units for part of each row (the fixture's §6, FA4's `ex2_emu_freq`), with its error
  in T1's budget.
- A persistent schedule over (tile, head) pairs, with `forTiles`, and the TMA-store epilogue from the GEMM track.
  `withExchange` is one-shot today, and it needs a `cta` context, so it cannot be reopened inside a role's tile loop:
  a persistent kernel needs a tile transition on both sides (`OFinal` back to a `fresh` writer after `storeO`, and the
  reader's `held` back to `fresh`), each side's phase register continuing across tiles as the accumulator ring's do.
- 2-CTA MMA for the non-causal case, FA4's default there, once the GEMM track provides `cta_group::2`.

## 7. Interactions with the other tracks

### 7.1 `Gpu.rac` sections this touches

| Section | Change | GEMM-performance track | Merge |
|---|---|---|---|
| sm_100a instructions | new templates: `tcgen05.st`, MMA with A in tensor memory, rank-3 TMA, `cvt`, `ex2`, `lg2`, `rcp`, `mov.b32` | adds 2-CTA MMA, cluster, multicast and TMA-store templates | additive on both sides; textual conflicts only |
| Tensor maps and the stage ring | `HeadMap`, `fillBlock`; rank-3 `MapEncoding` in `Cuda.rac`, `Check.launcher`, `Spec.rac`, launcher proof | TMA store needs an output map (f32 or bf16, other box), multicast loads for clusters | **conflict**: both change `MapEncoding` and I6. Proposal: one change, landed first, making an encoding carry its dtype, rank, extents as host expressions over the launcher's scalars, box, and swizzle; both tracks build on it |
| Tensor memory and the accumulator | `Tmem` gains an offset; `splitTmem`; `mmaStage` generalized; MN-major descriptors (LBO), instruction-descriptor transpose bit | 2-CTA allocation and MMA (`cta_group::2`, M = 256), whose `instrDesc` and `Tmem` change too | **conflict** in `Tmem`, `instrDesc`, `smemDesc`, `mmaStage`. Proposal: land the offset and the descriptor parameters (major-ness, LBO) first, as a refactor with no behaviour change to the GEMMs |
| Persistent GEMM: accumulator ring | `eachChunk`, `writeP`; `accBuffer` adds the region's offset | TMA-store epilogue changes `storeRows` / `storeTile` | small; both are additive |
| Kernel builders | `attentionKernel` | 2-CTA and cluster launches (cluster dimensions in the launcher) | additive, but `Cuda.Launcher` may gain cluster dims; attention takes the change unused |
| Control, groups | none in A1; `warpwise` and `Grain.warp` in A3 | none expected | A3 only |

A29 constrains both tracks: a kernel must use one `.cta_group`. If the GEMM track makes the CTA group a parameter of
the core, it should be an index of the kernel (of `Ctx` or of the builder), so that one kernel cannot mix them;
attention uses `cta_group::1` throughout.

### 7.2 What the protocol-verification track should model

- **The exchange** as a transition system: a one-buffer ring whose producer is 128 threads arriving together and whose
  consumer releases by commit, with the `OState` ghost (fresh until the first commit) and M14's chunk count; safety:
  no `st` to P or Ô between `awaitP` and the matching commit's completion, and no MMA between `acquireP` and the
  matching `publishP`.
- **The S ring** with a warpgroup consumer is the existing accumulator ring; the new use is reading it (`eachChunk`,
  `writeP`) between await and release.
- **The held stage**: a one-stage ring whose consumer holds one stage across a loop of MMAs and releases it once.
- **The whole A1 schedule per configuration** (stages 1/2/2, S buffers 2, `n` blocks up to a bound): all four
  protocols and the loader, MMA and softmax programs of §2.5, including the branch on `j + 1 < n` and the peeled first
  iterations. Safety as above; also deadlock freedom, which `OBLIGATIONS.md` does not claim but which the schedule's
  correctness needs and which is easy to get wrong when adding a role.
- **The tcgen05 ordering axioms** A19–A22 as the model's rules for tensor-memory accesses, citing §9.7.18.6; the
  proofs should say which of them each safety property uses, since A20 and A21 are inferred rather than quoted.
- For A3: two instances of each protocol, the `exp` turn, the row channel, and the `warpwise` group's rule that
  protocol operations stay outside warp-uniform branches.

## 8. Review

An adversarial review (2026-09-30, one reviewer, against the PTX ISA 9.4 text and `Gpu.rac`) found no blocker: no
race, phase alias or deadlock in the schedule of §2.5, and every refusal of §5 held. It checked, and found correct,
the phase registers and arrival counts of the exchange (still correct under the later change of start state, a
relabelling: the writer now starts at phase 0, on a phase that initialization completes), quiescence at every close, the `OState` transitions, holding
Q across the loop, that the MMA thread's loop is writable with `loopPeeled` and a uniform `branch`, the MN-major
descriptor, the `[a-tmem]` MMA form, `cvt`'s half order, A22, A29, the math accuracies, the canaries' exactness, and
every cited section number. What changed:

| Finding | Change |
|---|---|
| `publishP`'s `tcgen05.wait::st` (`.sync.aligned`) could follow a spin loop that left a warp diverged, since the types allow `awaitAcc` between the last `storeP` and `publishP` (an S2 violation) | `publishP` starts with `__syncwarp`; M13 says so; a unit test in the A1 checks (§3.4, §4.1, §6) |
| `mmaFirst`, `mmaNext` and `storeAcc` read `t.addr` directly, so a `splitTmem` half could alias the other | one accessor `tmemBase`, through which every address use goes; §4.2's audit notes `splitTmem` depends on it; a unit test (§3.1) |
| bf16's unit roundoff is 2⁻⁸, not 2⁻⁹; the score and summation terms were understated; the LSE bound had no derivation | §1.3 rewritten: worst-case bounds for a stated range, O at 2⁻⁷ · max\|V\|, LSE at 2⁻⁸, each term derived |
| T3's "every α is a power of two" is not guaranteed by `ex2`'s 2 ulp; a relative bound fails near zero | T3 uses V ≥ 0 and a bound relative to max\|V\|, derived |
| the uniform canary cannot see key-order errors | §1.3 and H2 say which canary checks what |
| A32 is false: `tcgen05.ld.red` is not on sm_100a | withdrawn; A3's plan no longer uses it |
| "rows past `seq` keep their sentinels" cannot be checked in a contiguous layout | A2's plan relies on per-head T1 and T4 instead |
| the public-surface audit missed `fixed…`, `splitTmem`, `F32x8.mk`, `fillHead`, `maskedScores`; §3.10 lacked the launch contract | both added (§4.2, §3.10) |
| A3: the exchange cannot be reopened in a tile loop; a skipped rescale needs `Fixed(PFree)` | both in A3's plan |
| nits: `loadAcc8`'s bound, f32-rounded reference, FMA contraction, shared-memory padding, a float comparison for the `−∞` guard, the `x: Exchange(x)` name clash, "second syntax form", divide versus `rcp`, A19's figure-only mapping, A20's second citation, the overlap A1 actually gets | each fixed where it stands |

After the review the coordinator set the reference implementation: FA4 from Dao-AILab's `flash-attention` (§2.7),
never a closed-source library. §2.7 cites its source where it settles schedule questions, and §6 benchmarks against
it; FA4's MMA order also added A33 for A3.
