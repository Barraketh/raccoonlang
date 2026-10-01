# Paged attention on the A1 kernel: design

Status: P1 built (2026-10-01), as §6 records: `Core.rac`'s paged-attention section, `examples/paged_attention.rac`,
`harness/paged_attention_test.cu` and `rejected/paged_attention_mutants.py`; checked by generation, the certificate,
the mutants and a compile against `gpu/stub/`, not run on hardware. P2 is design only. It extends A1
(`gpu/ATTENTION.md`, as built in `gpu/encoding/`) to a KV cache stored in pages. It is the second step of
`gpu/encoding/README.md`.

## 1. The target

**P1, paged prefill.** A1's kernel with K and V read from a paged cache. Everything else stays as A1 has it:
- non-causal;
- one fixed `seq`, a multiple of 128, for every sequence;
- head dimension 128;
- Q and O contiguous `[B·H, seq, 128]`.

The pieces:

- **The cache.** K and V are each `[pages, H, 128, 128]` bf16: a page holds 128 consecutive keys of every head. It is
  addressed as a rank-2 tensor `[pages · H · 128, 128]`, so the rows of page `p`, head `h`, start at
  `(p · H + h) · 128`.
- **The table.** `block_table [B, maxPages]` u32. Entry `[b][j]` is the physical page holding keys `128j` to
  `128j + 127` of sequence `b`. `maxPages ≥ seq / 128`.
- **The grid.** `(seq / 128, B · H)`, so CTA `(x, y)` computes query tile `x` of sequence `b = y / H`, head `h = y % H`.
  `H` is a generation-time constant of the kernel (the core divides only by constants), with one kernel per head
  count.

P2, below, is decode with append. It is where the resource questions of `docs/SEPARATION_PILOT.md` §6–§7 arise.

## 2. What changes from A1

Only the loader's addresses and the kernel's parameters change. The MMA thread, the softmax warpgroup, the S ring,
the exchange and the epilogue do not.

**The loader**, for block `j`:
1. reads `p = block_table[b][j]` with a guarded global load (`gload`), zero outside the table;
2. computes the row `(p · H + h) · 128`;
3. issues `fill` for K's and V's boxes at that row.

The loader is one elected thread, so `p` is that thread's value and no other thread needs it.

```raccoon
// The paged cache's map: a rank-2 bf16 tensor map over [pages · H · 128, 128] with the ring's box.
sealed struct PageMap (l: Lifetime)(spec: TmaSpec) : Type { scope = l }
 | mk (name: String)(heads: Nat) : PageMap(l, spec)

// The block table: a read-only u32 matrix [B, maxPages], read by the loader.
sealed struct PageTable (l: Lifetime) : Type { scope = l }
 | mk (name: String)(rows: Expr)(cols: Expr) : PageTable(l)

// Fills a stage of the ring with K's or V's 128 rows of block `j` of this CTA's sequence and head: reads the block's
// page from the table, then loads its two 64-wide boxes. The sequence, head and page row are the core's; the caller
// gives only `j`.
def fillPage {…}(e: Ctx(n, Group.lane))(ring: Ring(r, cfg))(s: Slot(r, m))(table: PageTable(L))(cache: PageMap(L, RingCfg.a(cfg)))
    (j: Val(S, u, DType.u32)): Pair(Ctx(n, Group.lane), ProducerAt(r, m))
```

**The kernel builder** `pagedAttentionKernel`:
- **Parameters:** `Q_map`, `K_map`, `V_map`, `O`, `LSE`, `block_table`, `B`, `seq`, `max_pages`, `pages`, `rows_q`,
  `rows_kv`, `dim`, `scale_log2`.
- **Requirements:**
  - `seq > 0`, `seq mod 128 = 0`, `B > 0`, `B · H ≤ 65535`;
  - `rows_q = B · H · seq` and `rows_kv = pages · H · 128`, the extents the maps use;
  - `dim = 128`;
  - `max_pages ≥ seq / 128`;
  - every extent below 2³¹.
- **Grid:** `(seq / 128, B · H)`.

## 3. Why it is safe

The paged loads add no hazard, whatever the table holds:
- **Memory.** A TMA box is clipped to its map's extents and zero-fills the rest (A9). Its coordinates are signed 32-bit,
  and the computed row wraps modulo 2³² before the copy reads it as signed. So every load reads only the cache, or
  zeros.
- **Protocol.** `fillPage` is `fill` with another address: the same arrive, the same two boxes into the same stage, so
  the stage ring's argument (`docs/SEPARATION_PILOT.md` §4) is unchanged.
- **The table read.** It is a guarded load of a read-only input, and the kernel writes neither the table nor the cache.

What the table's contents decide is **correctness**, not safety. A wrong page gives wrong attention, never a race or an
access outside the cache. So P1 needs no validation of the table and no ownership of pages. The launch contract says
what the caller promises: the table holds valid pages, and the cache's pages for those entries hold the sequences' K
and V.

## 4. P2: decode with append

The first kernel with a resource question.
- **The shape.** One query per sequence, or a few for speculative decoding.
- **The append.** Before attending, the kernel writes the new K and V into the tail of the sequence's last page, at
  `position = len_b`.
- **Exclusivity.** Two sequences must not share a last page, or two CTAs append into one page.

The encodings `docs/SEPARATION_PILOT.md` §6–§7 propose are the ones to build:
- a write token for the tail of a page chosen at run time, indexed by its register's handle;
- a scoped read lease over the page's prefix, held by the attention reads while the tail is written;
- for the table, a choice: validate it on the device, a pre-pass checking that last pages are distinct, or state
  distinctness in the launch contract, as P1 does for validity.

That choice decides whether the write token is minted by a checked operation or taken on trust at the launch. It is
the pilot's open question 3 in concrete form.

P2's query shape (a few rows per sequence) also needs a different tile than A1's 128 query rows. The decode schedule is
FlashDecoding's split over the key blocks, with its merge (`docs/SEPARATION_PILOT.md` §6, "split-KV partials"). That
schedule is its own design, after P1.

## 5. Checks

- **An example,** `examples/paged_attention.rac` (H = 8). It generates, passes `render`'s certificate and compiles
  against the stubs.
- **A harness,** `harness/paged_attention_test.cu`, with the host-side reference:
  - pages shuffled across sequences;
  - a table with out-of-range entries (the kernel must stay safe; the result is garbage, which the harness only
    requires to be finite);
  - T1–T4 of `ATTENTION.md` §1.3 for valid tables.
- **Mutants:** a caller-chosen page row (refused: `fillPage` takes only the block index), and a write into the cache
  (refused: no operation writes a `PageMap`).

## 6. P1 as built

As §1–§3 design it, with these decisions where the design left room:

- **Parameters.** The kernel takes `Q_map`, `K_map`, `V_map`, `O`, `LSE`, `block_table`, `B`, `seq`, `max_pages`,
  `scale_log2`. The launcher (`paged_attention_launch`) takes the arrays in their place (`Q`, `K`, `V`) and adds
  `pages`, `rows_q`, `rows_kv` and `dim`, which only it reads: `Q`, `K`, `V`, `O`, `LSE`, `block_table`, `B`, `seq`,
  `max_pages`, `pages`, `rows_q`, `rows_kv`, `dim`, `scale_log2`.
- **"Every extent below 2³¹"** is three requirements: `B · H · seq · 128` (every row and element index of Q, O and
  LSE fits a signed coordinate and a u32, as A1 requires), `pages · H · 128` (every row of the cache is addressable by a
  signed coordinate; a valid table's rows then never wrap) and `B · max_pages` (every index of the table fits a u32).
  The others follow: `pages`, `max_pages`, `seq` and `B` are each bounded by one of them.
- **`fillPage`** checks at generation that the ring's stage is two 64 × 128 boxes (`headStage`): it loads both boxes
  through the one cache map, typed by the first box, and a page is 128 rows. The table's guard is `gload`'s:
  `b < B ∧ j < max_pages`, else the value 0, which is then an ordinary page number. Both bounds hold for every `b` the
  grid makes and every `j` below `blocks`, but `j` is the caller's, so the guard is what keeps the read in the table.
- **`H`** is checked at generation to be from 1 to 65535; a kernel with more heads could never launch (`B ≥ 1`).
- **The table is read twice per block,** once by each `fillPage` (K's, then V's). Both reads are of the same entry of
  a read-only input, so they agree; reading it once would need a page value the caller holds, which `fillPage`'s
  signature rules out (`NOTES.md`).
- **The example shares no code with A1's.** Its issuer, softmax warpgroup and CTA are copies of
  `examples/attention.rac`'s (`NOTES.md`, "Paged attention").

The generated kernel (2677 lines, 182 KB with its launcher) differs from A1's only in its parameters, the four TMA
loads of the loader's loop, the two table reads before them, and the launcher.
