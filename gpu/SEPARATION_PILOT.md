# Encoding the GPU library's resources in Raccoon: pilot

Status: **draft, for discussion** (2026-10-01). The meanings it gives are still on paper. Decisions 6 and 7 landed in
`gpu/` (44143d9), and paged attention's append took a checked claim (`gpu/encoding/P2.md`) rather than §7's
encodings. It assumes `docs/implemented/SCOPE_CONTAINMENT.md` and `docs/implemented/NO_OPAQUE.md`.

## 0. The aim

Find the cleanest safe encoding, in Raccoon, of what the GPU library's tokens stand for. The goal is to support kernels
like paged attention.

"Safe" is argued on paper. Each token family gets a **meaning**: the pieces of ownership it stands for, in the notation
of §1. Each operation gets an informal argument that it moves pieces only as the hardware allows. Proving the encoding
correct in Raccoon, without changing it, is later research. It will likely need propositions about linearity and
scopes in the language.

"Clean" is judged by reviewing the working code once it runs: whether it reads well, and whether it carries
incidental complexity. `gpu/Gpu.rac` supports less than this design targets, so it is a starting point, not a
baseline.

Each protocol below gives:
1. its pieces, on paper;
2. an encoding in Raccoon, starting from `Gpu.rac` where it has one;
3. why the encoding keeps the pieces valid;
4. candidate changes to try in the code.

## 1. Pieces, on paper

A **piece** says what part of the running kernel's state is someone's to use. Pieces **combine**, written `a · b`, and
`✓ a` means `a` could be held all at once. Combining is commutative and associative, and `ε` (nothing) combines with
anything.

- `x ↦q v`: a share `q ≤ 1` of location `x`, which holds `v`. Shares add, values agree; 1 permits writing, any share
  reading. A share also records which proxies may access `x` next (§2.6).
- `●a`, `◯b`: authoritative ghost state `a` and a fragment `b` of it, valid together when they agree.
- `each t ∈ g. P(t)`: what every thread `t` of group `g` holds.
- `a ⇝ b`: a frame-preserving update. For every `f`, `✓ (a · f)` implies `✓ (b · f)`.

Threads hold pieces. So do operations in flight, until they complete, and barriers, between a phase's arrivals and its
waiter.

## 2. What carries the meaning

| Raccoon feature | Carries |
|---|---|
| A sealed linear token | an exclusive piece: it cannot be copied (no second holder), or dropped (it is handed back or consumed by an operation that accounts for it) |
| An unrestricted value confined to a scope | a shared piece, valid while its scope is open. Every copy is gone when the scope closes, so the lender gets the whole back without counting (`SCOPE_CONTAINMENT`) |
| A callback that binds a lifetime | lending: the callback's result cannot mention the lifetime, so nothing lent leaves it |
| A linear token that belongs to the lent scope | conservation: the scope closes only once every such token is used up, and an operation uses one up without handing it on only once every use is finished (`gpu/encoding`'s finishers; `gpu/Gpu.rac` still has the callback return a `…Done` token) |
| Sealing | only the module's operations mint or consume pieces |
| `Ctx(l, g)`, linear | the one emitter: code is emitted in the order authority flows, into block `l`, run by group `g` |
| An evidence argument | a fact about generation-time values (`0 < S`, alignment) |
| A token's registers | its runtime state (which stage, which phase). The token's meaning reads them, so a fieldless token means "the registers hold some stage `s` and round `r`, and …" |

Two consequences shape everything below:
- **SIMT.** A block is emitted once and run by every thread of its group. So a token held by group `g` means
  `each t ∈ g. P(t)`: the group's joint pieces.
- **Generated-once loops.** A loop's state must mean the same thing at every iteration (`Fixed`). Its meaning leaves
  the runtime stage and round unspecified, and that is what lets the body be generated once.

### 2.6 Proxies

PTX 9.4 §9.7.10.28.2 and §9.7.18.6.5 govern accesses through different proxies. Each share records the proxies that
may access its location next:
- an access by proxy `π` needs `π` in the set, and leaves only `π`;
- the accessing thread's `fence.proxy.async.shared::cta` adds the other proxy;
- a completed TMA load leaves both proxies, since its completion includes an implicit proxy fence;
- a completed MMA leaves only the async proxy.

So `fenceStage`, before a TMA store of staged data, is exactly the update that adds `async`.

## 3. The shared tile (today's encoding)

```raccoon
sealed struct   Smem  (a: Lifetime)(t: DType)(n: Nat) : Type { scope = a }                      // the array's name
sealed inductive Tile (a: Lifetime)(t: DType)(n: Nat)(s: TileState) : Type { kind = lin, scope = a }
sealed inductive SRead (a: Lifetime)(r: Lifetime)(t: DType)(n: Nat) : Type { scope = union(a, r) }

shared    : Ctx(l, g) -> … -> ((a) -> Smem(a, t, n) -> Tile(a, t, n, empty) -> Ctx(l, g) -> Ctx(l, g)) -> Ctx(l, g)
storeMine : Ctx(l, cta(n)) -> Smem -> Tile(…, empty) -> Val -> Pair(Ctx, Tile(…, written))
sync1     : Ctx(l, cta(n)) -> Tile(…, s) -> Pair(Ctx, Tile(…, afterSync(s)))
reads     : Ctx(l, g) -> Tile(…, ready) -> ((r) -> SRead(a, r, …) -> Ctx -> Pair(Ctx, X)) -> Pair(Ctx, Pair(Tile(…, reading), X))
sread     : Ctx(l, g) -> Smem -> SRead(a, r, …) -> Val -> Pair(Ctx, Val)
release   : Tile(…, empty) -> Unit
```

| Token | Means |
|---|---|
| `Tile(…, empty)` | `each t. v[t] ↦1 _` |
| `Tile(…, written)` | `each t. v[t] ↦1 x_t` |
| `Tile(…, ready)`, `Tile(…, reading)` | `each t. each i. v[i] ↦1/n x_i` |
| `SRead(a, r, …)` | while `r` is open, each thread may read any element with the share it holds |

**Why it is safe.**
- A barrier lets each thread trade its pieces for others with the same total (O5). `afterSync` is such a trade:
  - `written → ready`: each thread's own element becomes `1/n` of every element;
  - `reading → empty`: the shares come back to each thread's own element.
- A write needs a whole element; a concurrent read needs a share of it. They cannot combine.
- `release` needs every element whole, which only `empty` and `written` hold.

**What the meaning shows about the states.** `ready` and `reading` hold the same pieces. They differ in what the code
may do next:
- **`reads` needs `ready`.** It lends `SRead` under a scope `r`.
- **`reading` means a read scope has closed.** It has closed in the generator, but at run time other threads may still
  be reading. So the only way on is a barrier, and the shares come back as `empty`.

In pieces, one state with two barrier exits would say the same: shares kept (`ready`) or shares returned (`empty`).
Whether that is cleaner depends on how the exit is chosen. Decision 2 is open again (§9).

**Candidate changes.** A barrier over any number of tiles, rather than one per count (`sync1`, `sync2`).

## 4. The stage ring (`gpu/encoding/Core.rac`'s encoding, with the PTX fixes)

```raccoon
withRing       : Ctx(l, cta(w)) -> RingCfg -> (X: Type)
                 -> ((r) -> Ring(r, cfg) -> Producer(r) -> Consumer(r) -> Ctx -> Pair(Ctx, X))
                 -> Pair(Ctx, X)
takeProducer   : Ctx(m, lane) -> Elected(m) -> Ring(r, cfg) -> Producer(r) -> Pair(Ctx, ProducerAt(r, m))
acquire        : Ctx(n, lane) -> Ring -> ProducerAt(r, m) -> Pair(Ctx, Slot(r, m))
fill           : Ctx(n, lane) -> Ring -> Slot(r, m) -> TMap … -> Pair(Ctx, ProducerAt(r, m))
finishProducer : Ctx(n, lane) -> Ring -> ProducerAt(r, m) -> Ctx                         // the drain
finishConsumer : Ctx(n, lane) -> ConsumerAt(r, m) -> Ctx                                 // no code
await          : Ctx(n, lane) -> Ring -> ConsumerAt(r, m) -> Pair(Ctx, Ready(r, m))          // now with after_thread_sync
mmaFirst/Next  : … Ready(r, m) … -> … ReadyUsed(r, m) …
releaseByMma   : … ReadyUsed(r, m) -> Elected(m) -> … ConsumerAt(r, m)
```

**Pieces.**
- `W(s, j)` is the whole stage `s`, holding its `j`-th fill.
- Barrier `b` holds `●n(b)`, its completed phases, and the piece `R_b(k)` that completion `k`'s arrivals deposit and
  its waiter receives: `R_full[s](k) = W(s, k)`, and `R_empty[s](k) = W(s, _)`.
- Since the PTX fix, `withRing` completes each `empty[s]`'s first phase at initialization, lending the stage as
  `R_empty[s](1)`. No wait relies on a fresh barrier.
- A side's **cursor** is its stage and round. The authority holds per-stage fill and read counters. The producer's
  cursor `(s, r)` agrees when stages before `s` are filled `r + 1` times and the rest `r` times; the consumer's
  likewise with reads.

| Token | Means |
|---|---|
| `Producer(r)`, `Consumer(r)` | the side's cursor at stage 0, round 0 |
| `ProducerAt(r, m)` | the producer's cursor, held in the registers of the thread elected in `m` |
| `Slot(r, m)` | the cursor and `W(ps, _)` |
| `ConsumerAt(r, m)` | the consumer's cursor |
| `Ready(r, m)` | the cursor and `W(cs, k)` |
| `ReadyUsed(r, m)` | the cursor, and a claim that MMAs in flight hold `W(cs, k)` until the next commit |

**Why it is safe.** Each stage's whole piece is in exactly one place: with the producer, with TMA copies in flight, in
`R_full[s]` or with the consumer, with MMAs in flight, or in `R_empty[s]`. Since only one place holds it:
- **P1 and P2:** a TMA write and an MMA read never overlap.
- **The generation equation:** the `j`-th read reads the `j`-th fill.
- **P3:** each side's parity register is its round's parity, and the round-robin agreement keeps every wait within
  one phase of the barrier.
- **P4:** the close comes after both sides are used up (they are linear and belong to `r`), and `finishProducer`, the
  producer's only end, returns only once every `W(s, _)` is back: nothing in flight.
- **P5:** an arrival deposits a share it holds.
- **P8** (PTX §9.7.15.16.5.1): each phase is observed before the next one's arrivals, because the next arrival needs
  the piece the waiter received.

**Candidate changes.** `ReadyUsed` is a claim, not a piece anyone holds. A linear token for the MMAs in flight,
consumed by the commit, would say the same thing as a piece.

## 5. Counting: the accumulator ring

`accEmpty[b]` expects 128 arrivals:
- `R_accFull[b](k)` gives each of the 128 epilogue threads `1/128` of buffer `b`;
- each thread's arrival deposits its `1/128`;
- the 128th arrival completes the phase, and the issuer receives the whole.

`AccFull(q, m, f)` means `each t. buffer[b] ↦1/128`. **R4** (no thread arrives twice in a phase) needs no lemma: an
arrival needs a share, and the next share comes only from the next `accFull` phase, which needs all 128 first.

## 6. Paged attention

The goal kernel. One CTA computes attention for a block of queries of one sequence and head. It runs over that
sequence's logical KV pages:
1. read the physical page `p = table[b][j]` from device memory;
2. TMA-load `K[p]` and `V[p]` into a stage ring;
3. compute `S = QKᵀ` by MMA into tensor memory;
4. softmax, by warpgroups reading `S` and writing `P`;
5. compute `O += PV` by MMA, with a correction role rescaling `O`;
6. mask the last, partial page.

Decode also appends new K and V into the tail of the sequence's last page. Split-KV runs several CTAs per sequence and
merges their partial states afterwards.

| Need | Pieces | Candidate encoding | Status |
|---|---|---|---|
| Read the KV cache from many CTAs at once | a launch-level share of the whole cache, given to every CTA; reads need no per-page ownership | the cache's `TMap` as an unrestricted, launch-scoped read handle | today's encoding mostly suffices |
| Load a page chosen at run time | the TMA box's coordinates are runtime values. Reads stay inside the map by TMA clipping (A9), and the page's validity is a fact about the table | a `Val` for `p`, plus a fact "`p` is a valid page of sequence `b`" | **open question 3** |
| Several waiters on one barrier | `S`, `P` and `O` in tensor memory pass between the MMA warp and warpgroups of 128 threads, so a phase's piece must be split among 128 waiters | the protocol declares `R_b(k)` per waiter, e.g. `each t. 1/128` | **open question 2** |
| Append to the last page's tail | an exclusive piece of the tail, for a page chosen at run time, alongside readers of its prefix | `SlotOwn(l, kv)`-style runtime-indexed token (§7) | spike |
| Split-KV partials | each CTA owns its workspace slot, one writer per slot by index arithmetic, as `TileOwn` | like the persistent GEMM's tile ownership | today's pattern |
| Merge partials | read shares of the partials; logical disjointness of shards is a functional fact, not separation | out of the safety claim | — |

**Spikes, as Raccoon modules that must typecheck** (location to be agreed):
- **Open question 2:** a barrier whose phase piece is split among a waiting warpgroup's 128 threads, and one split
  between two roles (a softmax warpgroup and the correction warpgroup).
- **Open question 3:** a page-table entry read under a scoped read lease of the table. The fact "logical page `j` is
  physical page `p`" is an unrestricted value confined to the lease's scope, so it cannot outlive the lease. That
  settles staleness within a launch without versions. Across launches, the host updates the table, which is the launch
  boundary's business.
- **Append and pool reuse:** §7's encodings.

## 7. DV-P2: no slot reuse until asynchronous readers finish

**Setting.** A pool of `K` shared-memory slots. A kernel checks out a slot chosen at run time, lets asynchronous
operations read it, and returns it for another logical page.

**What is new.** The slot's index is a runtime value. A token for it is indexed by its register's handle,
`SlotOwn(l, kv)` with `kv : Val(l, …)`, and means the piece of the slot whose index the register holds when the code
runs. Exclusivity is then a fact about runtime slot numbers: two `SlotOwn` tokens are valid together only if their
registers hold different slots.

Two candidate encodings for the readers:

| | Counting | Scoped leases |
|---|---|---|
| Lend | `SlotOwn(k) -> SlotLent(k, n) · n × Lease(k)`, where `SlotLent` records `n` shares out | `withReaders(slot, body)` lends an unrestricted `Lease(r, k)` confined to a fresh scope `r` |
| Asynchronous read | consumes a lease into a linear `InFlight(k)`, whose completion gives it back | uses the lease to make a linear `InFlight(r, k)`, which must be awaited inside `r` |
| Reclaim | `SlotLent(k, n) · n × Lease(k) -> SlotOwn(k)` | at `r`'s exit, no lease or in-flight read survives, so `SlotOwn(k)` comes back whole |
| Leans on | linearity and counting | linearity for `InFlight`, scope containment for leases |

The scoped form is today's `reads`/`SRead` pattern (§3) with an asynchronous reader added. The code decides which
reads better.

The required rejections:
- **Premature reuse:** `retire` needs `SlotOwn` whole.
- **Duplicate checkout:** two `SlotOwn` tokens for one slot.
- **Unmatched completion:** an `InFlight` is linear and confined to `r`.
- **A stale page fact:** with a scoped lease, the fact dies with the scope (as for open question 3).

## 8. Open questions

1. **Cursors across a wrap** (resolved): one round per side, with per-stage counters in the authority (§4).
2. **Several waiters per barrier phase:** who declares the split, and is it part of the protocol's type? Spike (§6).
3. **Facts about runtime-chosen contents:** are they unrestricted values confined to a read lease's scope (proposed,
   §6), or versioned? Spike.
4. **Proxies** (resolved by the PTX check, §2.6).

## 9. Decisions for review

1. **The pilot is written in Raccoon**, with meanings and safety on paper. Proving the encoding correct without
   changing it is later research. This replaces "host-neutral first".
2. **The tile's `ready` and `reading`** (§3): keep both, or merge them into one state with two barrier exits? Open:
   it turns on how the exit is chosen.
3. **Barriers hold pieces per phase, declared by each protocol**, and the declaration covers the split among waiters
   (open question 2).
4. **Runtime-indexed tokens through `Val` handles** (§7).
5. **DV-P2's two encodings are both written**, and the code review picks one (§7).
6. **The fresh barrier becomes a real phase.** Done in `gpu/` (44143d9).
7. **`await` emits `after_thread_sync`.** Done in `gpu/` (44143d9).
8. **"Clean" is decided by reviewing working code** for readability and incidental complexity, not by comparison
   with `Gpu.rac` (§0).
