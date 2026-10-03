# A3b attention and persistent pair GEMM experiment

The question is whether a machine API can support the actual GPU clients, retain
Core's guarantees, improve their interface, and make their invariant proofs easier.
These are separate criteria. Generating a correct kernel does not settle the other
three. This tests the features these kernels need; it does not port every Core
feature, such as paged decode/append or SIMT shared tiles.

**The requested proof comparison has not been performed.** Its target is a
kernel-independent theorem: every CUDA kernel produced by a well-typed client of
the library satisfies the obligations, under the documented platform and launch
assumptions. This report records client ports and narrower proofs. It does not
answer whether that universal theorem is easier with Core plus typing reflection,
a primitive state-machine typing judgment, or ordinary dependent typing through
elaboration.

A subsequent [kernel-independent proof experiment](../../library-correctness/README.md)
attempts that comparison for a retirement/coverage fragment. It supplies checked
universal semantic proofs and explicit Core/cursor proof-interface obstructions,
but does not prove the full safety theorem for this API.

The library uses a sealed `Machine(l,g,S)` containing the emitter, resource state
and fixed-state witness, with read-only values returned separately. It supports
product framing, tickets for parked resources, first/rest loops, grain-sensitive
branches, pair allocation, leader work, owned tile/chunk loops, and the existing
checked native primitives. The lowering implementation is shared with Core through
`encoding.Lowering`. It is not an independent verification of those primitives.

Luna authored both clients independently of the library. Every role's operations,
attention arithmetic, resource handoff, allocation graph and cleanup are client
code. The attention port includes its issuer and loader rather than delegating
whole roles to `encoding.Attention`. The pair port explicitly chooses first/next
MMAs, leader work, half-chunk loads, staging writes/fence/store and both CTA drains.

## Safety obligations

| Core obligation | How the new interface retains it |
|---|---|
| I1–I6: target well-formedness, names, literals, scoping, shared memory and checker soundness | Same native AST constructors, sealed values/registers and checked `Core.render`. |
| I7–I8: convergent collectives and barrier lifetimes | Same native group indices, role/branch/loop lowering, scoped protocol openers and quiescent closes. |
| M24: register budgets and shares | Same `Registers` pool/shares, checked role split, restoration and toolkit register validation. The existing `Registers.pool` carve-out still applies. |
| M1–M4: construction authority, groups, committed work and waits | Native sealed tokens remain the cursor state; operations consume them through their original checked lowering functions. The cursor key, constructors and emitter extraction are also sealed. |
| M5–M7: protocol token conservation, ownership scopes, quiescent reuse | Linear cursors/tickets preserve all native state authority; allocation scopes cannot escape, loop/branch states remain fixed, and finishers retain their native waits. |
| M8–M11: rendering, joins/fences, grain and protocol phases | Same renderer, role joins, native grain-indexed values and protocol operations. Unrelated resources may be framed but cannot be discarded. Different role trip counts can still deadlock, as in Core. |
| M12–M16: rows, coverage, finishers and overlays | Native `Row` coverage, `Loaded`/`Probs`/`Final` states and score-buffer sides are unchanged. Clients choose all arithmetic. |
| M17: runtime claims for paged append | Not used by these kernels; paged-append APIs were not ported. |
| M18–M23: pair schedules, owned halves/chunks and leader/peer lifetimes | Same sealed schedule/ownership and pair tokens. Pair allocation requires the root pair lifetime. Leader work admits only consumer/accumulator-producer sides; loop/branch callbacks cannot capture peer obligations. |

The preservation argument depends on the shared lowering and the new cursor
wrappers meeting those contracts. The tests include invalid clients at the public
cursor interface, entire target/launcher equality, and the original GPU suite.
It is not a new formal universal proof of S1–S6 for all cursor programs. Core's
platform assumptions, launch contracts, liveness limits and numerical-correctness
limits remain in force.

## Interface result

Single-resource arithmetic is better localized: a loaded row and its authority
arrive together, and arithmetic preserves its state automatically. Clients do not
supply `Fixed` witnesses, including large product witnesses at loop boundaries.

The multi-resource parts are worse. An MMA touching a score buffer plus two input
rings requires selecting and repacking three leaves while retaining the others.
Pair GEMM's simple epilogue repeatedly spells out focused callbacks and their
state types. Lifetime parameters still distinguish a token's role owner from the
current generated block. The library hides the emitter tuple while introducing
substantial focus/ticket/type annotation code. Both feedback files report this
cost. This cursor API does not meet the desired ergonomic replacement criterion.

## Proof result

The baseline for Core's protocol correctness is its paper arguments, rather than
a Raccoon proof of those arguments. Core's checker soundness proofs cover a
separate structural subset. A partial machine-checked protocol proof is therefore
progress over that baseline; proving every S1–S6 claim is not a prerequisite for
crediting it.

`TargetFacts.rac` proves local facts about actual lowering: publication's store
wait/fence/arrival order, pair commit multicast, branch grain, and A3b's register
budget. Mutation checks make the publication and multicast facts fail when their
native implementation changes. Full-kernel equality ties the concrete client
ports to their original implementations. These are checked results, although the
local lowering facts also apply to Core because the implementation is shared.

The Tiny experiment supplies a restricted universal protocol certificate:
every public program has an AST-linked `KernelFlow` certificate, checked with an
unknown program parameter, and its protocol propositions support checked
predecessor and no-continuation theorems. However, no proof was attempted that
`KernelFlow` implies the library's full obligations. A certificate describing
legal protocol syntax is not itself that correctness theorem.

The A3b/pair cursor API has **not yet carried that certificate layer over**.
Wrapping native token types in a cursor supplies fixed-state evidence, but does
not expose a transition history or a proposition about all emitted paths. This
is an unfinished extension of the restricted protocol interface. More
fundamentally, neither experiment attempted the requested universal correctness
proof. The full-client ports establish functional coverage; their current proof
result is narrower than Tiny's.

The next proof experiment must use the same kernel-independent obligation
statements for all three approaches, and attempt proofs about arbitrary library
clients: primitive preservation, composition/control preservation, and the
library-wide theorem. A3b issuer and pair epilogue framing remain separate
interface problems. Successful ports do not resolve the choice of proof
architecture or establish whether a new typing judgment is needed.

## Validation

Completed checks:

- 35 modules/fixtures: 9 accepted and 26 rejected for the intended rule, at the
  intended client definition. Generic product framing through loops/branches is
  accepted; forged cursors/tickets, resource reuse, protocol order, wrong resource
  identities, escaping values, divergent collectives and leader/peer misuse are
  rejected.
- Eight definitionally equal complete kernel/launcher pairs: A3b's four
  causal/output combinations, and pair layouts `(stages,buffers,band)` of
  `(6,2,8)`, `(1,1,1)`, `(2,2,2)` and `(6,2,4)`.
- Byte-identical default CUDA/launchers, retained in `attention_a3b.cu` and
  `gemm_pair.cu`. Luna also compared all four A3b renderings independently.
- Two lowering mutations rejected by their target facts: deleting publication's
  tensor-memory store wait and changing the pair commit's multicast mask.
- Direct sm_100a compilation/register checks: both attention kernels use 128
  registers per thread and pair GEMM uses 71; all have zero spills. A3b's register
  share changes/restoration also pass the toolkit check.
- The complete original `gpu/check.sh` suite passes, including checker proofs,
  protocol mutations, model checks and generated CUDA compilation. Tiny's existing
  suite passes its 46 fixtures, complete-client equalities and target mutations.
- `sbt validate` passes formatting and all 936 tests.

Hardware execution and numerical comparisons are not part of this run.

To reproduce the client comparisons and public-interface checks:

```sh
python3 experiments/machine-core/full/run.py
python3 gpu/toolkit/registers.py < experiments/machine-core/full/attention_a3b.cu
python3 gpu/toolkit/registers.py < experiments/machine-core/full/gemm_pair.cu
```
