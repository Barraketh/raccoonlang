# TinyGEMM with indexed commands

This is the first actual client port in the comparison with Core. The alternative library builds `Cuda.Kernel`
directly, and the real TinyGEMM client chooses its resource operations through that library. The complete kernel
is definitionally equal to Core's TinyGEMM, including the launcher. The raw indexed-command port requires no
language feature, evaluation change, or typing reflection. The client API adds generic command-block notation;
it leaves the typing rules and eager evaluation unchanged.

This is a first case, not a replacement for the entire Core library. The follow-up
[`full/` experiment](full/RESULTS.md) tests A3b attention and persistent pair GEMM with a general cursor API
over shared lowering. This Tiny interface specializes the allocation graph and actor layout to TinyGEMM. A shorter
client is partly the result of that specialization, so it does not establish a reduction in the whole library's
implementation or proof complexity.

## Client API and Luna's kernel

[`Api.rac`](Api.rac) implements named resource views, helper contracts, real loaded register views, and checked
assembly/rendering. [`API.md`](API.md) describes the library boundary and the remaining generalization work.
After the library checked, a Luna agent independently wrote [`TinyClient.rac`](TinyClient.rac) against it,
including all primitive producer, first/rest issuer and store operations, plus configurable assembly.

The store continuation actually compiles:

```raccoon
chunk.load(fun (values: Values(chunk)): LoadedBody(chunk) =>
  command Gpu.then {
    chunk.staging.acquire
    chunk.staging.write(values)
    chunk.staging.fence
    chunk.output.store
  })
```

The notation expands to ordinary applications of the named sequencing function. Resource properties supply
commands; the loaded view identifies the actual registers allocated by load. `Native.Op.writeStage` now takes
that register base explicitly. A checked target fact with an unknown fresh-name counter proves that the first
shared write uses the supplied data. A mutation that guesses the base from the counter fails that proof.

[`CLIENT_FEEDBACK.md`](CLIENT_FEEDBACK.md) records Luna's authoring experience. It exposed an avoidable exact
closure-scope requirement: iteration builders now read out and retain the callbacks' actual dependency scopes,
so ordinary lambdas work. Remaining costs are explicit lifetime/type headers, continuation-style load binding,
and repetitive root callback adapters. Named views are still facets of Tiny's fixed graph; independent resource
allocation and frame rules are not implemented.

[`ClientBridge.rac`](ClientBridge.rac) checks full kernel/launcher equality against Core and certification of an
unknown public program. The runner compares both clients against all four layouts, rejects the API-specific
invalid clients, and checks byte-identical rendering. [`client-generated.cu`](client-generated.cu) is Luna's
rendered result. This completes an independent authoring test for TinyGEMM, not A3b or pair GEMM.

## Client and target comparison

[`Tiny.rac`](Tiny.rac) ports all three roles. The producer composes `acquire` and `fill`. The issuer composes
`awaitFirst`/`awaitNext`, `mmaFirst`/`mmaNext`, and `release`. The epilogue composes tensor-memory load,
staging-buffer acquisition, write, proxy fence, and TMA store. Callbacks contain no emitter, token tuple, `Fixed`
witness, or proof term. Lifetime binders and type annotations remain ordinary Raccoon syntax; nested `then`
calls would benefit from an imperative notation.

```raccoon
Commands.chunks(r, fun (i: Lifetime)(index: Index(i)): Commands.ChunkBody(l, w, index) =>
  Commands.then(load(r, index),
    Commands.then(acquireStage(r, index),
      Commands.then(writeStage(r, index),
        Commands.then(fenceStage(r, index), store(r, index))))))
```

The chunk coordinate is part of the states. Each body must change `chunk(index)` to `stored(index)`; the loop
changes the whole tile from `storing` to `done`. A different coordinate, second chunk store, second pass over
the tile, or omitted store fails to match those states. There is no separate chunk ownership token: an
ownership fact is available in the proposition alongside protocol ordering.

[`Commands.rac`](Commands.rac) owns sealed scoped references, indices, linear commands and `Program`. A command
contains an eager compiler closure. Composition threads the fresh-symbol counter and matching states. Loop
builders compile unrestricted callbacks once in fresh lifetimes and then emit runtime loops. The states describe
generated code's effects; eagerly evaluating a callback does not execute GPU work.

[`Native.rac`](Native.rac) is an independent backend, with templates ported from Core. Its shell fixes one
128-column accumulator, a handoff barrier, a configurable stage ring and configurable staging buffers. It assigns
the four roles, initializes resources, joins roles, drains outstanding work, invalidates barriers and deallocates
tensor memory. It also emits tensor maps, host requirements and launch geometry. Its only import is `Cuda`.

The alternative depends on `Tiny → Commands → Protocol → Native → Cuda`; rendering also imports `Check`.
There is no transitive Core dependency. Core appears only in comparison fixtures.

[`Bridge.rac`](Bridge.rac) proves:

```text
Eq(Cuda.Kernel,
   Commands.syntax(MachineTiny.kernel),
   Core.kernelSyntax(CoreTiny.kernel))
```

`Baseline.rac` is the real current Core client with its rendering expression removed and namespace renamed.
The runner verifies that correspondence against `gpu/encoding/examples/tinygemm.rac`. It checks complete kernel
equality for four/two, one/one, two/two and six/two ring stages/staging buffers. This includes every instruction,
operand, binding, control node, shared offset and size, map encoding, host requirement, grid and block size.
Launch bounds are checked separately in the rendered output.

## Proof interface and its limits

[`Protocol.rac`](Protocol.rac) defines one `Step` catalogue and a `Flow` proposition indexed by retained command
syntax, actual `Cuda.Block`, actor, input/output states and fresh-name interval. Primitive leaves use the native
emission template; sequence checks intermediate states; peeled loops check the first transition and repeated
invariant; the chunk loop checks ownership of its actual loop coordinate. A caller cannot supply an abstract
step paired with an unrelated emitter.

Every public `Program` has a `KernelFlow` certificate about its actual syntax, including its three role bodies
and allocation/finish shell. [`Proofs.rac`](Proofs.rac) checks this with an unknown program parameter. It is a
protocol and emission certificate, not a theorem of hardware race freedom.

The checked universal theorems include:

| Theorem | Proof |
|---|---|
| A transition to `fenced(i)` came from `written(i)` | One `Step` case |
| Store of `i` requires `fenced(i)` | One `Step` case |
| Releasing a stage requires the MMA-used state | One `Step` case |
| First MMA requires the ready, empty-accumulator state | One `Step` case |
| No primitive operation follows `stored(i)` | Constructor exclusion |
| No certified command, including composition and loops, continues from `stored(i)` | Induction over retained syntax, using the primitive fact |

The last theorem rules out restarting a consumed chunk through a control combinator. Its proof needs more than
local backlinks. Raccoon cannot structurally recurse on erased `Prop` evidence; an attempted recursion on an
AST-indexed data derivation also encountered conservative termination checking. Retaining an ordinary `Plan`
makes the induction check without modifying the checker.

These facts are easier to state than construction-history theorems about Core's opaque `StageFenced` and
`ChunkOwn`: their premises are public propositions with ordinary elimination rules. This is evidence for those
specific proofs, not a claim that every Core invariant becomes trivial.

[`Templates.rac`](Templates.rac) proves concrete target facts separately: fence emits a proxy fence and warp
reconvergence, await emits a wait followed by the tensor-core fence, and release emits a completion commit and
cursor advance. Deleting the native proxy fence invalidates its target proof. State rules alone would not detect
that deletion. Native templates still need justification against instruction semantics; the full Core equality
is an additional correspondence check for these clients and layouts.

## Guarantees against Core

The baseline is [`gpu/OBLIGATIONS.md`](../../gpu/OBLIGATIONS.md). Complete AST equality transfers every property
of the concrete Core TinyGEMM, relative to its existing hardware, launch, renderer and Core correctness
assumptions. It does not prove a universal refinement theorem for all alternative clients.

| Core guarantee | TinyGEMM alternative | Work outside this port |
|---|---|---|
| I1: declarations and scopes | Fresh names, scoped callbacks, existing `Check.scoping` gate | Generic scoped values and registers |
| I2: shared layout | Identical layout formulas and offsets, existing size checks | Independent allocations, framing and quantitative separation proofs |
| I3: named barriers | Fixed role joins, identical ids/counts, existing checks | General layouts and register splits |
| I4: ranges/descriptors | Fixed Tiny shapes, existing instruction/literal checks | Other shapes and runtime address bounds |
| I5: names | Existing name checker | Same documented name-checker limits |
| I6: launcher | Equality of the whole launcher | Attention and pair launch contracts |
| I7: collective convergence | Actor-indexed commands in a fixed role shell | Grain-indexed branches, warpwise groups, leader arms |
| I8: barrier lifetime | Fixed initialization and close shell | Reusable scopes and pair publication/close |
| M1: ordered emission | Linear composition, target derivation and load continuations | General value-producing arithmetic |
| M2: scope confinement | Scoped indices, loaded register views and command dependencies | Mutable registers and general borrowed views |
| M3: groups | Indexed roles assigned physical groups by the shell | General group/grain indices |
| M4: authority | Sealed builder; ownership also in command state indices | Independently defined resource families |
| M5: representative loop state | Fixed before/after indices, repeated invariant | Dependent state families and branches |
| M6: actor affinity | Private cursors in one elected producer/issuer block | Multiple resource/actor scopes |
| M7: quiescent close | Producer drain, final store wait, joined deallocation | Accumulator rings and overlays |
| M8: checked rendering | Sealed program plus `Check.WellFormed` | General builders; raw `Cuda` remains outside either safe interface |
| M9: handoff fence | Fixed wait/fence sequence | Score-buffer/correction handoffs |
| M10: grain | Authenticated loop indices and fixed uniform bounds | Thread/warp values, votes and conditionals |
| M11: FIFO safety, excluding liveness | Same ring templates and drains | Runtime cursor/phase invariant; no deadlock-freedom claim |
| M12: row affinity and ownership | Fixed lane/quadrant mapping, consumed coordinate-indexed chunks | Attention statistics, normalization and LSE |
| M13: thread-written tmem publication | Not exercised | A3b's P and corrected accumulator |
| M14: coverage | Four output chunks, each consuming its coordinate | P's sixteen-chunk publication count |
| M15: endpoints finish before close | Whole-role contracts and mandatory shell finishers | Multiple independently scoped openers |
| M16: overlays after completed reads | Not exercised | A3b's P-over-S and next-S-over-P |
| M17: atomic claims | Not exercised by the chosen three clients | Separate append/claim port for full Core coverage |
| M18: pair lockstep | Not exercised | Persistent pair GEMM |
| M19: pair resources and common layout | Not exercised | Persistent pair GEMM |
| M20: leader-only ownership | Not exercised | Persistent pair GEMM, including peer-completion negatives |
| M21: warpwise collectivity | Not exercised | A3b correction branch |
| M22: alpha-ring affinity | Not exercised | A3b softmax/correction handoff |
| M23: callback execution/captures | Unrestricted loop callbacks, fixed actor narrowing | General branches, leader arms and outer-register writes |
| M24: register redistribution | Uniform launch bounds, no redistribution | A3b weighted pool, restore order and final barrier |

The propositions do not supply a GPU interleaving semantics, ring phase invariant, shared-layout separation
theorem or PTX adequacy theorem. `Check.WellFormed` checks the same structural subset as it does for Core.
The actual port has the same target behavior as Core; general semantic safety remains a separate obligation.

## A3b and persistent pair GEMM

The follow-up comparisons use [`attention_a3b.rac`](../../gpu/encoding/examples/attention_a3b.rac) and
[`gemm_pair.rac`](../../gpu/encoding/examples/gemm_pair.rac). The library, Luna-authored clients, guarantee
accounting and results are in [`full/`](full/RESULTS.md). That experiment shares Core's lowering implementation;
it does not generalize this independent Tiny backend or its whole-program certificate.

A3b is the first substantial generalization: scoped arithmetic results and mutable statistics; four input rings
and two independent score buffers; warp-uniform conditional rescaling; and register redistribution. It needs
commands with bound results, resource-indexed product states and frame rules, and group/grain indices. Flattening
all combinations into Tiny's enum would lose modularity. Making an entire softmax role one opaque native operation
would avoid testing the actual client interface and proof decomposition.

Persistent pair GEMM then tests repeated fresh tile ownership, two rotating accumulators, leader-only issuance,
and completion obligations in both peers. Its issuer may retire leader-only endpoints; it must not retire the
peer's producer or store endpoint. Pair openers must stay on the common top-level path. Local predecessor states
need actor and scope facts to express these restrictions.

This layering avoids the Core/resource import cycle for a closed catalogue. Opening it to separate resource
modules remains work: arbitrary new `step + emit` pairs would reintroduce the old soundness gap. A new family needs
checked compositions of instruction contracts or a justified lowering contract.

The replacement criteria remain real client source, full-kernel generation, complete target/launch
comparison, guarantee accounting, invalid clients and proofs about unknown well-typed clients. The follow-up
records which criteria it meets. Successful concrete comparisons alone do not establish lower proof complexity
or a need for a native machine judgement.

## Reproduction

```sh
python3 experiments/machine-core/run.py
gpu/toolkit/cuda.sh nvcc -gencode arch=compute_100a,code=sm_100a -O2 -c -Xptxas -v \
  experiments/machine-core/generated.cu -o /tmp/machine-tiny.o
```

The runner checks 46 modules/fixtures (15 accepted, 31 rejected), the real-client fixture, whole-kernel equalities
for both clients, omitted-fence and ignored-data mutations, rendering and host C++ syntax. The retained
[`generated.cu`](generated.cu) and [`client-generated.cu`](client-generated.cu) are byte-identical. Their sm_100a
compilation uses 55 registers and three barriers, with zero stack frame or spills. No hardware execution or
numerical accuracy test was performed. `sbt validate` includes six command-notation tests in addition to the
existing 930 tests.
