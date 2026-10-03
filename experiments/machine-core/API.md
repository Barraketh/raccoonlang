# Client API and independent authoring experiment

This is an implemented TinyGEMM slice of a larger library design. Import `Api` and
open `Gpu`. The library generates the independent native backend's `Cuda.Kernel`;
it does not import Core. Evaluation stays eager. Runtime loop builders compile
scoped callbacks once and retain the generated loop syntax and its derivation.

## Design

A client names resources and data. A public helper declares an entry/exit contract;
its body composes operations without threading an emitter, authority tuple or proof.
Copyable references identify resources; linear indexed commands carry authority to
perform the next operation. The existing proposition catalogue certifies the actual
emission. Reusing a reference does not permit repeating a consumed transition.

`command Gpu.then { ... }` is generic language notation for right-associated ordinary
function applications. It supports ordinary `let` bindings and local `open` statements.
The named function supplies the composition rule. There is no GPU rule, implicit
synchronization or runtime interpretation in the syntax.

Operations with no operands are properties such as `slice.ring.acquire`; operations
with operands are calls such as `chunk.staging.write(values)`. This follows Raccoon's
existing selection/application rules rather than pretending that zero-argument method
syntax or partial application exists.

## Public contracts

| Callback | Input view | Result contract |
|---|---|---|
| Producer role | `Producer(l, w)` | `ProducerBody(l, w)` |
| Issuer role | `Issuer(l, w)` | `IssueBody(l, w)` |
| Store role | `Store(l, w)` | `StoreBody(l, w)` |
| Producer iteration | `Slice(l, i, w)` | `ProduceStep(l, i, w)` |
| First issue iteration | `Slice(l, i, w)` | `FirstStep(l, i, w)` |
| Later issue iteration | `Slice(l, i, w)` | `NextStep(l, i, w)` |
| Output chunk | `chunk: Chunk(l, i, w)` | `ChunkBody(chunk)` |
| After a chunk load | `values: Values(chunk)` | `LoadedBody(chunk)` |

`Layout` names the allocation configuration type. `layout(stages, buffers)` supplies
its TinyGEMM instance. Helper parameters `{l: Lifetime}{w: Layout}` are read out of
the role view. Local callbacks still explicitly bind their fresh iteration lifetime;
all their resource views already include that lifetime, so no `inScope` is needed.
Iteration builders infer each callback's closure scope and retain it in the resulting
command's dependency scope. Callbacks which capture nothing need no scope annotation;
capturing an outer resource still carries that resource's lifetime.

The available iteration builders are `producer.eachSlice(body)`,
`issuer.peeled(first, rest)` and `store.chunks(body)`. The first two traverse the
positive peeled K-slice domain of the existing TinyGEMM shell. The last consumes
the four actual output chunk coordinates. Their bounds are still fixed by this
shell, not chosen by arbitrary client loops.

The primitive operations are:

- Producer: `slice.ring.acquire`, then `slice.fill`.
- First issuer iteration: `slice.ring.awaitFirst`, `slice.accumulator.overwrite`,
  `slice.ring.release`.
- Later issuer iteration: `slice.ring.awaitNext`, `slice.accumulator.accumulate`,
  `slice.ring.release`.
- Store: `chunk.load(body)`, then the continuation can compose
  `chunk.staging.acquire`, `chunk.staging.write(values)`, `chunk.staging.fence`,
  and `chunk.output.store`.

A loaded value is an actual scoped register view, not a pretend return value or
an implicit scratch-register convention. The load compiler mints the view with
its fresh register base, and write uses that base explicitly. Its allocation and
chunk indices reject data from a different world or coordinate. The view is read
only and may be reused as data; the commands enforce output ownership separately.
It currently supports staging writes, not arbitrary arithmetic or mutable registers.

For example, a store continuation can have this form:

```raccoon
chunk.load(fun (values: Values(chunk)): LoadedBody(chunk) =>
  command Gpu.then {
    chunk.staging.acquire
    chunk.staging.write(values)
    chunk.staging.fence
    chunk.output.store
  })
```

This explicitly typed continuation is the current result-binding interface.
`let values <- load(...)` and inferred lambda headers are not implemented.

## Assembly and proof boundary

`tinyGemm(name, stages, buffers, producer, issuer, store)` accepts the three typed
root callbacks and requires positive stage/buffer counts through ordinary evidence
arguments. `Program`, `syntax`, `certified`, and `render` expose the sealed program,
its full kernel, its `KernelFlow` proposition, and checked CUDA rendering.

The builder name deliberately exposes its specialization: it owns the fixed
128-by-128 bf16 GEMM allocation graph, elected producer/issuer, four store warps,
launch contract, handoff and close shell. These resource views are named facets of
that graph; they are not yet independently allocated resources or a generic frame
rule. The client still chooses every instruction in the role bodies.

For a general replacement, the intended boundary is independent allocation/role
builders plus resource-indexed product states. Helpers declare their touched resources
and state changes; composition frames the others. A3b must exercise result-producing
arithmetic, register mutation, warp-uniform branches, overlays and register budgets.
Pair GEMM must exercise common allocations, leader-only work and peer completion.
No opaque whole-softmax operation or whole-pair kernel will count as those ports.
The follow-up [`full/API.md`](full/API.md) tests these requirements with generic machine cursors over the
shared lowering engine; [`full/RESULTS.md`](full/RESULTS.md) records its interface and proof limitations.

## Authoring test

The API designer implemented and checked the library, then a Luna agent independently
wrote `TinyClient.rac` without modifying it. Luna read the contract and could consult
the real Core client, then supplied producer, first/rest issuer, epilogue and assembly.
Its feedback exposed the exact closure-scope requirement; the designer generalized
the library, and Luna removed the annotations and checked its client again.
`ClientBridge.rac` and the runner check full-kernel and launcher equality against Core
across the four layouts, rendering and invalid clients. `CLIENT_FEEDBACK.md` records
remaining friction rather than treating successful compilation as proof of ergonomics.

The current limitations worth testing are explicit lifetime/lambda headers,
continuation-style result binding, callback wrappers at kernel assembly, and raw
indexed-type errors. Friendly protocol diagnostics and a fully inferred command
surface are design goals, not completed features.
