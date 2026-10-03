# Luna client authoring feedback

`TinyClient.rac` compiles as a reusable client module with no evaluation body. It uses only `Api`, names all producer, issuer and store operations, and provides `build` plus the default `kernel` for the 4-stage, 2-buffer layout. I did not compare rendered output or kernel equality; those fixtures are intentionally left for the library author.

## Friction encountered

- The callbacks still need explicit type information: each iteration callback binds a fresh `Lifetime`, names the corresponding `Slice` or `Chunk`, and spells out its result contract. This was manageable with the API table and examples, but adds annotation overhead.
- Initially, all three iteration lambdas needed `fun { scope = l } (i: Lifetime)`: ordinary callbacks failed with a closure-scope mismatch (`l` expected, `Lifetime.empty` inferred). The library author updated the iteration builders to retain the callback closure scope in the command dependency scope. I removed those annotations and recompiled successfully; the current client needs only ordinary `fun (i: Lifetime)` lambdas. That initial diagnostic was real friction in the first API revision, but it is no longer a requirement of the current API.
- A `load` result cannot be bound with `let`; the store callback has to be nested as `chunk.load(fun (values: Values(chunk)): LoadedBody(chunk) => ...)`. The continuation is explicit and locally understandable, but it nests the whole write sequence and repeats the chunk-dependent result type.
- The public spellings are generally discoverable from `API.md`, especially property-style zero-operand commands and `command Gpu.then`. The code reads as a sequence of resource actions, and does not expose command authority or evidence plumbing.

## Readability comparison

Against `MachineTiny` in `Tiny.rac`, this client makes each command sequence easier to scan: `command Gpu.then` removes repeated binary `Commands.then` calls, while resource views give useful names such as `slice.ring` and `chunk.staging`. The older client is shorter in its helper signatures and assembly because it directly names indexed `Cmd` types and passes the root `Resource`; the public client pays for its boundary in explicit scoped callback and view/result annotations. The new form is clearer about which resource is acted on, but the required continuation makes the store callback less linear than the old `load; acquire; write; fence; store` chain. Overall, this is a credible improvement in operation-level readability and boundary clarity, with noticeable annotation and nesting costs. Successful compilation alone does not make the API effortless.
