# Design and integration friction

These observations were made by root while designing, integrating and reviewing
Luna's proofs. The separate Luna logs record proof-authoring diagnostics.

The original timing observations below were taken on `soundness_improvements`
at `acaf536`, before integrating the existing interpreter optimizations. On
October 3 the experiment work was rebased onto `codex/native-buffer-program`
at `eed468e`, which includes `codex/frame-composition-experiments` at `321d5b6`.
With the earlier positivity-cache prototype held aside, the preserved record
reproducer still exceeded a fresh 15-second limit on this optimized base. This
is a bounded reproduction, not a measured comparison with the earlier timeouts;
it does not identify the remaining cause or justify a particular optimization.

| Observation | Category | Resolution / implication |
|---|---|---|
| `RingClient` initially failed `Check.WellFormed` with `v3 declared twice` and repeated `v2 declared twice`. | Lowering bug. | Threaded fresh IDs through sequencing, both branch arms and nested loops. The same client then checked and emitted CUDA. No proof-language change. |
| The first arrival predicate allowed any unpublished live barrier, although only the initial setup arrival was intended. | Specification omission. | Strengthened it to require `Usable(s)` or equality to the initializer's exact initial barrier state. Luna's setup and release proofs now distinguish those cases. |
| `Layout` checked the issued byte count and resource extent but did not bind the launcher's actual TMA map box. | Specification omission found in review. | Added `MapContract`: the actual map is the fixed 64x64 bf16 input map. This is checked together with the independent 8192-byte native issue template. Added a box-change mutation. |
| Ordinary generic reads precede a later async-proxy overwrite across the empty handoff. That direction should be explicit in the implementation. | Platform-contract / backend design. | Added a consumer proxy-fence primitive, its quiescence precondition, and the corresponding native instruction before empty arrival. This is an explicit ordering contract, not a theorem about hardware. Added a fence-removal mutation. |
| A combined `Guarantees` record declaration exhausted a 120-second compiler timeout, then another 25-second profiling limit; no diagnostic was emitted. | Compiler performance; sampled stack localized the work to positivity checking. | Replaced the record with a named conjunction of the identical five obligations. That module checked with no diagnostics in 2.2 seconds in the measured run. Preserved the original declaration in `probes/RingGuaranteesRecord.rac`, outside the default test suite. A subsequent six-second stack sample repeatedly visited `CoreAst.mentionsGlobal` and `InductiveChecks.thunkMayContain` / `scanClosure`; this localizes the costly work to positivity checking across closures, but does not establish the precise algorithmic cause. This is meaningful proof ergonomics friction, rather than a demonstrated expressiveness limitation. |
| The backend artifact initially checked the compiled endpoint blocks and setup/close definitions, but did not independently constrain their assembly into the actual kernel. | Specification omission found in review. | Added `Shell(p)` tying the actual kernel to independent thread guards, phase initialization, setup/close order, parameters, launcher and shared extent. Added root-assembly mutations. Endpoint template correctness alone would not detect a bad enclosing lowerer. |
| The first combined theorem omitted setup and retirement conclusions that were proved separately. | Specification integration omission. | Added `SetupSafe` and `ShutdownSafe` to the aggregate. Shutdown depends only on genuinely exhausted actual queues, and derives quiescence and the raw close outcome. |
| Combining shutdown into the public theorem initially failed despite component proofs checking; expanded expected/actual types differed only in arrow grouping. | Proof-language/API friction. | The checker distinguishes a multi-binder Pi from a nested function returning another Pi. One multi-binder lambda with an explicit terminal result annotation checked successfully; semantic obligations are unchanged. The initial complete corpus check was 70/71 with this single wrapper failure. The existing `ValueEquivalenceTests` explicitly tests that Pi definitional equality distinguishes telescope grouping, so this is a friction point in the current language design rather than an unconfirmed equality-checker bug. |
| The initial transaction-debt mutation replaced a boolean test with literal `true`, which the compiler rejected as an unreachable false branch before checking safety. | Test-harness weakness. | Changed the mutant to compare `expected` with itself. It still ignores completion debt but retains well-typed branches, so the runner requires a local proof `TypeMismatch` rather than accepting an unrelated compile rejection. |
| A producer issue with zero expected bytes completes its phase before the async copy starts. | Necessary semantic premise. | The generic protocol theorem requires positive bytes; the concrete API fixes 8192 bytes. The executable test witnesses premature zero-byte completion. |

The four new proof files contain 1341 lines in this version (887 primitive, 118 backend, 280 parity and 56 aggregate), including comments and helper definitions. They also reuse the earlier scheduler and memory proofs. This is a concrete cost baseline, not a measure of irreducible proof complexity: the primitive and parity dispatchers repeat many impossible local-state cases, and explicit equality transport dominates the reduction helpers. A checked theorem is therefore not evidence that the proof was trivial. Simplification/rewrite support and better case handling are plausible improvements; their benefit has not been measured here.

This pass deliberately leaves the language unchanged. The record/conjunction
performance difference and equality-transport work reported by Luna deserve
compiler and proof-tooling attention. They do not yet show that a new typing
judgment would shorten the actual physical-protocol argument. The successful
ordinary proofs must still be evaluated against multi-stage, tensor, output,
register and pair extensions before deciding that question.
