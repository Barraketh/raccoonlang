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

## Positivity performance diagnosis after rebase (October 3)

These measurements use `7c27c01`, based on `codex/native-buffer-program` at
`eed468e`. No compiler source or on-disk compiled compiler class changed during the
investigation, and the earlier cache prototype remains held aside. Each timing
starts a fresh Oracle GraalVM 21.0.12 JVM with `-Xmx2g -ea`; environment assertions
remain enabled and the CLI uses its default 256 MiB checking-thread stack.
Formal timing runs are sequential, without concurrent builds, tests or profiles.

The original record has five obligations; the current library conjunction has
eight. The timing control therefore uses a matched five-obligation conjunction,
with the existing `RingLibrary.CheckSound(p)` definition expressing its terminal
implication. Both are checked with the same imports and abstract parameters.

| Case | Whole-CLI wall time | Runs |
|---|---:|---:|
| Import library only | 2.620 s | 1 |
| Empty record with the same parameters | 2.467 s | 1 |
| Matched five-obligation conjunction | 2.552 s median (2.666, 2.552, 2.521) | 3 |
| Full five-field record | All exceed 60 s | 3 |
| Single-field records: backend, primitives, memory or participation | 2.546–2.615 s | 1 each |
| Single-field record: checker-soundness implication | Exceeds 20 s | 1 |

The record slowdown is at least 23.5 times the conjunction's whole-CLI median;
the slow runs are censored, so their actual completion times are unknown. Median
peak RSS is approximately 850 MB for the record and 845 MB for the conjunction.
The expensive field is `Check.WellFormed(Ring.kernel(p)) ->
Spec.WellFormed(Ring.kernel(p))`, before any proof of it is constructed.

A separate JFR recording without the observation agent isolates positivity checking: after
excluding its first 5.5 seconds, 1394 of 1397 checker execution samples include
`InductiveChecks` (99.8%). `CoreAst.mentionsGlobal` appears in 741 samples (53.0%);
these inclusive regions overlap. GC pauses sum to 0.356 seconds in the 24.807-second
window (1.4%). Weighted allocation samples estimate about 95.6 GB of allocation
in that window, largely iterators, arrays and vectors. This is allocation churn
from repeated work, despite a stable peak live process footprint.

Observation-only bytecode counters in a separate run report 13,450,602 closure
scans over 165 distinct closure objects across 34 root scans. Of those calls,
13,450,257 revisit a value after a completed scan in the same root. No active
cycles occur, and every completed scan reports absence of the target.
The still-running final root has only 35 distinct closure objects. Its most
frequently visited lambda is scanned 6,718,372 times. Global-name syntax scanning
is called 334,152,342 times over only 1005 distinct syntax nodes. Counter-run
elapsed times are not used for performance comparisons.

The cause is now reproduced without GPU imports. The minimal fixture defines
`pop` as a match on an abstract natural-number value, builds a chain of nested
`pop` calls, and puts `Truth(chain(n)) -> Truth(n)` in a record field. Eager
evaluation produces a linear chain of neutral closures. In each closure, the
identity-capture vector and captured environment contain the same predecessor.
`thunkMayContain` traverses both. `scanClosure` remembers only active visits and
removes them on return, so the second edge traverses the predecessor again.
The resulting scan count is `2^depth - 1`: depths 8, 12 and 16 produce exactly
255, 4095 and 65,535 scans over 8, 12 and 16 distinct closures respectively, with
zero active-cycle visits. This establishes exponential revisiting of a shared
value graph rather than merely localizing a hot method.

| Closure depth | Implication alias, median s | Record, median s |
|---|---:|---:|
| 16 | 0.433 | 0.606 |
| 20 | 0.444 | 0.877 |
| 22 | 0.431 | 1.271 |
| 24 | 0.442 | 2.923 |
| 26 | 0.443 | 10.055 |

Each entry uses three fresh-JVM measurements, with depth order and alias/record
order alternating. All these synthetic checks complete successfully. The
initial exploratory scaling runs overlapped profile export and are excluded
from this table.

The recommended first fix, not applied here, is to retain completed negative
occurrence answers by closure identity for the same target within one query.
Keep the existing conservative active-cycle handling and discard the completed
table when the query finishes. This should remove repeated paths through shared
closures while preserving the current occurrence judgment. Its soundness needs
checks covering hidden captured occurrences, native closures, cycles, mutual
families and changed targets; its benefit must be measured on this base. No
speedup for that proposed change is established by the present measurements.
This issue can be addressed in the existing checker while retaining eager
evaluation; it supplies no reason to change the library's typing discipline.

Raw [baseline results](../../target/performance/ring-record-diagnosis-20261003/baseline-results.json),
[synthetic results](../../target/performance/ring-record-diagnosis-20261003/scaling-repeated-results.json),
[summary](../../target/performance/ring-record-diagnosis-20261003/summary.json) and
[provenance](../../target/performance/ring-record-diagnosis-20261003/manifest.json)
are retained locally under ignored `target/performance`. That directory also
contains the fixtures, measurement driver, JFR recording, compact profile
summary, stack sample and observation-only agent source. The initial invalid
conjunction fixture is preserved separately and excluded from all results.
