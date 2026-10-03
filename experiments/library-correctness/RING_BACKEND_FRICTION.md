# Ring backend proof friction

This log records only diagnostics observed while checking `RingBackendProofs.rac` with the library-correctness CLI. No elapsed-time or performance measurements were taken.

| Goal / diagnostic | Cause | Spec or API impact | Category and workaround | Severity | Repetition |
|---|---|---|---|---|---|
| Recursive `planNoCollectives` call was reported as `RingBackendProofs.planNoCollectives not found`. | The proof recursed through the `Plan` proof value without a supported structural measure. | No change to `RingBackend` or endpoint API. | Language/elaboration. The first attempted measure, `structural(plan)`, was rejected because structural recursion on proof values is unsupported. Passing the indexed `Code` value explicitly and decreasing on that syntax made the recursion checkable. | Low; proof-shape friction only. | One initial report; no recurrence after the syntax-indexed definition. |
| `Artifact.mk` reported “expected 6 params (p, producer, consumer, setup, close, layout), got 5”. | The constructor requires the program index explicitly in this call. | No API change. | API/elaboration. Passed `p` as the first constructor argument. | Low; a direct constructor-arity correction. | One report; no recurrence after correction. |
| `Eq.refl(Block)` had actual type `Eq(Type, Block, Block)` where the artifact field required an equality between block values. | `Eq.refl` takes a term; `Block` names the type, rather than the concrete setup value. | No change to setup or close templates. | Language/type elaboration. Used `Eq.refl(Ring.setup)` and `Eq.refl(Ring.close)`, which reduce against their independent specifications. | Low; a direct witness correction. | One report; no recurrence after correction. |

The final check used `run.check` on `RingBackendProofs.rac`; it returned exit code 0 and an empty diagnostics array. No `sbt` command was run.

The structural induction over `Endpoints.Typed` and threading each exact `Ring.compile(...).next` supply caused no compiler friction. The public `Endpoints.syntax` and `Endpoints.typing` accessors exposed enough information for the universal program theorem; no API or language change is suggested by this proof.

## Review-driven specification correction

Root review found that the original `Layout` statement fixed shared-memory and CTA geometry but did not bind the launcher's actual tensor-map list to the 64x64 bf16 load represented by the 8192-byte native issue template. A 64x32 map mutation could therefore have retained the proof. `RingBackend.Layout` now includes an independent `MapContract`, and `RingBackendProofs.layout` supplies `Eq.refl(Ring.launcher.maps)`. This is a specification correction found in review, not a compiler diagnostic or proof failure. One such gap was identified in review; no recurrence count is available or relevant.

Root review also found that ordinary shared reads must be ordered before the next asynchronous TMA overwrite. The concrete consumer release template now emits `fenceProxyAsync` before its empty-barrier arrival, and the independent atomic template includes the same instruction. `Individual` admits that instruction, and `atomicNoCollectives` has one more concrete AST leaf in the release case. The corresponding library obligation remains separate from this template proof. This is a design correction from review, not a proof diagnostic or proof failure. One such correction was communicated during this task.

Root's final review found that `Artifact`'s endpoint plans and setup/close/layout fields did not constrain assembly of the enclosing `Ring.kernel(p)`. `RingBackend` now specifies parameters, launcher, and the complete shell independently, including selected producer/consumer threads and scoped setup/endpoints/close blocks. `everyProgram` supplies `Eq.refl(Ring.kernel(p))` for `Shell(p)`; reduction verifies the actual generic kernel against that independent assembly for unknown `p`. This review-driven specification correction closes the shell boundary and was not a semantic or language difficulty. One such correction was communicated during this task.
