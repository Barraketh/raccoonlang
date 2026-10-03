# Ring proof friction

This log records compiler checks and design corrections that affected the ring proofs. Compiler results below come from `run.check` on the named `.rac` file; `sbt` was not run.

## Setup audit

The setup goal is `run(setup, dead) = ran(world(bytes, Concurrent.initial))` plus an independent `Audit` for all seven primitive steps, for arbitrary `bytes` (`RingProofs.rac:27-66`). Four unsuccessful compiler checks preceded the first success: a closing-parenthesis parse error; `Audit.advance` receiving 14 parameters instead of 8; intermediate worlds using `Mbarrier.waiting` before publication even though that constructor already sets `fenced` and `visible`; and a mismatch against the exact `SafeBarrier.init` obligation. Naming each suffix and raw intermediate world fixed these proof-construction errors. The final audit passed without a primitive API or language change.

## Wait reduction and natural-number equalities

The wait cases need to prove both current-epoch blocking and immediately-previous-epoch observation. A direct reflexivity proof after establishing the relevant `Nat.beq` facts did not reduce the nested `Mbarrier.wait` match in the result type. The proof now mirrors the two boolean branches in transparent helpers `waitByTest` and `waitAfterCurrent`, then transports through the test equalities with `Eq.substP` (`RingProofs.rac:68-100`). This is proof-level rewriting; no changed wait semantics or new typing judgment was needed.

The issue/completion arithmetic is ordinary Nat equality work. For example, `Nat.add(a, b)` recurses on `b`, so `Nat.add(a, Nat.succ(b))` is not definitionally the same term as `Nat.succ(Nat.add(a, b))`. Small lemmas such as `beqAddSuccLeft`, `completeDebtEq`, and existing `Arithmetic.addSuccessor`/`Arithmetic.zeroAdd` expose the equalities needed by the raw barrier proof (`RingProofs.rac:344-440`, `Arithmetic.rac`). These are routine arithmetic obligations, not evidence that the library needs reflected typing.

The positive-byte premise is semantically necessary: `arrive(bytes)` with `bytes = 0` can immediately complete the phase. The universal refinement therefore assumes `Nat.lt(0, bytes)` for every action; setup itself remains independent of `bytes`.

## Arrive safety and release proxy fence

The setup arrival is the only pre-publication arrival. Root strengthened `SafeBarrier.arrive` to require either `Usable(state)` or exact equality with `Mbarrier.initial`, while retaining the live, arrival, and observed facts. The setup audit uses that exact initializer exception (`RingObligations.rac`, `RingProofs.rac:53-57`). This was a specification correction, not a proof-language limitation.

Root review also added `Primitive.proxyFence` before the empty-barrier `arrive(0)` in `RingPrimitives.implementation` for release. The consumer's generic shared reads must be ordered before a later async-proxy TMA overwrite. `Safe(proxyFence, w)` independently requires a usable and quiescent full barrier. `releaseReading` now proves that no-op step and audit first, then the arrival step (`RingPrimitives.rac:80-90`, `RingProofs.rac:189-217`, `RingProofs.rac:608-624`). Three failed checks followed the correction: the old singleton implementation shape no longer matched; an `Or.inl` call supplied a proof where its right-proposition parameter belonged (`ImplicitReconstructionFailed`); and the corrected safe-arrival disjunction had the initializer equality on the wrong side. The final source uses the Usable branch for release and checks clean. These were ordinary proof-shape corrections; the proxy-fence addition is the material protocol-design correction.

## Arbitrary histories and retirement

The generalized dispatcher covers all `Concurrent.Invariant` and `Action` cases, including both ran and blocked outcomes (`RingProofs.rac:689-840`). Three failed checks occurred while adding the structural `Execution` induction: one parse error from inserting it before the remaining dispatcher branches, then constructor arity diagnostics (`History.done` expected `(bytes, state)`, while `History.advance` infers its family `bytes` parameter and expected eight explicit fields). Reordering the definitions and following those constructor signatures fixed the checks. `everyExecution` derives each macro audit from `Invariant` and `Allowed`; `everyKernel` and `everyProgram` apply it to the exact `Scheduler.kernel` / `Ring.execute` result (`RingProofs.rac:842-871`).

`retirementClose` takes an actual `Scheduler.Joint` and proofs that both endpoint queues are empty. It calls `Scheduler.retirement` and returns the derived `AccessSafe` and closed-state invariant together with the close `CorrectMacro` audit (`RingProofs.rac:873-889`). No async-quiescence or empty-slot fact is assumed as an input. The close audit derives the quiescent states needed for join and invalidation from the invariant and empty endpoint queues.

## Combined API theorem

The final public `RingLibrary.Guarantees` predicate assembles eight independent conclusions: exact backend artifact and shell, primitive `History`, race freedom, no inserted collectives in endpoint blocks, logical/native phase parity, well-formedness soundness, setup audit, and conditional shutdown audit. `RingLibraryProofs.everyProgram` composes these directly. `PhaseSafe` now uses `RingParity.TraceResult` from the same `RingParity` module, so the temporary duplicate trace and conversion are gone. The final source quickchecks for both `RingLibraryProofs.rac` and `RingProofs.rac` returned exit code 0 with no diagnostics.

The shutdown wrapper took two lambda-shape fixes. An initial annotated nested lambda failed to parse; the next quickcheck reported a type mismatch at `shutdownSafe`: the expected type printed as `(producerEmpty: Eq(...)) -> (consumerEmpty: Eq(...)) -> Conclusion`, while the actual type printed as `(producerEmpty: Eq(...)) -> ((consumerEmpty: Eq(...)) -> Conclusion)`. These are mathematically equivalent Pi shapes, but the checker did not identify them under the return alias on the outer lambda. Replacing the nested lambdas with one curried multi-binder lambda and a single explicit terminal return type made the wrapper check. This is a function-grouping friction point rather than a safety-specification mismatch; no obligation or premise was weakened. Root subsequently verified that the existing `ValueEquivalenceTests` deliberately distinguishes telescope grouping, so the behavior is an intentional current equality rule, not an established compiler defect.

Root separately reported that an initial `RingLibrary.Guarantees` struct timed out twice, at 120 seconds and 25 seconds. Replacing it with a named conjunction predicate checked in 2.2 seconds. Sampled compiler stacks localized repeated work to `CoreAst.mentionsGlobal` and the `InductiveChecks.thunkMayContain` / `scanClosure` positivity path; the exact algorithmic cause remains undiagnosed. The struct remains a performance reproducer. No `sbt` command was run for this proof work.

## Parent-reported lowering issue

An initial native lowering reused fixed local IDs `read = 2` and `loop = 3` and failed with `v3 declared twice` / `v2 declared twice` for composed code. Threading fresh IDs through composition, branches, and loop bodies fixed the AST-name collision. This was detected by existing well-formedness checks; it does not suggest a new reflected typing feature.

Other instances own the backend and parity proof files and their respective friction logs.
