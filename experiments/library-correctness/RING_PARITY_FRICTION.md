# Ring parity proof friction

This log records diagnostics observed while checking `RingParityProofs.rac` with `run.check`. No elapsed-time or performance measurements were taken.

| Goal / diagnostic | Cause | Spec or API impact | Category and workaround | Severity | Repetition |
|---|---|---|---|---|---|
| The parser reported `Failed to parse LayoutSymTight())` at the existential trace result type. | The inline predicate passed to `Exists` was not accepted in that type position. | No change to the trace or execution semantics. | Parser/language. Named the proposition-valued function `TraceResult` and passed that function to `Exists`. | Low; representation syntax only. | One report; no recurrence after the named predicate. |
| `Exists.intro` reported “expected 3 params (p, witness, proof), got 2”. | This core constructor requires its proposition predicate explicitly at application sites. | No API change. | API/elaboration. Passed `TraceResult(...)` before the witness and proof. | Low; direct constructor-arity correction. | One report; no recurrence after correction. |

The induction over `Concurrent.Execution`, endpoint-round matching, and issue/release bit flips required no further compiler-driven changes. The backend proof's `Typed` induction and exact fresh-ID threading also checked without a language workaround once structural recursion was measured on syntax. No language change is suggested by these proof runs. The final `run.check` returned exit code 0 and an empty diagnostics array. No `sbt` command was run.

## Module ownership / interface correction

Root moved the authoritative `BitTrace` and `TraceResult` propositions into `RingParity.rac`, where `RingLibrary.PhaseSafe` also consumes them. `RingParityProofs.rac` now uses `RingParity.BitTrace` and `RingParity.TraceResult` throughout and contains no duplicate definitions or conversion theorem. This was a module ownership/interface correction with no semantic difficulty and no compiler diagnostic.
