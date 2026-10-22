# Declaration-time occurrence and positivity checks

Status: implemented by Luna at max effort, 2026-10-03. Functional validation
passes. Depth scaling stays flat, but the timing comparison misses the baseline
acceptance criterion; see the measured results below. GPU proof checking reaches
the known separate compact-Nat barrier.

This replaces two designs:

- `POSITIVITY_SUMMARIES.md`, the per-value summaries implemented in `bfa2bc3`
  (`ValueAnalysis.scala`). The document has been removed; it remains in git
  history up to `d727085`.
- `PI_AND_INDUCTIVE_OCCURRENCES.md`, the proposed Pi/inductive-head ownership
  redesign. It was never implemented or committed.

Do not use either document as a requirement for this work.

## Terms

- **Block**: the inductive families declared together in one
  `Decl.InductiveBlock`, and checked by `InductiveChecks.evalInductiveBlock`.
- **Target**: what an occurrence question asks about. It is either the whole
  block (all of its family names), or one local variable `VarId`, used when
  inferring which parameters are positive.
- **Absent(t, v)**: target `t` cannot occur anywhere in value `v`.
- **Positive(t, v)**: every occurrence of `t` in `v` is strictly positive.
- **Uniform(v)**: every application of a block family inside `v` uses the
  block's common parameters, and its indices do not mention the block.
- **Freshness**: `validateBlockLayout` rejects any block name that is already
  defined. So no value that existed before the block was opened can refer to the
  block: no builtin, native function, global definition or earlier family. A
  reference to the block can start only at the provisional heads placed in
  `provisionalEnv`. It can reach a value only through what that value is built
  from: arguments, Pi domains and codomains, constructor fields, closure
  captures and environments, and the code of closures created while the block is
  being checked.
- **Scan**: one memoized run of a relation for one target, described below.

## Why this change

Two defects led here.

1. **Exponential walk.** The walker before `bfa2bc3` remembered only the values
   it was currently inside, not the ones it had finished. A chain of neutral
   closures, each reaching its predecessor through both its captures and its
   environment, cost `2^depth - 1` scans over only `depth` distinct closures. See
   `experiments/library-correctness/RING_DESIGN_FRICTION.md`. The cause was a
   missing memo. The per-value summaries fixed the cost, but added about 440
   lines and two lazy fields on every `Value`.
2. **Native false positive.** Both the old walker and the summaries treat a
   native lambda's host code as possibly naming every family. Compact Nat
   arithmetic now leaves `Nat.add(top, bytes)` as a native application, so the
   result index of `Regions.Layout.reserve` is rejected
   (`probes/NativeNatOccurrence.rac`). The same rule disables structure eta for
   `Fin`, whose evidence field mentions `Nat.lt(i, n)` (three
   `EvidenceFieldTests` failures). Freshness says host code cannot name the
   block. Only a native's type, captures and environment can.

The fix is the standard kernel approach (Lean and Coq do the same): check each
constructor directly, once, when the block is declared. Use one rule set,
memoize by object identity for the duration of a scan, and keep no state on
values.

## Design

### Relations and their rules

All three relations live in `InductiveChecks`. `direct(t, v)` means `v` is
exactly the target: for a block target, `VConst(name, Inductive(_), _)` with
`name` in the block; for a local target, `Var(_, id, _)`.

**Absent(t, v)**

- Local target: if `!v.synDeps.contains(id)`, return true. The `synDeps`
  invariant (`Value.scala` header) makes this one-way shortcut sound. When the
  id is present, fall through to the structural rules, which can still prove
  absence (for example, an unused variable captured in a Pi's environment).
- `direct(t, v)`: false.

| Form | Rule |
|---|---|
| `NeutralThunk` | Closure rule: `tpe`, every capture, every local value in `env`, and, for a block target, `CoreAst.mentionsGlobal(term, names)` must be false. For a local target, use `!synDeps.contains(id)`. |
| `InductiveFamilyValue(instance)` | False if the head is direct; otherwise all `args`. |
| `VApp` | `head`, all `args` (the forcing accessor, evidence included), and `tpe`. |
| `VPi` | Freshen once: every fresh binder's type, then the codomain. |
| `VProof`, `VPacked` | `tpe`. |
| `VNatPrefix` | `base` and `tpe`. |
| `VLam`, block target | `Core`: `tpe`, captures, `env` local values, and code names. **`Native`: `tpe`, captures and `env` local values only. No code names: by freshness, host code cannot name the block.** `ProofEta`: `tpe` and captures. |
| `VLam`, local target | `!synDeps.contains(id)`. |
| `ConstructorHead`, `Level`, `Kind`, `ParameterTpe`, `SortParameter`, `Large`, `VSort`, `Var`, other `VConst` | Block target: true. Local target: `!synDeps.contains(id)`. |
| `DeferredEvidence` | `deferred.escaped`, unchanged. |

**Positive(t, v)**

- First, if `Absent(t, v)`, return true. Strict positivity forbids only targets
  that occur, so an absent target is trivially positive.
- `direct(t, v)`: true.

| Form | Rule |
|---|---|
| `NeutralThunk` | False. A stuck computation that mentions the target cannot certify positive placement. |
| `InductiveFamilyValue(instance)` | True if the head is direct. Otherwise, for each argument: at a positive parameter position, `Positive`; elsewhere, `Absent`. Positive positions come from the scan's override if its block key matches, otherwise from `instance.meta.block.isPositiveCoreArgument`. |
| `VApp` | (`direct(head)` or `Absent(head)`) and all `args` `Absent` and `Positive(tpe)`. |
| `VPi` | Every fresh binder type `Absent`, and `Positive(codomain)`. |
| `VProof`, `VPacked` | `Absent(tpe)`. |
| `VNatPrefix` | `Absent(base)` and `Positive(tpe)`. |
| `VLam` | `Native`: false (its occurrences are its positivity). `Core` and `ProofEta`: apply to fresh rigid arguments with `Interpreter.evalApply`; every binder type `Absent` and the result `Positive`. |
| Leaf forms (as listed under Absent) | True. |
| `DeferredEvidence` | `deferred.escaped`. |

**Uniform(v)** (block target only; the expected parameters belong to one constructor)

- First, if `Absent(block, v)`, return true. A value that does not mention the
  block contains no block application.

| Form | Rule |
|---|---|
| `NeutralThunk` | False. |
| `InductiveFamilyValue(instance)` | Block family: at least as many args as expected parameters, the leading ones `defEq` to the expected parameters, and the remaining ones `Absent`. Other family: all args `Uniform`. |
| `VApp` | `Absent(head)`, all args `Uniform`, `Uniform(tpe)`. |
| `VPi` | Fresh binder types `Uniform`, codomain `Uniform`. |
| `VProof`, `VPacked` | `Uniform(tpe)`. |
| `VNatPrefix` | `Uniform(base)` and `Uniform(tpe)`. |
| `VLam` | `Native`: false. `Core`/`ProofEta`: on fresh rigid arguments, binder types and result `Uniform`. |
| Bare block head `VConst` | False. |
| Other leaf forms | True. |
| `DeferredEvidence` | `deferred.escaped`. |

These are the rules of the walker before `bfa2bc3` (`git show
bfa2bc3^:src/main/scala/com/raccoonlang/InductiveChecks.scala`), with four
changes:

1. **Natives** use the freshness rule (no code names).
2. **`VNatPrefix`** cases are added, matching the uncommitted uniformity case in
   the working tree.
3. **The Absent shortcut** at the top of Positive and Uniform.
4. **The `synDeps` shortcut** for local targets.

Changes 1 and 3 together mean a native function, or a stuck computation that
does not mention the block, is accepted inside a recursive field. Before, the
first was rejected by positivity and the second by uniformity. Both are sound
by freshness. This widening is intended; do not flag it as a regression.

### Scans: memo and cycles

A scan is an ordinary object passed as a parameter. Do not use `ThreadLocal`s
or globals. It holds:

- one `java.util.IdentityHashMap[Value, java.lang.Boolean]` of completed
  answers per relation it serves;
- one identity "active" set per relation, for cycles.

Every relation call does: memo lookup → if the value is active, return the
conservative answer (Absent false, Positive false, Uniform false) → mark it
active → compute → unmark (in `finally`) → store the answer. Storing a
conservative answer that a cycle cut produced is sound. Never derive absence or
positivity from a cut.

A memo is valid only while its answers depend on nothing but the value:

- **Block scan** (Absent and Positive for the block target, no override): create
  one per `evalInductiveBlock`, and share it across every family, constructor,
  field and result-index check. It replaces
  `ValueAnalysis.defaultResolutionContext`.
- **Uniform scan**: one per constructor, since the expected parameters are that
  constructor's own parameter variables. Its Absent queries use the block scan.
- **Local scans**: create inside `PositiveParamContext.accepts`, for each
  `(context, sourceIndex)` and fixed-point pass, carrying that pass's
  `PositiveParamOverride(blockKey, current)`. Each context has its own parameter
  `VarId`s, so these memos cannot be shared anyway.

Each Pi or lambda is then freshened at most once per relation per scan. Do not
add a separate cache of telescopes unless measurements show a need.

### Call sites in `checkFamilyConstructors` and `computePositiveParams`

- **Result indices**: `Absent(block, arg)` for every index argument of the
  constructor result, as now.
- **`hasRecursiveField`**: set it only when
  `syntacticallyRecursive(sourceFieldIndex) && !Absent(block, field.tpe)`. This
  is the same syntax test that already decides whether positivity is checked,
  so both decisions in the loop agree. It is exactly as sound as the existing
  positivity gate: by freshness, a field type's value can mention the block
  only if its syntax does, or it depends on an earlier recursive field.
- **Recursive fields**: unchanged structure,
  `syntacticallyRecursive && (Positive(block, tpe) && Uniform(tpe))`.
- **Positive parameters**: restore the old fixed point. Each pass builds
  `PositiveParamOverride(blockKey, current)`, and `accepts` checks `Absent` on
  the forbidden values and `Positive` on the positive values, using local scans.
  Keep the existing semantics: an override applies only to its own block key,
  and the provisional descriptor's all-positive assumption is used outside an
  override.
- Keep `CoreAst.Term.globalNames` (cached per syntax node) and `mentionsGlobal`
  as they are.

### Removals

- Delete `src/main/scala/com/raccoonlang/ValueAnalysis.scala`.
- In `Value.scala`, remove `occurrenceSummary0`, `positivitySummary0`,
  `occurrences`, `positivity`, `VPi.analysisTelescope0`/`analysisTelescope`
  and `VLam.analysisResult0`/`analysisResult`.
- In `InductiveChecks.scala`, remove `activeUniformityLambdas`, the
  `ValueAnalysis.ResolutionContext` parameters, and the summary-based
  `doesNotOccur`/`occursPositively`.
- Delete `src/test/scala/com/raccoonlang/ValueAnalysisTests.scala`. It tests
  the removed API. Carry its soundness intent over as declaration tests (below).

After this change, nothing in `src/` should mention `ValueAnalysis`,
`.occurrences`, `.positivity`, `analysisTelescope`, `analysisResult`,
`RigidTelescope` or `ResolutionContext`.

## Implementation steps

1. Read the old walker at `bfa2bc3^` and the current `InductiveChecks.scala`.
   The only uncommitted change to that file is the `VNatPrefix` uniformity
   case; keep it. Other files touched here (`Value.scala`, tests) also carry
   uncommitted compact-Nat work. Edit around it and do not revert it.
2. Implement the three relations and scans as above in `InductiveChecks`.
   `Value` is sealed and the build uses `-Xfatal-warnings`, so a missed form
   fails to compile. Add a case; never add a wildcard.
3. Rewire the call sites and remove the summary code (Removals).
4. Add a one-line note on `LamBody.Native` (`Value.scala`) stating the
   invariant the freshness rule relies on: host code obtains values only
   through its arguments, its `env`, and values that existed before it was
   built. All six construction sites satisfy it today: `Builtins`,
   `NativeBufferBuiltins`, `Packed` (twice), `TerminationChecker` and
   `ValueOps.materialize`.
5. In `docs/kernel.md`, under the positivity bullets in the inductive-checking
   section, state the occurrence rule in two or three sentences: references to
   the block start only at its heads, natives and earlier globals contribute
   none, and the checks run once at declaration with identity memoization.
6. Tests and validation (below). Then update
   `experiments/library-correctness/RING_STORAGE_FRICTION.md` with the results.

## Tests

Keep every existing `InductiveCheckTest` and `EvidenceFieldTests` case
unchanged. If an existing test expects rejection only because a native or a
stuck computation that does not mention the block appears in a recursive field,
stop and report it instead of editing it.

Add declaration-level regressions, preferably in `InductiveCheckTest`:

1. **Native result index accepted.** The `NativeNatOccurrence.rac` shape:
   `reserve (top)(bytes)(previous: Layout(top)) : Layout(Nat.add(top, bytes))`.
   Set it up so `Nat.add` really runs as a compact native operation (see
   `NativeLiteralTests` and `Packed`), and assert the index is a native
   application, so the test exercises the native path.
2. **Block reached through a compact prefix base is rejected.** With
   `axiom size (T: Type): Nat`, a result index such as
   `Nat.add(size(Bad(0)), 1000)` (or any form whose evaluated index keeps
   `Bad` inside a prefix base or native argument) gives `NonStrictlyPositive`.
3. **Memo regression.** Depth-40 version of the scaling fixture
   (`target/performance/ring-record-diagnosis-20261003/fixtures/scaling_record_4.rac`
   shows the pattern), with the chain in a **result index**, so the
   syntactic gate does not skip it: `inductive Deep indices (m: N): Prop |
   mk (n: N): Deep(chain40(n))` is accepted. Without the memo this needs about
   2^40 scans, so a regression shows up as a hang. This is why the measurement
   step below is also required.
4. **Deep chain in a non-recursive field** (the `scaling_record` shape at depth
   40) is accepted.
5. **Stuck computation over the family is rejected.** With
   `def Sel (b: Bool)(T: Type): Type := match b returning Type with | Bool.true
   => T | Bool.false => Nat`, a field `x: Sel(b, W(n))` with `b` an earlier
   `Bool` field gives `NonStrictlyPositive`.
6. **Stuck computation not mentioning the family is accepted** in a recursive
   field (intended widening): `mk (f: Truth(pop(n)) -> W(n)) : W(n)`.
7. Port the intent of the deleted `ValueAnalysisTests` that can be written as
   declarations: double-negative domains rejected and positive codomain
   accepted; curried type-level match selecting a negative branch after
   application; provisional mutual parameter removed in a later fixed-point
   pass; whole-block head exemption for sibling members; hidden family name in
   closure code or annotations; materialized and rebuilt dependent Pis. List
   any that cannot be expressed as declarations in the report, with the reason.

## Validation and measurement

Run builds and CLI checks one at a time.

1. `sbt validate` (formatting and the full suite). Expect all tests to pass.
   The three Fin failures in `EvidenceFieldTests` must be gone.
2. `sbt graalvmNativeImageClasspath`, then the three conversion probes from
   `experiments/library-correctness/run.py` (`NativeNatOccurrence.rac`,
   `NatBoundConversion.rac`, `RingStorageBound.rac`). All must check with no
   diagnostics.
3. Check `RingStorage.rac`, `RingStorageProofs.rac` and `RingLibraryProofs.rac`.
   Expected: `RingStorage.rac` checks. The proof files get past
   `Regions.Layout` and stop at the separate barrier below.
4. Performance: rerun
   `target/performance/ring-record-diagnosis-20261003/measure.py`'s cases
   (`full_record`, `matched_conjunction`, `scaling_alias_*` and
   `scaling_record_*` at depths 16/20/22/24/26), three fresh-JVM trials each,
   same command and heap as `positivity-summaries-20261003/manifest.json`.
   Record user+system CPU time as well as wall time. Save to a new directory,
   `target/performance/declaration-positivity-YYYYMMDD/`, with source and class
   fingerprints. Acceptance: `scaling_record` stays flat across depths, like
   `scaling_alias`. Every case should be within noise of
   `positivity-summaries-20261003/summary.json` (for example `scaling_record_26`
   ≈ 0.50 s, `full_record` ≈ 2.9 s, `matched_conjunction` ≈ 2.7 s median wall).
   Report any case that is clearly slower; do not tune.

### Known separate barrier (out of scope)

`gpu/proofs/SharedMemory.rac:58` (`SharedMemory.notPositive`) fails because
`Nat.blt(0, Nat.succ(m))` stays stuck. It fails identically on the build before
this change, as a standalone six-line file. It is a compact-Nat reduction gap,
not an occurrence problem. Record it, and add it as a standalone probe if useful.
Do not work around it in the GPU proofs.

## Evidence from a prototype

A scratch copy with only the native freshness rule applied to the current
`ValueAnalysis` (2026-10-03):

- the three probes check clean;
- `EvidenceFieldTests` and `InductiveCheckTest` pass;
- 1054 of 1056 tests pass, and the two failures are `ValueAnalysisTests` that
  assert the old "native mentions everything" rule;
- `RingStorage.rac` checks, and the proof files reach the `notPositive` barrier
  above.

This confirms the semantic fix. It does not test the walker, the memo or the
measurements, which are this work's obligations.

## Constraints

- Do not commit. The touched files share the working tree with uncommitted
  compact-Nat work that is not part of this change.
- Do not change GPU library predicates or proofs, the positivity discipline
  beyond the rules above, or unrelated performance behavior.
- If a new compiler or proof barrier appears, keep a small reproducer and
  report it rather than working around it.

## Implementation and validation results, 2026-10-03

`InductiveChecks` now owns declaration-scoped Absent, Positive and Uniform
scans with separate completed identity memos and conservative active-cycle
guards. One block scan covers the declaration; Uniform scans are constructor
specific, and Local scans are recreated for each context/source parameter/pass.
The old `ValueAnalysis` implementation, Value summaries and Pi/lambda inspection
caches are removed. The uncommitted compact-Nat work is preserved.

The focused inductive/evidence/native/tail suites pass 106/106; `sbt validate`
passes formatting and all 1,052 tests. Classpath generation passes. Existing
inductive and evidence test assertions were unchanged. New declaration tests
cover native result indices, recursive occurrences through compact-prefix bases,
both depth-40 graphs, both stuck-computation cases, double-negative domains,
positive codomains, curried selection and annotation-hidden family names.

The annotation-hidden case uses a typed CoreAst declaration because source type
syntax does not admit lambda terms. Existing mutual intersection and Even/Odd
tests cover fixed-point parameter rejection and whole-block sibling heads.
Rebuilding/materializing a Pi is internal to EqStore/ValueOps and cannot be
invoked or observed by a declaration; existing `ValueOpsTests` remain in place.
The removed API-specific cache identity, cycle and inspection-count assertions
have no declaration-level equivalent. The deep graph tests exercise the new
memoization behavior instead.

The three conversion probes check unchanged (0.798, 0.807 and 2.427 seconds).
`Arithmetic.rac` and `RingStorage.rac` check in 0.860 and 2.348 seconds. All five
storage counterexamples reject locally at `Rejected.bad` with `TypeMismatch`.
`RingStorageProofs.rac` and `RingLibraryProofs.rac` each report the one known
`SharedMemory.notPositive` diagnostic in 3.138 and 3.718 seconds. The standalone
`NatBltSuccessor.rac` fails identically before and after this replacement. GPU
proofs and predicates were not changed; the nine-field aggregate remains a draft.

### Preserved benchmark comparison

All 36 trials complete with no diagnostics. They use fresh sequential JVMs,
the original fixture bytes, command, heap, assertions, classpath paths, roots and
prelude. Wall time and user/system CPU, source/class/library fingerprints and
diagnostics are saved in `target/performance/declaration-positivity-20261003/`.
Fingerprints stayed fixed throughout timing. CPU below is median user + system
time for each trial, in seconds.

| Case | Baseline wall | New wall | Baseline CPU | New CPU |
|---|---:|---:|---:|---:|
| full record | 2.891 | 3.258 | 6.760 | 7.599 |
| matched conjunction | 2.683 | 2.983 | 6.423 | 6.983 |
| alias 16 | 0.416 | 0.809 | 0.846 | 2.066 |
| record 16 | 0.477 | 0.843 | 0.972 | 2.102 |
| alias 20 | 0.468 | 0.810 | 0.946 | 2.042 |
| record 20 | 0.482 | 0.834 | 0.956 | 2.098 |
| alias 22 | 0.438 | 0.821 | 0.900 | 2.079 |
| record 22 | 0.471 | 0.843 | 0.966 | 2.092 |
| alias 24 | 0.465 | 0.825 | 0.956 | 2.081 |
| record 24 | 0.517 | 0.853 | 1.046 | 2.138 |
| alias 26 | 0.473 | 0.832 | 0.959 | 2.095 |
| record 26 | 0.499 | 0.853 | 1.010 | 2.120 |

Depth scaling is flat for both aliases and records, satisfying the graph-growth
criterion. The timing comparison is clearly slower: full record +12.7%, matched
conjunction +11.2%, and the small scaling fixtures +65–95%. CPU rises too, so
the difference is not just a wall-clock delay. Similar alias/record shifts suggest
a shared cost rather than the former exponential record traversal; they do not
locate that cost. The baseline predates the uncommitted compact-Nat work and
storage imports, so this comparison does not isolate the positivity replacement.
The within-noise criterion is not met. No performance tuning was applied.
