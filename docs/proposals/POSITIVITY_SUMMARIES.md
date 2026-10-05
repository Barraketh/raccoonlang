# Intrinsic occurrence and strict-positivity summaries

## Decision and scope

Every value has kernel-owned, memoized occurrence and strict-positivity metadata.
In particular, every Pi has this metadata without an annotation from its caller.
The inductive checker consumes it instead of repeatedly traversing closures and
freshening the same telescope for each target. Evaluation remains eager; computing
analysis metadata is lazy, so creating a value does not execute additional code.

This implements the proposed “what is this value negative in?” interface. It is
not a cache of answers to individual positivity queries. The summaries are
independent of the queried family or variable, and shared children contribute
their already computed summaries. There is one implementation of each occurrence
and positivity rule. Remove the old absence/positivity walkers when switching the
checker to these summaries. Uniform parameters and nonrecursive indices remain
separate requirements.

The initial implementation preserves the existing checker judgments. This is a
compiler representation change, not new source syntax, variance declarations,
typing reflection, or a different positivity discipline. Do not apply the earlier
query-cache stash or make unrelated performance changes.

## Interface and ownership

Provide package-private accessors on `Value` for:

* `occurrences`: a conservative set of possible target occurrences;
* `positivity`: a compositional description of targets forbidden by strict
  positivity, normally reduced to a set;
* Pi inspection: its domains and codomain under one fresh rigid telescope,
  shared by the two analyses;
* lambda inspection, when needed: domains and result on rigid arguments.

Names and exact Scala layout are implementation choices. The accessors must be
available by default on every value and owned by the kernel, not supplied as
trusted assertions by arbitrary constructors. Their results belong to an
immutable value instance. Copying/rebuilding a value gives it fresh analysis
state; never copy a summary by `ValueId`, syntax identity, or conversion key.
Use object identity for reentry guards and analysis DAG memos: Scala value
equality is not an appropriate key, and Pi equality deliberately throws.

Keep occurrence construction separate from positivity construction. Asking
whether a closure contains a family must not apply that closure merely to
compute its positivity. Likewise, metadata must not force a Pi classifier or
walk an unbounded tower of sort classifiers.

## Targets and sets

The checker has two query kinds:

* the entire canonical member set of an `InductiveBlockKey`;
* one free `VarId`, for positive-parameter inference.

Global code references retain canonical names; local dependencies retain unique
variable IDs. A bare inductive head contributes its canonical name. Keep these
two namespaces distinct. A global-name set also includes names appearing in
closure code: these need not themselves name families, but only family blocks
are queried. Do not identify families by unqualified display names.

Unknown code is conservative. Represent global sets as finite or cofinite sets
(“all names except these”), since unknown code must remain unknown after a
recursive family's member names are excluded. Local sets similarly need a
conservative universal case for unsupported positivity inspection. Ordinary
local occurrence summaries use `DepSet`; they must not silently lose dependencies
in types. Union and membership need no evaluation. Unknown is never absence.

The block query boundary is essential. The current recursive-family rule skips
its arguments when its head is any member of the queried block. A flat summary
can express this by excluding that family's **whole block** from its argument
failures. This is exact for whole-block queries, not arbitrary sets containing
only some members or a mixture of blocks. Expose whole-block queries and prevent
an arbitrary names-set API from accidentally claiming those semantics.

## Composition rules

Write `O(v)` for occurrence targets and `F(v)` for forbidden targets. The ordinary
arrow rules are:

```
O(A -> B) = O(A) union O(B)
F(A -> B) = O(A) union F(B)
```

Use the same rules for every domain in a dependent telescope and its evaluated
codomain. This is strict positivity, not signed variance: `((T -> N) -> N)` still
forbids `T`. Any occurrence below a function domain is forbidden.

Fresh telescope identities are private witnesses of analysis, not the caller's
variables. Remove newly introduced witness IDs from outward summaries, or retain
them as private IDs that can never be queried from outside that inspection. Do
not replace occurrences of captured variables with binder-position guesses.

Preserve these existing form-specific rules:

| Form | Occurrence summary | Forbidden summary |
|---|---|---|
| Saturated inductive family | Head name and occurrences of all arguments; no extra classifier walk | For each argument, `F(arg)` at certified positive positions, otherwise `O(arg)`; exclude the head family's whole block from global failures |
| Other application | Union of head, **all** arguments and result type | Head occurrences except its direct target (a variable ID or inductive head name), all argument occurrences, and result-type forbidden targets |
| Pi | Occurrences in fresh domain types and evaluated codomain | All domain occurrences and codomain forbidden targets |
| Neutral match thunk | Global occurrences in type, captures, local environment and all code references; local occurrences from its `synDeps` | Its occurrence targets: a stuck computation cannot certify positive placement |
| Core lambda | Global occurrences in type, captures, local environment and all code references; local occurrences from its `synDeps` | Domain occurrences and forbidden targets in its result on fresh rigid arguments |
| Native lambda | Unknown global occurrences; local occurrences from `synDeps` | Unknown for both query kinds, matching current rejection of native lambda inspection |
| Proof eta lambda | Type/capture occurrences, with no hidden code | Analyze its result on rigid arguments, as with the existing inspector |
| Erased proof / packed value | Occurrences in its exact type | All occurrences in its exact type |
| Constructor head | Local occurrences from `synDeps`; no global occurrences | Empty, as in the existing rule |
| Variable and other leaf forms | Local occurrences from `synDeps`; variables also directly occur in their own ID; bare inductive heads directly occur by name | Empty |

The distinctions in this table are intentional. For example, global occurrence
checking does not traverse a bare variable's type, while local checking uses its
dependencies. `VProof` does not expose an erased interior. A constructor-valued
index is still checked through its application's fields and exact type.

`DeferredEvidence` is not an inspectable value. Preserve its escaped-container
error. Building analysis state must not force it at value construction. When an
actual occurrence/positivity analysis reads an application's arguments, use the
same forcing boundary as the existing checker (`args`, including evidence).
Do not substitute `determiningArgs` for all arguments in these rules.

Cache the set of global names mentioned by each immutable Core term, composed
from child sets. Make `mentionsGlobal` a membership/intersection query against
that same authoritative set, so shared closure code is not rescanned for each
value or target. Retain current inclusion of annotations, motives and branches.

## Dependent substitution and evaluation

Do not perform symbolic substitution of occurrence sets through arbitrary
dependent computations. A Pi inspection evaluates its checked codomain on rigid
arguments once, as the existing checker does. An actual application evaluates
normally and exposes the resulting value's own summaries. Substitution,
materialization and partial application already rebuild affected values: their
new instances must compute new summaries in the new environment.

For example, applying a type-level match to a constructor may select a branch
containing a negative arrow even though applying it to a rigid variable produces
a neutral thunk. The selected value must receive the selected arrow's summary;
the unresolved thunk stays conservative. Reusing the original Pi's summary as
the application's summary would be unsound. No new native codomain capabilities
are assumed merely because a host function has been evaluated once.

## Mutual families and conditional metadata

Checked family parameter positions are immutable and can be composed immediately.
Provisional block positions cannot be frozen to their initial all-positive guess.
Retain a small immutable forbidden-set expression for provisional positions:

```
argument(block, i, arg) =
  if positive(block, i) then F(arg) else O(arg)
```

Expressions need only constants, union, exclusion of global block members, and
these conditional argument choices. Child expressions are shared as a DAG; do
not flatten them by recursively copying every path. Track which provisional
block assumptions an expression depends on. Expressions without such assumptions
reduce once to ordinary sets. In particular, occurrence summaries never depend
on the positive-parameter fixed point.

Each iteration of `computePositiveParams` uses one resolution context containing
the block key, current positive positions, and an identity memo from expression
nodes to resolved sets. Resolve the same node once in that context, then answer
all parameter queries by membership. An override applies to that block key only;
previously checked blocks use their certified positions. Outside an override,
provisional expressions use the descriptor's current provisional assumptions,
preserving the recursive-constructor checking order. Published heads carry the
final checked schema, not a resolved provisional summary. Context memos have
bounded pass lifetimes; do not add an unbounded global cache of environments,
targets, overrides or values.

This means the common query is a set lookup; mutual inference first resolves
conditional metadata once per fixed-point pass. It does not reevaluate domain
types, closures, code or codomains on every pass.

## Reentry and correctness boundary

Guard metadata construction by object identity **before** entering a memoized
initializer. A recursive hit returns a conservative unknown contribution;
completed children reuse their permanent metadata. Clean up active state in
`finally`, including after an exception. Avoid recursive lazy-initializer
deadlock/overflow and do not turn a cycle into an empty summary. Analysis cycles
are conservative rejection, never an extra way to certify an inductive.

Uniform-family checking continues to inspect values, because equal common
parameters and nonrecursive indices are relational obligations. It consumes the
new occurrence summaries for its absence questions. Its lambda recursion guard
must still cover the entire recursive uniformity check, even if rigid lambda
inspection is shared/memoized. It is not replaced by a negative-target set.

Required invariants for review:

1. A reported absence is justified by the occurrence rule, including hidden
   code/captures and both paths to a shared captured value.
2. A reported positive placement follows the strict rules above, not sign
   cancellation or merely absence from a Pi domain.
3. No provisional variance result survives a change of fixed-point assumptions.
4. Rebuilding after reduction/substitution cannot retain another value's metadata.
5. Classifiers, proof erasure, evidence forcing and value identity retain their
   existing behavior.

## Tests and measurement

Run the full existing suite and add focused regressions for:

* double-negative arrows; positive codomain and negative dependent domains;
* captured local IDs and fresh/alpha-renamed binders;
* constructor-selected dependent branches, partial application and materialization;
* hidden family names in closure code, annotations and environments;
* native and cyclic closures, including repeated queries after guarded failure;
* erased proofs, packed values, constructor-valued indices and evidence forcing;
* mutually recursive positive-parameter inference where an initially allowed
  sibling parameter is later removed, including reuse of the same expression
  under two assumption sets;
* whole-block head exemption and the independent rejection of nonuniform or
  recursively indexed applications;
* a deep shared neutral graph: permanent metadata is reused and construction
  follows the graph rather than exponentially many capture paths;
* one Pi codomain inspection for repeated occurrence/positivity queries, without
  requiring any caller to opt into metadata.

Prefer semantic assertions and construction counters to fragile wall-time test
limits. Do not keep the old implementation as a second permanent test oracle.
Run `sbt validate` and regenerate the runtime classpath before CLI runs.

After tests/builds finish, benchmark the preserved record, matched conjunction,
and synthetic depths 16/20/22/24/26, with three fresh JVM trials each, matching
the baseline command, assertions and heap. Run builds and measurements sequentially.
Preserve the original evidence under
`target/performance/ring-record-diagnosis-20261003/`; save new measurements in a
separate directory. Record source/class fingerprints and completion diagnostics,
not only elapsed times. Update the friction report with actual results and
remaining limitations before declaring this work complete.

## Implemented layout

`ValueAnalysis.scala` owns the target sets, occurrence rules, forbidden-set
expressions and resolution contexts. `Value` exposes `occurrences` and
`positivity` through per-instance lazy fields guarded by object identity.
`VPi.analysisTelescope` and `VLam.analysisResult` retain the rigid inspection
shared by the analyses and the uniform-family checker. `CoreAst.Term.globalNames`
retains the syntax summary used by both closure analysis and `mentionsGlobal`.

`InductiveChecks` now queries this metadata. Its former occurrence and positivity
walkers have been removed; uniform-family checking remains structural. Each
positive-parameter fixed-point pass creates its own resolution context, and
constructor checking shares a default context for that block. None of these
contexts outlives the check that needs it.

Luna implemented this design at max reasoning effort. Root reviewed the rules
against the former checker, corrected the separation of global closure traversal
from local `synDeps`, and strengthened dependent-application, materialization and
hidden-code regressions. The twelve focused tests check metadata reuse and
semantic behavior; the existing inductive, evidence and proof-collapse tests
cover the surrounding checker obligations.

The implementation retains inspected values and immutable target sets for the
lifetime of their owning values. Repeated queries avoid traversal, but initial
construction still costs evaluation and set union; this is not a constant-time
or linear-time claim for all dependent programs. Provisional summaries require
resolution once per assumption context, and unsupported or cyclic inspection
remains conservative. This change does not add reflected typing propositions or
simplify equality transport in proofs.

Measured results and validation are recorded in
[the library friction report](https://github.com/Barraketh/lemur-raccoon/blob/main/experiments/library-correctness/RING_DESIGN_FRICTION.md).
