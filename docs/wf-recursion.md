# K2: Sealed Accessibility and Well-Founded Recursion

Status: **K2 kernel implemented; T3 export mapping pending the translator** (2026-07-16). Companion to
`mathlib-export-port.md` (K2/T3),
`kernel-theory.md` (decidability and the axiom ledger), `proof-collapse.md` (proof representation), and
`k6-mutual-nested-inductives.md` (ordinary generated recursors).

## 1. Outcome

Support Lean's `Acc`/`WellFounded` declaration cluster without adding proof-driven definitional recursion.

`Acc` and `WellFounded` remain ordinary checked inductive propositions. Their constructors, proof-recovery recipes,
and non-recursive eliminations use the same kernel paths as other inductives. The exceptional operation is recursive
elimination from an `Acc` proof into data: the public Sort-motive `Acc.rec` is installed as a **sealed symbolic
constant**. Applying it never performs an ι-step, even when its major premise is constructor-headed.

The primitive has a propositional constructor equation. Users and translated definitions may rewrite explicitly with
that equation, but the evaluator and definitional equality never consult it automatically. This is the same separation
as an opaque mathematical function plus a theorem describing it, not a new evaluator rule.

The intended translated cluster is therefore:

```text
Acc / Acc.intro                    ordinary checked inductive declaration
Acc.rec at every motive             sealed K2 primitive
Acc.rec constructor equation        primitive propositional lemma
Acc.casesOn                          direct non-recursive ordinary match
WellFounded / WellFounded.intro     ordinary checked inductive declaration
WellFounded.recursion/fixF/fix      translated wrappers over the sealed primitive
fixF_eq/fix_eq                      synthesized and checked proof applications (§8)
```

There is no runtime representation of an accessibility derivation beyond the existing proof representation. No
fixpoint is tied, no thunk follows an `Acc` child, and no proof becomes a termination metric.

## 2. Why K2 exists

Lean's generated `Acc.rec` recursively eliminates an accessibility proof:

```lean
@Acc.rec :
  {α : Sort u} →
  {r : α → α → Prop} →
  {motive : (a : α) → Acc r a → Sort v} →
  ((x : α) →
    (h : (y : α) → r y x → Acc r y) →
    ((y : α) → (hr : r y x) → motive y (h y hr)) →
    motive x (Acc.intro x h)) →
  {a : α} →
  (t : Acc r a) →
  motive a t
```

Allowing this recursor to unfold definitionally through proof irrelevance is one of the two undecidability channels
excluded by Raccoon. A proof of `Acc r a` may be represented canonically from its exact proposition, but that does not
license recursive evaluation through the reconstructed child-proof function. In particular, proof reconstruction is
an ordinary-match certificate, not a structural-recursion certificate.

K2 retains the logical theorem that well-founded recursion exists and satisfies its equation while declining to make
that theorem a definitional computation rule.

## 3. Lean 4.30 export facts

The parity target used by M0 is Lean 4.30.0 at
`d024af099ca4bf2c86f649261ebf59565dc8c622`. `Init/WF.lean` contains:

- the recursive proposition `Acc` and constructor `Acc.intro`;
- the non-recursive proposition `WellFounded` and constructor `WellFounded.intro`;
- generated `Acc.rec`, `recOn`, and `casesOn` recursors;
- reducible `Acc.ndrec` and `Acc.ndrecOn` wrappers;
- `WellFounded.recursion`, `fixF`, and `fix` definitions;
- `WellFounded.fixF_eq` and `fix_eq` theorem statements.

Lean 4.30 also imports `Init/WFComputable.lean`, which adds computable `Acc.recC`, `ndrecC`, and
`ndrecOnC` variants, `WellFounded.fixFC`/`fixC`, and public `[csimp]` equality bridges between the
logical and computable operations. These declarations were not covered by the 4.24 cluster policy.

For `Acc.rec.{v,u}`, the first exported universe argument is the motive-result universe `v`; the second is the carrier
universe `u`. T3 retains and validates this order, but it does not select different operational heads by universe:
every `Acc.rec` occurrence is sealed.

M0 now finds eleven Sort-motive `Acc.rec` users outside the old fix cluster in `Init`:

```text
Acc.recOn
Acc.ndrecOn
Acc.ndrecOn.eq_1
Acc.rec_eq_recC
Acc.ndrecOn_eq_ndrecOnC
WellFounded.fixF.eq_1
Acc.ndrec
Acc.ndrec.eq_1
Acc.ndrec_eq_ndrecC
Acc.casesOn
WellFounded.fixF_eq_fixFC
```

The fixed cluster recognized by the scanner is:

```text
Acc.rec
WellFounded.recursion
WellFounded.fixF
WellFounded.fixF_eq
WellFounded.fix
WellFounded.fix_eq
```

K2 defines the trusted semantic boundary. T3 owns recognition and translation of these exported names. The 4.30
bridge and generated-equation declarations require an explicit compatibility case; none may become a definitional
rewrite or bypass the sealed `Acc.rec` boundary.

## 4. Kernel invariants

K2 must preserve all of the following:

1. **No proof metric.** `TerminationChecker` continues to reject every proof-valued structural, lexicographic, or
   measure component. K2 adds no exception.
2. **No recursive proof evaluator.** Neither `Interpreter` nor `ValueEquivalence` gains an `Acc` reduction case.
3. **No sealed ι-rule.** Applying sealed `Acc.rec` to `Acc.intro x h` remains a neutral application.
4. **Propositional equation only.** The constructor equation is a proof term. It is never registered as a rewrite,
   conversion, unification, or match-refinement rule.
5. **Exact-type proof representation.** `Acc` proofs remain `VProof` or a declaration-certified reconstructed
   `Acc.intro` governed by `ProofRecoveryInfo` and `ProofReconstruction`. No erased witness is stored in either
   representation.
6. **Ordinary matches stay ordinary.** A non-recursive match on an `Acc` proof may take one constructor step when the
   existing `ProofRecoveryInfo` recipe lets `ProofReconstruction` reconstruct `Acc.intro` from the exact proposition.
   T3 uses this path for the non-recursive `Acc.casesOn` wrapper.
7. **Uniform sealing.** `Acc.rec` is sealed at every motive universe, including exact `0`. Once its universe arguments
   specialize an eta-expanded wrapper to a Pi into Prop, ordinary proof canonicalization identifies it with the unique
   proof of that Pi proposition; a separate proof-recursion identity adds no observable definitional behavior. Core
   itself admits saturated calls only; translating source underapplication is T3's responsibility.
8. **No name-based trust.** An exported declaration named `Acc.rec` is insufficient. The `Acc` block shape and the
   exported recursor type must be validated mechanically before the reserved primitive is installed. Likewise, an
   exported family named `Eq` is not accepted as the equality used by any generated primitive proposition; it must
   first produce the validated equality capability described in §6.1.

## 5. Declaration and value representation

### 5.1 Use the existing symbolic-constant path

The sealed recursor requires no new `Value` form and no operational `Builtin` entry. Its checked value is the same
symbolic `VConst` currently used for an axiom or opaque head. Function application consequently produces the existing
neutral `VApp` form.

The K2 kernel core should represent its sealed recursor/equation pair using the existing `AxiomDecl` publication
behavior, installed only by a kernel-owned helper:

```text
Acc.rec                         : validated generated recursor type
$raccoon.wf.Acc.rec_eq          : mechanically generated constructor-equation type
```

`$raccoon.wf.Acc.rec_eq` is an internal name outside the encoding of Lean names. It is not emitted by ordinary source
elaboration or accepted from an export by name. T3 uses it to synthesize and check the public equation proofs. The
public `WellFounded.fixF_eq` and `WellFounded.fix_eq` declarations add no primitive identities: §8.4 constructs ordinary
proof applications and checks them against the exported theorem types before publication.

Using `AxiomDecl` here is a representation choice, not permission to trust the export's type. The installer first
derives and checks the declaration types as described in §§6–7. Existing publication then retains `Acc.rec` as a
symbolic `VConst`, while `Value.canonicalizeProof` publishes the propositional equation as its canonical proof value;
the internal equation name remains an environment/audit identity, not an executable proof head. A distinct
`SealedPrimitiveDecl` would duplicate the same runtime behavior and is deferred unless audit tooling needs
declaration-origin metadata that cannot live in the importer manifest.

### 5.2 Reserve the identities narrowly

Generalize the current bundled-Prelude reserved-name permission from a Boolean to an explicit permit set or capability.
Ordinary `Interpreter.evalDecl` calls have an empty permit. The translated-Prelude session may request the appropriate
K2 permit only while installing the validated core pair described below.

Suggested shape:

```scala
final case class ReservedNamePermit(names: Set[String])

object WfPrimitives {
  val SealedRecName: String = "Acc.rec"
  val EquationName: String = "$raccoon.wf.Acc.rec_eq"
  val reservedNames: Set[String] = Set(SealedRecName, EquationName)
}
```

The K2 installer receives a permit for exactly `reservedNames`. The permit bypasses only the name rejection. It does
not bypass type checking, equality/`Acc` block-shape validation, checked-body staging, or expected-type comparison.
`Acc.casesOn`, the ordinary well-founded wrappers, and their synthesized equation proofs need no permit because K2
gives their names no primitive meaning after their generated CoreAst has passed ordinary checking.

## 6. Recognizing and validating equation dependencies

### 6.1 Validate the equality dependency

Checking that a generated equation type lives in `Prop` is not enough: a corrupt export could bind the canonical `Eq`
name to an empty inductive proposition, after which publishing an inhabitant of `Eq A lhs rhs` would be inconsistent.
Every builder of a primitive propositional equation therefore consumes a shared `ValidatedEquality` capability rather
than looking up `Eq` by name.

For the pinned Lean export shape, issue that capability only after ordinary inductive checking has installed and the
validator has structurally confirmed:

- one family with type `Eq.{u} : (α : Sort u) → (a b : α) → Prop`;
- Lean metadata splitting `α` and `a` as the two parameters and `b` as the single index;
- result universe exactly `Prop`;
- exactly one constructor owned by the family, `Eq.refl`, with no proper fields after Lean's `α`, `a` parameters and
  result `Eq α a a`; its re-split Raccoon form stores the diagonal value as its sole field;
- the Raccoon calling convention `{u}` implicit and `α`, `a`, `b` explicit on the family, with `{u}`, `{α}` implicit
  and the diagonal value explicit on `Eq.refl`;
- no recursive occurrence, and agreement of exported ownership/order and parameter/index counts with the facts
  derived from the checked declaration.

Lean's redundant block metadata and Raccoon's checked inductive split deliberately describe different presentations.
T1 must retain Lean's `numParams = 2`, `numIndices = 1` metadata (`α` and the left endpoint are Lean parameters), while
lowering the checked Raccoon family to parameters `{u}`, `α` and indices `a`, `b`. The validator compares both facts;
it must not copy Lean's one-index split into Core or derive the retained Lean metadata from Core's two indices.

Binder and namespace spellings are not evidence. `ValidatedEquality` retains the checked family and constructor heads
that the equation-type builder must use; the builder never reconstructs either head from the string `"Eq"`. A future
prelude-alignment mode that reuses a differently split but extensionally standard Raccoon equality must add and prove a
separate accepted shape rather than silently weakening this validator.

Installation order is consequently fixed: install and validate `Eq`/`Eq.refl`; install and validate `Acc`/`Acc.intro`;
validate and install sealed `Acc.rec`; only then generate and install `$raccoon.wf.Acc.rec_eq`. The equality capability
is the sole equation-builder dependency not contained in `AccRecursorShape`.

### 6.2 Validate `Acc`

K2 is intentionally specific to Lean's accessibility predicate rather than a general facility for arbitrary recursive
Prop recursors. Before installation, validate the checked logical block:

- one public family named by the importer's canonical encoding of `Acc`;
- parameters corresponding to `α : Sort u` and `r : α → α → Prop`;
- one index `a : α`;
- result universe exactly `Prop`;
- one constructor corresponding to `Acc.intro`;
- constructor fields `x : α` and `h : (y : α) → r y x → Acc r y`;
- constructor result `Acc r x` with uniform family parameters;
- the Raccoon calling convention `{u}` implicit and `α`, `r`, `a` explicit on the family, with `{u}`, `{α}` implicit
  and `r`, `x`, `h` explicit on `Acc.intro`; relation and child-function arguments are all explicit;
- exactly one recursive occurrence, in the result of `h`;
- the block and constructor pass the ordinary positivity, universe, parameter, and proof-recovery checks;
- exported constructor ownership/order, `numParams`, `numIndices`, `isRec`, and rule headers agree with facts derived by
  `AccRecursorShape` and the T1 export IR.

The check is structural and type-directed. Binder spellings and pretty-printed syntax are irrelevant. Failure is an
export-parity error with family/constructor provenance, never a fallback to trusting the named constant.

Today's `InductiveMeta` does not retain the parameter/index split, block recursiveness, or exported recursor rules. The
initial `AccRecursorShape` must therefore consume both:

- the original checked `CoreAst.Decl.InductiveDecl` plus the post-install family/constructor values; and
- the T1 export block IR containing redundant Lean metadata and recursor rule headers.

`header.params`/`header.indices` supply the split after ordinary inductive checking has validated their types. The
shape builder re-evaluates the constructor telescope/result in the installed environment and derives the recursive
occurrence and expected rule header structurally; it does not pretend those facts already live in `InductiveMeta`.
Exported redundant fields are compared against this derived shape, never against nonexistent metadata.

The completed K6/T2 `LogicalExtendedBlock` will become the final authority and replace these two interim inputs. The
singleton builder must return a neutral descriptor that the later one-component logical block can implement. Do not
encode the expected recursor type as an unchecked string or bundled source declaration.

## 7. Recursor installation

### 7.1 Derive and compare the public type

Mechanically derive the complete `Acc.rec` telescope shown in §2 from the checked family and constructor metadata.
Generate fresh `LocalRef`s for every universe, parameter, motive, minor, index, major, and induction-hypothesis binder.
No exported local id or source span is reused as kernel identity.

Validate all of the following before publication:

- exported universe-parameter count and order;
- motive binder shape and motive-result universe;
- minor-premise field and induction-hypothesis order;
- induction-hypothesis result `motive y (h y hr)`;
- minor result `motive x (Acc.intro x h)`;
- major type `Acc r a` and final result `motive a t`;
- the sole exported rule belongs to `Acc.intro` and has the expected field count.

Compare the evaluated exported and derived types by `ValueEquivalence.defEq`. A mismatch rejects the declaration; the
exported rule RHS is not evidence for accepting the primitive.

Core lowering follows Raccoon's forced-implicit discipline. The universe levels, carrier, and final index remain
forceable implicits. The relation and motive do not: proof collapse prevents recovering them from later proof-bearing
types, so T3 lowers those two binders to explicit Core arguments and retains their fully explicit export arguments at
every occurrence. This is a calling-convention normalization, not a change to the dependent telescope above.

### 7.2 Uniformly sealed route

Install the validated public name `Acc.rec` as a symbolic constant. Ignore its executable exported rule RHS after any
header validation required for export parity. An application remains neutral for constructor, reconstructed, erased,
axiom, and blocked proof majors alike.

This route is used for every motive-result universe: exact zero, definitely positive, and unresolved/conditional.
Raccoon Core applications saturate one complete Pi telescope; they do not represent underapplication. T3 therefore
eta-expands a Lean partial occurrence into a lambda whose body is one saturated call. At `v = 0`, every eta-expanded
wrapper whose remaining codomain is Prop is handled by ordinary Pi-proof canonicalization. A separate `recProp`
identity would therefore produce the same observable proofs while adding a trusted generated principle and a routing
branch.

Lean export constants carry all universe arguments even when the value is later passed first-class or partially
applied. T3 preserves those arguments, always emits the sealed public head, and eta-expands any underapplication before
producing Core.

### 7.3 Non-recursive `Acc.casesOn`

`Acc.casesOn` is the one non-recursive member of the four M0 out-of-cluster users: its minor receives the constructor
fields but no induction hypothesis. Translating its exported body literally through sealed `Acc.rec` would lose a safe
one-step definitional reduction.

T3 instead synthesizes `Acc.casesOn` directly as an ordinary match after validating its exported type and sole rule.
At a data motive the match fires exactly when the existing `ProofReconstruction` certificate reconstructs
`Acc.intro`; otherwise it remains stuck. At a Prop motive ordinary proof canonicalization applies. This adds no proof
metric or recursive child traversal.

`Acc.recOn`, `Acc.ndrec`, and `Acc.ndrecOn` remain recursive wrappers over sealed `Acc.rec` and receive no analogous
escape hatch.

## 8. Primitive constructor equation

### 8.1 Statement

Generate one primitive theorem for the sealed head. In Lean notation its conclusion is:

```lean
Acc.rec intro (Acc.intro x h)
  = intro x h (fun y hr => Acc.rec intro (h y hr))
```

with the full parameters and dependent motive from §2. Both sides have type
`motive x (Acc.intro x h)`. Every occurrence of `Acc.rec` in this statement is the sealed public head.

The equation type is generated from the checked `AccRecursorShape` and the `ValidatedEquality` family head from §6.1.
It is checked as a proposition before its canonical proof is published. Its value follows the ordinary
proof-representation policy and contains no executable witness. Looking up an export declaration spelled `Eq` is not
an admissible substitute for the capability.

### 8.2 Strength after proof collapse

The ledger must record the equation as it is actually interpreted by Raccoon's proof representation, not only its
source syntax. The child function

```text
h : (y : α) → r y x → Acc r y
```

is itself a proof of a Pi proposition. Any two inhabitants of that type canonicalize to the same proof eta-lambda.
Likewise, every proof `t : Acc r a` canonicalizes from the exact proposition, either to the same reconstructed
`Acc.intro` recipe or to witness-free `VProof` when reconstruction is unavailable.

Consequently the primitive equation effectively validates the following instantiated behavior: for any
`t : Acc r a`, sealed recursion is propositionally equal to one unfolding through the canonical child proof `h₀` at
that exact proposition. This is stronger-looking than a constructor equation over an observable accessibility tree,
because no such tree survives proof collapse. It is nevertheless the intended theorem: proof irrelevance identifies
the source proofs, and the rank/well-founded-recursion model supplies a result satisfying the equation independently of
which proof witness was presented.

The `kernel-theory.md` ledger entry must state this collapsed form explicitly so future audits check the real axiom
strength against the model.

### 8.3 Operational status

The equation is not added to:

- `Interpreter.evalApply`;
- `ValueEquivalence.defEq` or apartness;
- `EqStore` unification;
- match refinement or reachability;
- native-operation interception;
- any implicit simplifier or normalization pass.

Consequently `rfl` must not prove the equation merely because the major is `Acc.intro`. A translated proof must apply
the primitive lemma explicitly, normally through `Eq.subst`/rewriting already present in its exported proof term or a
T4 patch.

The two sides must also remain **not apart**. Neither axiom-headed neutral applications nor their transparent frames
provide constructor no-confusion evidence. Match reachability may not discard a branch merely because the sides are
closed, stuck, or syntactically different. This is permanent case law for every propositional equation primitive, not
only K2.

### 8.4 Trust granularity and wrapper opacity

The initial implementation trusts only the generic `Acc.rec` equation. `WellFounded.fixF_eq` and
`WellFounded.fix_eq` are ordinary checked applications of it, synthesized while the wrapper bodies remain available
inside the atomic import transaction.

Modulo implicit parameters, synthesize `fixF_eq` by instantiating `$raccoon.wf.Acc.rec_eq` with:

```text
motive := fun x _ => C x
minor  := fun x h ih => F x ih
h₀     := fun y p => Acc.inv acx p
```

For `fixF_eq`, `acx` is the local accessibility-proof binder from the checked exported theorem telescope; it is not a
global lookup. The displayed `minor` is likewise not independently reconstructed by name. Pattern-match the checked
`fixF` body at its validated sealed-recursion occurrence, `Acc.rec <minorTerm> ... a`, and reuse `<minorTerm>` in the
equation instantiation; for the pinned body it has the displayed beta/eta shape. Likewise, pattern-match the checked
`fix` body as `fixF F x <accTerm>` and reuse `<accTerm>` as the `acx` argument when synthesizing `fix_eq`; for the pinned
body this is `apply hwf x`. Match the already validated `Acc.rec` identity and the transaction-local `fixF` declaration
identity, not strings such as `"WellFounded.apply"`. A body outside these pinned patterns is an unsupported export
shape, not a signal to guess a term or add a primitive proof.

Checking `fixF_eq` against the exported theorem type requires one transaction-local unfold of `fixF`, beta reduction,
and proof collapse for `acx ≡ Acc.intro x h₀`. Checking `fix_eq` additionally requires one transaction-local unfold of
`fix` to expose `fixF F x <accTerm>`, after which the checked `fixF_eq` instance applies; the remaining
`Acc.inv <accTerm> p ≡ apply hwf y` obligation is again proof irrelevance at the exact proposition. These are exactly
the conversion capabilities used when the checker compares each synthesized application's inferred type with the
exported expected type, so no statement-only validation path is needed.

`Acc.inv` needs ordinary declaration/type checking but no K2 identity or shape validation. It occurs only as an
inhabitant of an `Acc` proposition, so its spelling and proof body disappear under exact-type proof collapse. `Eq` is
different: it is the family forming the proposition itself, not a proof argument inside it, which is why §6.1 must
validate its inductive meaning.

The staging sequence is:

1. translate and typecheck each wrapper body while retaining its checked body in the import transaction;
2. extract and type-validate `<minorTerm>` and `<accTerm>` from the two pinned checked-body patterns above;
3. synthesize the `fixF_eq` application and check it against the exported theorem type;
4. synthesize `fix_eq` from that checked term and check it against its exported theorem type;
5. publish the wrappers with exported opacity and publish both checked theorem declarations together.

Published theorem values canonicalize exactly as any other checked proofs; their synthesized bodies are discarded.
A failed check publishes neither the wrappers nor the equations, so no later declaration can observe a half-installed
cluster.

### 8.5 Proposed axiom-ledger entries

K2 adds only the following explicit trust surface. These entries are copied into `kernel-theory.md` when K2.1 lands:

| Identity | Assertion actually trusted | Admission check | Operational effect |
|---|---|---|---|
| `Acc.rec` | A polymorphic inhabitant of the mechanically derived recursive `Acc` eliminator type exists. | Checked `AccRecursorShape`; exported type agrees exactly. | Sealed symbolic data head; no reduction rule. |
| `$raccoon.wf.Acc.rec_eq` | The sealed inhabitant satisfies §8.1, interpreted at the proof-collapsed strength stated in §8.2. | Equation type generated from `AccRecursorShape` plus `ValidatedEquality`, then checked as a proposition. | Canonical proof only; never a definitional/native rewrite. |

The public theorem names do not establish either assertion by themselves. Each is installed only by the permit named
in §5.2 after its row's admission check succeeds. Synthesized `fixF_eq`/`fix_eq` are deliberately absent: checked proof
terms need no axiom-ledger entries.

If proof extraction proves brittle for a future pinned Lean version, the importer must report an unsupported cluster
shape. Replacing either proof with a primitive is a documented contingency, not an automatic fallback: it requires a
new reserved identity, permit, statement builder, and ledger entry before it can land. The temporary checked wrapper
body is validation evidence, not a runtime delta rule, and is discarded when an opaque wrapper is published.

## 9. T3 mapping policy

K2 supplies the primitive identities and type/equation builders. T3 performs the following fixed translations:

| Exported declaration/use | Translation |
|---|---|
| `Acc` / `Acc.intro` | ordinary inductive block and constructor |
| declaration `Acc.rec` | validate exported metadata/type; install the uniformly sealed public primitive |
| every occurrence `Acc.rec.{v,u}` | sealed public `Acc.rec`, preserving and validating both universe arguments |
| first-class or partial `Acc.rec` occurrence | eta-expand to a lambda containing one saturated call to sealed `Acc.rec` |
| `Acc.casesOn` | validate its exported type/rule and synthesize a direct non-recursive ordinary match |
| `Acc.recOn`, `ndrec`, `ndrecOn` | translate as recursive wrappers over sealed `Acc.rec` |
| 4.30 `recC`/`ndrecC`/`ndrecOnC` bridge declarations and generated `.eq_1` theorems | validate and classify explicitly in T3; never install as definitional rewrites merely because they are `[csimp]` bridges in Lean |
| `WellFounded` / `WellFounded.intro` | ordinary inductive block and constructor |
| `WellFounded.recursion`, `fixF`, `fix` | typecheck bodies in the atomic K2 staging transaction, then publish with exported opacity |
| `WellFounded.fixF_eq`, `fix_eq` | synthesize the checked proof applications from §8.4; publish through ordinary proof canonicalization |
| downstream users of the equation lemmas | translate unchanged |

T3 recognizes canonical decoded Lean names before general name mangling. It also checks the target lean4export version;
a producer version with a different cluster shape requires an explicit compatibility case.

## 10. Interaction checklist

### Proof irrelevance

`Acc.intro` contains a proof-valued child function. The existing `ProofRecoveryInfo` /
`ProofReconstruction` analysis may reconstruct it only from the exact proposition and proof eta. K2 never reads an
original witness. Sealed applications carry only canonical proof arguments, and the equation proof is itself canonical.

### Termination

K2 creates no `Lam` with a recursive self and no `DecreaseSpec`. Existing rejection of proof-valued metrics remains the
decisive guard. The recursive calls appearing in the *statement* of the primitive equation are ordinary occurrences of
the sealed constant, not evaluator recursion.

### Positivity and inductive checking

`Acc` must pass the same strict-positivity checker as every translated inductive. The exceptional recursor does not
weaken positivity or constructor result checks. A declaration that merely resembles `Acc` but fails the checked shape
gets no primitive.

### Structure eta and projections

`Acc` is recursive and indexed, so it is not structure-eta eligible. Any positional projection capability is governed
by the ordinary singleton-family rules and the Prop-field restriction; K2 adds none. `WellFounded` is non-recursive but
its Prop instances still follow proof representation rather than data structure eta.

### Quotients and axioms

The equation adds propositional equality, not definitional equality. It must therefore be included in the axiom ledger
and in every audit that asks whether equality is coarser than constructor structure. It creates no constructor
no-confusion exception and no new injective head. Axiom-headed neutrals are never apart merely because they are closed
or syntactically distinct; match reachability must keep every branch for which no existing constructor evidence proves
impossibility. Add this as `kernel-theory.md` case law alongside the pending blocker-set case-law edit rather than
silently broadening the notion of closed-normal-form disequality later.

### Canonicity

A sealed `Acc.rec` application at a data motive can be a closed stuck data term—for example, a closed `Bool` that is
neither constructor-headed nor reducible. This is the existing canonicity cost of symbolic axiom/opaque applications,
but K2 makes such terms an unconditional part of translated Mathlib environments. Kernel code must not assume that a
closed inhabitant of an inductive data type exposes a constructor; it may instead remain a neutral `VApp`.

### Universes

The carrier and motive universes retain exported order and normalized `imax` structure. They affect the validated
recursor type but never select an operational route: every universe instantiation uses the same sealed head.

### Native literals

K2 enables the implemented trusted native equations for `Nat.div`-class operations to cite propositional equation
lemmas rather than unfold well-founded definitions. Native operation interception remains separately reserved and is
admitted only by K3's Lean-style trusted bootstrap rule; it is not part of `Acc.rec` evaluation and does not consume a
K2 capability. Existing `Packed.runOp` dispatch accepts only the expected
`VPacked` arguments and returns `None` for a sealed neutral, after which the structural fallback may remain stuck. K2
must preserve that fall-through behavior rather than treating a closed non-literal argument as an evaluator error.

## 11. Error model and diagnostics

Add K2/T3-specific errors with declaration provenance for:

- reserved K2 name installed without the importer permit;
- equality family/constructor shape mismatch or equation generation attempted without `ValidatedEquality`;
- `Acc` family/constructor shape mismatch;
- exported `Acc.rec` universe count or order mismatch;
- exported recursor type differs from the mechanically derived type;
- exported rule owner, constructor, or field count mismatch;
- inability to generate or typecheck the primitive constructor-equation proposition;
- a synthesized equation proof that does not check against the exported theorem type;
- failure to retain/check a wrapper body before applying its exported opacity hint;
- a fixed-cluster name encountered under an unsupported lean4export/Lean version;
- an attempt to register the equation as a definitional/native rewrite.

Diagnostics should distinguish `UnsupportedWfExportShape` from ordinary type mismatch so T4 does not misclassify a K2
recognition failure as a general Lean/Raccoon defeq gap.

## 12. File-by-file implementation plan

### Kernel-independent design and metadata

- `docs/wf-recursion.md`: this specification.
- `docs/kernel-theory.md`: add the K2 ledger entries from §8.5 and a case-law entry stating that proof metrics and
  recursive proof ι-reduction remain forbidden.
- `docs/mathlib-export-port.md`: change the K2 gate from spec review to implementation/complete as phases land.
- `docs/mathlib-export-port.md`: retain the M0/M1 parity pin to lean4export 3.1.0 tag `v4.30.0`, Lean 4.30.0 commit
  `d024af099ca4bf2c86f649261ebf59565dc8c622`; future changes reopen the K2, K3, and K6 shape assumptions.

### Reserved identities and installation

- Add `ValidatedEquality` (shared with future propositional primitives) and `WfPrimitives.scala` with canonical
  internal/public names, the singleton `Acc` shape descriptor, expected recursor/equation-type builders, and the
  checked installer. The equation builder requires the equality capability as an explicit argument.
- Use the shared reserved-name registry and narrow `ReservedNamePermit`s. `Packed.reservedNames` remains the Nat subset;
  K3 derives its native permit and validation profile from one sealed `BootstrapAuthority`, while K2 receives only
  `ReservedNamePermit.wellFounded` at its installer boundary.
- Reuse existing `AxiomDecl` publication: symbolic for the data-valued recursor, proof-canonicalized for the equations.
  Do not add a `Builtins` entry or evaluator case.

### Recursor derivation seam

- Initially derive the singleton expected telescope through `AccRecursorShape` over the checked Core declaration,
  post-install values, and T1 export IR; current `InductiveMeta` alone is insufficient.
- When K6/T2 lands, make the one-component `LogicalExtendedBlock` recursor descriptor implement the same interface and
  delete any duplicated telescope construction.
- The type builder must use `AstNodeId.synthetic()`/fresh `LocalRef`s and must be deterministic under the exported block
  order.

### T1/T3 integration

- Validate the pinned Lean `Eq` block and retain its capability before K2 equation installation.
- Extend the future export declaration IR to retain `Acc.rec` universe parameters, rule headers, and RHS references
  until K2 classification is complete.
- Translate every `Acc.rec` constant-with-levels node to the same sealed head while preserving its universe arguments.
- Add an atomic staging transaction that checks wrapper bodies, extracts the `fixF` minor and `fix` accessibility term
  from their pinned checked-body patterns, and checks the synthesized `fixF_eq`/`fix_eq` proof terms before publishing
  wrappers with their exported opacity.
- Synthesize `Acc.casesOn` as the validated direct-match exception and translate the recursive wrappers per §9.
- Replace exported equation proof bodies with the checked applications from §8.4.
- Emit K2 classification and patch provenance in the per-declaration benchmark/failure report.

## 13. Test plan

### Primitive sealing

- Install a synthetic checked `Acc` declaration and the validated primitive.
- Apply sealed `Acc.rec` with a data motive to a literal `Acc.intro`; assert the result is a neutral application.
- Repeat with an erased/reconstructed proof, an axiom proof, and a blocked proof; none may enter a recursive evaluator.
- Use a minor premise whose evaluation would fail or diverge if entered; forming the sealed application must terminate
  without evaluating the minor body.
- Assert the primitive has no `LamBody`, recursive self, native implementation, or reduction rule.

### Uniform sealing and proof collapse

- Translate motive universe `0`, a positive constant level, a level parameter, and unresolved `imax` to the same
  sealed head.
- Pin that kernel Core rejects underapplication. In T3 tests, eta-expand each exported partial occurrence and, at
  `v := 0`, verify every wrapper whose remaining type is Pi-into-Prop canonicalizes to the same proof eta-lambda that a
  hypothetical generated Prop recursor would publish.
- Substitute `0` for a previously unresolved level and verify the sealed occurrence's proof result canonicalizes
  normally without a routing change.
- Verify first-class occurrences and the saturated bodies of eta-expanded partial occurrences retain the sealed
  public identity.

### Constructor equation

- Validate the standard `Eq` block before generating the equation; assert the builder cannot be called without the
  resulting `ValidatedEquality` capability.
- Reject a named `Eq` with no `refl`, an extra constructor, a non-diagonal constructor result, the wrong parameter/index
  split, or a non-Prop result; no equation proof may be published.
- Generate and typecheck the full dependent constructor-equation type.
- Apply its proof and verify the result is the canonical representation of that equality proposition.
- Assert `defEq` between the equation's left and right data terms remains false/stuck without using the proof.
- Assert the two sides are not apart, even when both are closed and syntactically distinct.
- Put the two sides in match indices/reachability constraints and assert no branch is pruned without constructor
  no-confusion evidence.
- Repeat the not-apart/reachability pins for a generic axiom-headed neutral to make the case law independent of K2's
  exact names.
- Assert `rfl` alone cannot replace the primitive lemma at a nontrivial data motive.
- Verify no equation name appears in evaluator, native-operation, or equality dispatch tables.

### Derived wrapper equations

- Extract the minor from `Acc.rec <minorTerm> ... a` in the checked `fixF` body and the accessibility argument from
  `fixF F x <accTerm>` in the checked `fix` body. Reuse those exact terms, and reject body-shape changes rather than
  resolving either dependency by name.
- Synthesize and check `fixF_eq` as one instantiation of the generic equation, pinning one `fixF` unfold, beta
  reductions, and proof-collapse comparison of `acx` with `Acc.intro x h₀`.
- Synthesize and check `fix_eq` from the checked `fixF_eq` term, pinning proof collapse between
  `Acc.inv <accTerm> p` and `apply hwf y`, plus the one `fix` unfold needed to expose `fixF F x <accTerm>`.
- Publish both through ordinary theorem checking/canonicalization and assert that neither name is reserved or appears
  in the axiom ledger.
- Corrupt either exported theorem type and assert the entire wrapper/equation transaction publishes nothing; do not
  fall back to a primitive proof.

### Shape and export validation

- Reject a non-Prop `Acc`, wrong relation type, missing index, extra constructor, non-recursive child, negative child,
  wrong constructor result, or mismatched exported recursor type/rule header.
- Vary `numParams`, `numIndices`, `isRec`, constructor ownership, and rule headers independently in the T1 fixture and
  verify comparison is against `AccRecursorShape`, not current `InductiveMeta` fields.
- Reject correct names under the wrong lean4export version or without the K2 reserved-name permit.
- Assert that the production installer accepts only `ValidatedEquality` plus `AccRecursorShape`; no method accepting a
  caller-supplied recursor type is reachable from T1/T3 after K2.2.
- Accept alpha-renamed binders and irrelevant source spans.

### Consistency regressions

- Retain the existing proof-metric rejection tests.
- Pin that one ordinary non-recursive match on reconstructible `Acc.intro` may fire, while recursive data elimination
  remains sealed.
- Pin that synthesized data-motive `Acc.casesOn` takes that one step, while `recOn`, `ndrec`, and `ndrecOn` do not gain
  recursive reduction.
- Add a must-terminate probe exercising a constructor-headed accessibility proof and a self-referential-looking minor.
- Apply a native Nat operation to a sealed `Acc.rec` result of type `Nat`; assert native dispatch falls through safely
  and the structural application remains stuck rather than crashing or inventing a literal result.
- Run the full consistency, proof-collapse, quotient, structure-eta, blocker-set, termination, and native-literal suites.

### Real-export gate (T3)

- Validate the real Lean 4.30 `Eq` block and issue `ValidatedEquality` before any primitive equation is generated.
- Validate and install the real Lean 4.30 `Acc` block and `Acc.rec` declaration.
- Classify and translate all eleven M0 out-of-old-cluster users, including the `WFComputable` bridges.
- Translate `WellFounded.recursion`, `fixF`, `fix`, and their equation lemmas.
- Require zero unclassified K2 failures in `Init` and `Mathlib.Logic.Basic`.
- Report every sealed `Acc.rec` occurrence and direct-match `Acc.casesOn` synthesis by declaration.

## 14. Landing plan

### Phase K2.1 — specification and sealed identity

- Land the axiom-ledger/case-law text.
- Add the shared reserved-name permit mechanism and `WfPrimitives` identities.
- Use a test-only staging harness to publish a supplied, already checked expected recursor type as an inert symbolic
  constant. It must be absent from production importer paths and deleted when K2.2 lands; no production API accepting a
  caller-supplied recursor type may survive.
- Pin the absence of evaluator/native behavior.

### Phase K2.2 — checked `Acc` shape and equation

- Build the shared `ValidatedEquality` descriptor and reject named-but-nonstandard equality blocks.
- Build the singleton `AccRecursorShape` from the checked declaration/post-install values and synthetic export IR.
- Derive and compare the full public recursor type.
- Generate and install the dependent primitive constructor equation from both validated descriptors.
- Remove the K2.1 supplied-type staging harness and make the descriptor-taking installer the only production entry.
- Land uniform-sealing/proof-collapse tests, negative shape/type tests, apartness/reachability pins, and the
  must-terminate probe.

At this point the kernel portion of K2 is complete independently of the NDJSON translator.

### Phase T3.1 — real export mapping

- Recognize and validate the Lean 4.30 `Eq` dependency and expanded WF/WFComputable cluster in declaration order.
- Seal all `Acc.rec` occurrences, synthesize direct `Acc.casesOn`, and translate the recursive wrappers.
- Add atomic wrapper/equation staging, extract the minor/accessibility terms from checked wrapper bodies, and
  synthesize/check `fixF_eq`/`fix_eq` from the generic equation before applying wrapper opacity.
- Run the real-export gate and feed any remaining definitional reliance into T4.

## 15. Acceptance criteria

K2 is complete when:

- the equation builder receives a structurally checked `ValidatedEquality` capability and rejects equality-by-name,
  including an empty `Eq` block;
- the public Sort-motive `Acc.rec` type is mechanically derived from a checked `Acc` declaration and validated against
  the export;
- its value is a symbolic constant with no evaluator, match, fixpoint, or native reduction path;
- constructor-headed, reconstructed, erased, axiom, and blocked accessibility proofs all remain non-recursive under
  data elimination;
- every motive universe uses the same sealed `Acc.rec`, while T3 eta-expands partial occurrences and Prop-specialized
  wrappers canonicalize by ordinary proof irrelevance;
- non-recursive `Acc.casesOn` uses a separately validated ordinary match and no other recursive wrapper gains that
  reduction;
- the constructor equation is available propositionally and absent from definitional equality;
- `fixF_eq` and `fix_eq` are synthesized checked applications of that equation, add no reserved identity or ledger
  entry, and are published atomically with their opaque wrappers;
- the equation's sides and generic axiom-headed neutrals remain not-apart and cannot justify reachability pruning;
- proof-valued metrics remain rejected without exception;
- reserved primitive identities cannot be installed by ordinary declarations;
- no production importer path can install `Acc.rec` from a caller-supplied type without both validated descriptors;
- native Nat dispatch safely falls through on sealed neutral arguments;
- all K2-specific failures carry export provenance;
- the existing consistency suite and new must-terminate probes pass;
- T3 translates the complete real `Init`/`Mathlib.Logic.Basic` cluster with no unclassified K2 failure.

## 16. Resolved and remaining review decisions

The following choices are intentionally recorded for iteration:

1. **Uniform sealing — resolved.** Every `Acc.rec` occurrence is sealed. Core applications are saturated, so T3
   eta-expands exported partial occurrences; at `v = 0`, each resulting Pi-into-Prop wrapper is already definitionally
   identified by proof irrelevance. A third `recProp` identity would add trust accounting and routing complexity
   without adding observable computation.
2. **Equation trust granularity — resolved.** Trust only the generic `Acc.rec` constructor equation. Synthesize and
   check `fixF_eq`/`fix_eq` as direct applications inside the pre-opacity transaction. A primitive-proof fallback is a
   future theory change requiring its own permit and ledger entry, not an importer recovery path.
3. **Equality dependency — resolved.** Primitive equation builders consume `ValidatedEquality`; proposition checking
   alone does not authenticate the meaning of `Eq`. The pinned Lean block is validated and installed before K2.
4. **Axiom representation versus a distinct declaration kind.** Preferred: reuse `AxiomDecl` plus reserved installer
   provenance, since no new runtime behavior exists. Add a declaration kind only if auditing cannot recover the origin
   from the checked import manifest.
5. **Wrapper transparency.** Preferred: translate `WellFounded.recursion`, `fixF`, and `fix` normally over the sealed
   head, check their synthesized equation proofs in an atomic staging transaction, and then respect exported opacity hints. Mapping
   each wrapper to another sealed primitive is a performance fallback, not part of the initial trust surface.
6. **Interim metadata churn.** `AccRecursorShape` temporarily reads the checked Core declaration/post-install values
   plus T1 export IR because current `InductiveMeta` lacks block metadata. K6 replaces this input with
   `LogicalExtendedBlock`; the neutral shape/type builders should survive unchanged.
