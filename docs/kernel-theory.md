# Kernel Theory Ledger

This document is the justification record for every semantic judgment the kernel emits. It exists
because soundness is a global property that local tests cannot defend: every soundness hole found so
far was an interaction between two individually-reasonable features, and several were *enshrined* by
tests written from the implementation's own worldview.

**The rule:** any code that emits a semantic judgment — declares two values equal or apart, treats a
unification solution as a fact, classifies a type into a universe, permits an elimination — must be
justifiable by an entry in this ledger, and the justification must hold under the *planned* axioms
(§4), not just the current ones. A rule that is merely "not exploitable today" is a finding, not a
justification. When adding a feature, walk the interaction checklist (§6).

Trust model context: everything post-CoreAst is trusted (no adversarial kernel/elaborator split);
this ledger is what that trust is *in*.

---

## 1. The three equality relations

Most historical holes were category errors between these. Any equality-flavored judgment must state
which relation it is about.

| Relation | Meaning | Decided/used by |
|---|---|---|
| **Definitional conversion** `a ≡ b` | Interchangeable during type checking. Includes evaluation, congruence, proof irrelevance, level arithmetic. | `ValueEquivalence.defEq`, `checkFits` |
| **Eliminator consequence** | What is *forced* in a match branch, given that the scrutinee is literally this constructor. Justified by the family's recursor (J-style): whole parameters/indices are equated; decomposing *inside* index values needs derivable injectivity (§5). | MatchChecker refinement (unifier links) |
| **Propositional equality** `Eq A a b` | Provable equality in the object theory. Coarser than ≡ wherever axioms speak (`Quot.sound` today; propext/funext later). | Reachability pruning (`apart`), any "this type is uninhabited" conclusion |

Ordering: `≡` ⊆ eliminator-consequence ⊆ `=`. Evidence valid for a finer relation is **not**
automatically valid for a coarser one. In particular: definitional distinctness does not imply
propositional distinctness (pruning needs the latter). Choice-mode unification (Solve links,
whose solutions implied nothing at all) was removed with its clients — every surviving unifier
link is a consequence.

## 2. Definitional equality specification

`defEq` (ValueEquivalence.scala) decides `≡`. Its components and their justifications:

- **Evaluation**: values are maximally reduced at construction (Interpreter); defEq compares WHNF-ish
  values. Beta/iota/builtin reduction (Quot.lift/ind on `mk`) are part of `≡`.
- **Structural congruence** per value class (`defEqStructural`), with extensional function comparison
  (run both lambdas on a shared fresh var).
- **Proof irrelevance** (definitional): any two values whose type is a *proposition* are equal.
  A proposition is a type that lives in `Prop`; the sort `Prop` itself is NOT a proposition
  (`Prop : Sort 1`). See §5 "Prop classification" for the hole this distinction fixed.
  Conversion applies the uniform proof equation
  `p ≡ q ⇔ tpe(p) ≡ tpe(q)` to every proof representation, including proof-typed variables. An
  erased proof is the structureless `VProof(tpe)`. Exact-type canonicalization reconstructs a
  `VCtor` when the family carries a declaration-checked recipe that succeeds at that proposition,
  and reconstructs a synthetic eta `VLam` for every proof of a Pi proposition. Checked source
  proof-lambda bodies are discarded after validation, not rewritten or executed. The stored
  `InductiveMeta.proofStorage` recipe requires one constructor and every non-Prop stored field to
  occur directly in the result family arguments (`proof-collapse.md`). Operational structure
  never changes proof equality, and unification never structurally links or decomposes proofs.
- **Structure eta** (definitional): a value of an *eta-eligible* struct type equals the
  constructor applied to its projections. Eligibility (`InductiveMeta.etaInfo`, computed by
  InductiveChecks): declared struct, one constructor, no indices, no recursive field, not
  declared in Prop. Prop instantiations of sort-polymorphic structs are proof-representation
  territory instead — they never eta-expand, and every inhabitant follows `proofStorage` based on
  its exact proposition. Enforced by
  *representation*, not a conversion rule (`StructEta.scala`): every value of eligible struct
  type is constructor-headed *from creation*. Binders freshen as the constructor of fresh field
  witnesses; neutrals (opaque constants, axioms, blocked applications and matches, recursive-call
  residuals, stuck builtins) wrap into the constructor of their stuck projections at creation.
  Ascription and materialization deliberately do NOT expand: they retype circulating values, and
  a late wrap would coexist with bare copies — proof irrelevance tolerates mixed erased/retained
  proof values, while expansion has no analogous mixed rule. Fieldwise congruence then *is* eta, a match
  on a struct scrutinee always fires (binding the branch to the scrutinee's projections), and the
  stuck projection — a `StructField`-headed application, equal by head name + base — is the only
  projection neutral form. The eligibility gate is load-bearing for decidability: "single
  constructor" alone would admit `Acc` (destructuring neutral accessibility proofs is the
  undecidability channel wf-recursion seals) and `Quot.mk` (expansion would invent a quotient
  representative); other layers also exclude both, but the gate must never rest on that
  coincidence. Known completeness gap: a value created before its type is a *known* struct
  instance stays bare (rigid binders at then-blocked types, neutrals whose types reveal only
  under a later store); rigid vars additionally cannot be expanded in place — rigid vs. refinable
  is store-relative, and metas must stay linkable (the same reason `canonicalizeProof` exempts
  Vars).
- **Packed Nat representation** (definitional): every ground bundled-Prelude `Nat` is born as
  `VPacked(NatCodec, payload, Nat)`; `decodeHead` exposes one constructor layer for matching,
  projection, and mixed packed/constructor comparison, while all ground constructor-birth and
  materialization seams fold back. Payload equality is Nat definitional equality (codec L3), and
  the mixed peel is ordinary constructor congruence (L4). Native `add/sub/mul/pow/beq/ble/blt`
  are sound bounded derived rules: admitted packed arguments return exactly the structural
  Prelude result; ordinary dispatch mismatches fall through to that definition. `pow` raises an
  explicit evaluator resource error above exponent `2²⁴`, rather than entering eager unary
  fallback. Their
  canonical names, plus `Nat` and its constructors, are reserved to the bundled Prelude, so a
  `ValueId.Const` table key cannot identify a user body (`native-literals.md` L7–L8).
- **Levels**: normalized representation `max(aᵢ + kᵢ, c)`, where an atom is a level
  variable or a normalized unresolved `imax(l, r)` (invariant: `c = 0` or `c > all kᵢ`). The
  `imax` smart constructor reduces when `r` is always zero or always positive and otherwise
  preserves the conditional atom; EqStore materialization recursively substitutes its operands
  and re-runs the smart constructor. Equality is representation equality. `Level.leq`, used only
  for inductive universe bounds, is sound and intentionally incomplete on `imax` atoms.
- **Cumulativity**: `checkFits` additionally accepts `Sort u ≤ Sort v` (`sortLeq`) — subsumption at
  the top level only, no deep/contravariant subtyping.
- **Identity keys** (`ValueKey`): `key1 == key2 ⇒ defEq` is trusted outright. The inputs for
  `VPi`/`VLam`/`NeutralThunk` keys are therefore explicit, unique `AstNodeId`s plus captures, not
  source spans alone. Every `parseProgram` call receives a fresh `SourceId` from the shared
  allocator (including preludes and loaded modules); checked source terms preserve their
  `span.nodeId`, while quoted or otherwise fabricated Pi/Lam/Match terms receive a fresh synthetic
  id from a reserved source. Packed keys mix the closed codec id, the full canonical payload
  bytes, and the packed type; key trust there is codec injectivity (L3), with no node identity.
  `Span` remains diagnostic metadata and need not be unique. The only accepted remaining
  identity risk is a 128-bit `ValueKey` hash collision.

### Universe rules

- `Prop = Sort 0`, `Type = Sort 1`, `Prop : Sort 1`.
- A Pi is impredicatively in `Prop` iff its **codomain is a proposition** (`getUniverse(out) ==
  Prop`). The sort `Prop` as codomain does NOT qualify: `(A: Type) -> Prop : Sort 2`. Conflating
  these made predicates proof-irrelevant → False (case law §7.4).
- A telescope `(x₁ : A₁) … (xₙ : Aₙ) → B` lives in
  `Sort(imax(u₁, … imax(uₙ, v)…))`, right-folding the domain sorts `uᵢ` over the codomain sort
  `v`, as Lean does. This reduces immediately to `Prop` when `v` is zero and to the ordinary
  maximum when `v` is definitely positive. The classifier is never stored in checked syntax — it
  is env-dependent for level-polymorphic telescopes, so each `VPi` instance derives it lazily
  (`Interpreter.piClassifier`).
- **Forced implicits** (single call form): a binder may be implicit only if it is *forced* —
  recoverable by structural projection from the type of a later non-implicit binder
  (`telescope/Projection.scala`; positions: the whole type, rigid-constant spine args,
  no-confusion constructor fields in indices, `Sort → level`, single-atom `u+k` levels,
  independent Pi domains, non-dependent Pi codomains; saturating through forced implicits' own
  types). Unforced ⇒ `NonForcedImplicitParam`; in constructor telescopes unforced implicits demote
  to explicit instead (rightmost-first). Call sites supply exactly the explicit args; implicits are
  never written and are reconstructed by running the compiled projection specs — at application
  checking and again at residual evaluation (checked `App`s carry only explicit args). Projection
  is a *choice*: the checker re-verifies every argument against its instantiated binder type, so
  soundness never rests on injectivity of the projected positions. A proof implicit is recognized
  checker-side by a proof-valued position of the same proposition; any proof projected there is a
  valid choice by irrelevance, without storing a witness in `VProof`. Coherence: runtime argument
  binding ascribes args to their binder types exactly as the checker's verification pass does
  (`Interpreter.ascribeArgs`), so run-world projection reads the same shapes the checker read.
- **Universes are NOT cumulative** (Lean-style): `checkFits` is defEq-only; there is no `sortLeq`
  subsumption. `Sort(1)` does not fit a `Sort(2)` binder. Non-cumulativity is load-bearing for
  forced implicits: it makes a value's `.tpe` canonical up to defEq at exactly one sort, so the
  level a projection spec reads is the only level the argument can carry (the earlier cumulative
  regime let check world and run world project *different* levels from the same argument —
  a checked equation `g(Nat) = 2` evaluated to `1`). Universe *bound* checks on constructor
  fields (`Level.leq` in InductiveChecks) are a size rule, not subtyping, and remain.

## 3. Canonicity status

The original core had canonicity: closed values reduce to constructor forms. **Axioms break it** —
a closed proof may be stuck on `Quot.sound` (or any user axiom) forever. Consequences that kernel
code must not assume:

- "Every inhabitant of an inductive type is constructor-headed" is FALSE for open terms and for
  closed proofs behind axioms/opaque defs. Empty-match justification therefore cannot be "no
  constructor value fits"; it must be propositional (the type is provably empty — `apart` evidence).
- Evaluation may return `NeutralThunk`/blocked applications for closed programs that use axioms.

## 4. Axiom ledger

Every evidence rule in §5 must remain valid under all rows of this table.

| Axiom / primitive | Status | What it coarsens or breaks |
|---|---|---|
| `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` + `Quot.sound` | **Present** (builtins + axiom, Lean-style) | `=` at quotient types is coarser than structure: `mk a = mk b` without `a = b`. `Quot.mk` must never carry constructor no-confusion. Canonicity broken (§3). |
| Proof irrelevance | **Present** (definitional) | `≡` at propositions is coarser than structure: constructor shape and fields carry no equality evidence (inl/inr equal, `Exists.intro` not witness-injective). The exact proposition chooses one operational form: a declaration-reconstructed `VCtor`, a type-directed eta `VLam` for Pi propositions, or witness-free `VProof(tpe)`. `ProofEquation` compares every proof value through its proposition and intercepts proof constructors before no-confusion (`proof-collapse.md`). |
| `propext` | **Planned** (Mathlib) | `=` at `Prop` coarser than structure: distinct true propositions become equal (`And T T = Or T T`). Kills: apartness between propositions-as-values, injectivity of Prop-valued family formers in index positions. Audited: §5 rules already exclude these; residual TODO on `noConfusionHead` (index-position decomposition of Prop-sorted family instances). |
| `funext` | **Planned** (Mathlib) | `=` at function types coarser than intensional structure: extensionally equal, syntactically distinct functions become equal. Kills: any apartness between function values; makes "provable equations between stuck applications" constructible, which is why Invert-mode links under non-invertible frames had to be refused *before* funext lands. |
| Choice / LEM | **Planned** (Mathlib) | Anti-classical assumptions become inconsistent: notably *injectivity of type formers with large parameters* (Cantor). Family-former injectivity must never be propositional evidence. |
| Checked Prop induction principles | **Planned** (K6, kernel-generated) | Adds no executable proof recursion: the principle is Pi-shaped and publishes as the canonical proof eta-lambda, which reconstructs only the instantiated conclusion. Its proposition must be derived mechanically from a kernel-checked strictly-positive inductive block—including its logical nested extension—and validated against the export; trusting an exported type would permit arbitrary false theorems. Sort-motive recursive principles such as `Acc.rec` remain K2 because proof metrics are forbidden, independently of constructor reconstruction. |
| Univalence | **Not planned** | Would kill generativity of Type-valued formers too. If this ever changes, re-audit §5 entirely. |

Trusted derived rules adjacent to this ledger, but not axioms: the reserved-name native Nat
operation table. Each admitted entry is extensionally the bundled structural definition;
ordinary dispatch mismatches may decline to that definition: `add`, truncating `sub`, `mul`,
`pow` with `pow(a, 0) = 1`, `beq`, `ble`, and `blt`. `pow` has an evaluator resource limit of
`2²⁴` on its exponent. The differential certification suite pins every entry; adding an operation
requires its structural equation, conventions, reserved canonical name, and a new certification
case.

## 5. Evidence table (unifier & match checker)

`ValueEquivalence.tryUnify` runs in a mode (`UnifyMode`) declaring what its output may be used for.

**Link invariant (both modes):** a link records exactly the equation presented at the point of
linking, or its unique forced solution — the store never invents values. Constraints with multiple
solutions (`max(u, v) = 1`) are never solved by picking one; they stay stuck. Spine unification
*postpones* stuck component equations and retries them after the rest of the spine, so constraints
that become forced once their atoms are solved elsewhere still succeed (postponement reorders work
without inventing values).

| Judgment | Consumer | Required justification | Current implementation |
|---|---|---|---|
| **Link** (consequence) | MatchChecker reachability and branch refinement | The link is forced when the scrutinee is literally this constructor: definitional invertibility of every enclosing frame. (Choice-mode Solve links — allowed under any frame — were removed with unification-based elaboration and instance search.) | `Ctx.invertibleFrame`; non-invertible: opaque/blocked heads, Pi binder/codomain, thunk captures. No evaluator consumes links. |
| **Apartness** (`UnifyFailure.apart`) | MatchChecker pruning (a case may be omitted) | *Propositional* no-confusion must be **derivable**: only a constructor clash of a Type-valued inductive (large elimination constructs the discriminating family). | `VCtor ≠ VCtor` + both `noConfusion`, after `ProofEquation` has intercepted all proof-typed values. Family-head clashes (any sort), proof equations, quotient ctors, occurs-failures, and level failures are **stuck**, never apart. |
| **Packed payload apartness** | MatchChecker pruning (a case may be omitted) | Unequal payloads may be refuted only when the closed codec claims L9: their finite decodings reach a constructor clash between derivable no-confusion heads. L3 definitional inequality alone is insufficient under planned funext. | Same-codec `VPacked` values with explicitly unequal payloads and `refutesUnequalPayloads`; Nat claims L9 because unequal unary decodings reach `zero`/`succ`. Equal payloads continue through the type equation; codecs without L9 and packed-vs-neutral comparisons are stuck. |
| **Stuck** (`apart = false`) | — | Means only "this algorithm cannot solve it". Must never justify pruning or disequality. | MatchChecker treats stuck ctors as reachable-unrefined (`EqStore.empty`). |
| **Frame invertibility** (failure pass-through & link transparency) | within tryUnify | Definitional injectivity: `≡` of two same-head applications forces component `≡`. True for inductive family formers and data constructors; false for arbitrary functions and the Pi-former. Proof applications are handled by `ProofEquation` before frame decomposition. | `definitionallyInjectiveHead`. |
| **Large elimination permit** | MatchChecker `checkPropElimination` | A Prop scrutinee may eliminate into non-Prop only when no constructor is reachable or its family carries the declaration-time `Reconstruct` recipe: one constructor and each non-Prop field directly present in the result arguments. Motive `Prop`-the-sort counts as large (it is data). | `InductiveMeta.proofStorage`; `allowLargeElimination` consults metadata plus empty reachability. At runtime the exact proposition either reconstructs an ordinary `VCtor` or remains `VProof`; no unification runs. |
| **Prop classification** | TypeChecker `checkPi`, `checkPropElimination` | A type is a proposition iff it *lives in* `Prop`; the sort `Prop` never qualifies. | `isPropValuedType = getUniverse(v) == PropTpe`. |
| **Structural decrease** (recursive call permitted) | TerminationChecker guard (`rawRecursiveSelf`) | The call's metric is strictly below the current one in the well-founded tree order of strictly positive inductive values: reachable by ≥1 constructor-field step, where an application of a function-typed field steps to a child (the field is its node's child-selector; Agda foetus / Coq guard precedent). Assumes values are well-founded trees: strict positivity (InductiveChecks) and no value-level self-capture (recursion requires a decreasing parameter). | `isStrictSubterm`: `VCtor` field descent plus `VApp`-spine stripping that must bottom out at a field (`applicationOfSubterm`); any other head (blocked match, lambda) must be defEq to the field itself. Proof metrics rejected at declaration (`InvalidDecreaseSpec`); axiom/quotient-typed metrics rejected (`requireInductiveMetric`). |
| **Packed structural decrease** | TerminationChecker guard (`rawRecursiveSelf`) | Codec order L6 is exactly reachability by one or more constructor-field steps on decoded values and is well-founded, so it is the existing structural tree order rather than a new measure. | Same-codec packed metrics compare through `codec.strictlyLess`; Nat uses numeric `<`, which realizes repeated predecessor steps. Payloads are compared directly and never decoded recursively. |

**Design debt, agreed direction:** head-shape classification (`definitionallyInjectiveHead`, the
per-constructor `noConfusion` flag) is a proxy for the real predicate "the corresponding
no-confusion/injectivity theorem is derivable at the compared values' type" — Lean enforces this
implicitly because its equation compiler must cite generated lemmas that simply don't exist for Prop
inductives, type formers, or `Quot.mk`. Planned refactor: evidence grades (`Choices` /
`DefinitionalConsequences` / `PropositionalConsequences`) classified by the values' *type*;
MatchChecker decomposes the root family instantiation itself (eliminator-justified) and requests
only propositional-grade component evidence; the `noConfusion` flag is then derivable and deleted.
This closes the `TODO(propext)` and makes probe B's type-former injectivity (anti-classical, §4)
impossible to reintroduce. Sequencing: the proof representation policy (`proof-collapse.md`) is
**done**. The refactor must preserve `ProofEquation`'s interception of reconstructed proof constructors;
it cannot assume that every proof is physically `VProof`.

## 6. Interaction checklist

Walk this list before landing any feature that touches equality, universes, or evaluation:

- **× proof irrelevance**: does the feature read constructor shape, field values, or identity of
  anything whose type might be a proposition? (Case law: 7.3, 7.4.)
- **× quotients / axioms (canonicity)**: does it assume closed values are constructor-headed, or
  that unification failure means uninhabited? (7.1.)
- **× non-forced unification**: does it consume a unifier success as a *fact* rather than a choice?
  State the mode explicitly. (7.2.)
- **× impredicativity / large elimination**: does it move data out of a proof, or classify a Pi into
  `Prop`? (7.4.)
- **× planned axioms (§4)**: is the justification a theorem, or a "nobody can currently prove the
  premise" argument? The latter is a finding.
- **× cumulativity**: none — fits are defEq-only (§2). If a feature wants subsumption between
  sorts, that is a theory change, not a local convenience; it re-breaks `.tpe` canonicity and with
  it implicit-projection coherence.
- **× identity keys**: does it mint values from synthesized/quoted terms? The collision described
  in §7.7 is fixed, but the surviving discipline is load-bearing: every fabricated Pi/Lam/Match
  receives a fresh `AstNodeId.synthetic()`; do not extend key-trusted surfaces without preserving
  it.
- **× termination order**: does the feature introduce values that are not well-founded trees —
  laziness, corecursion, value-level self-capture, weakened positivity? The structural-decrease
  judgment (§5) descends constructor fields *and applications of function-typed fields*; both
  premises are load-bearing.
- **× structure eta / expansion**: does the feature create struct-typed values off the expansion
  seams (binder freshening and neutral creation — §2 structure eta), leaving two representations
  of the same value? Does it expand a value that already circulates (the ascription/materialize
  mistake §2 rules out)? Does it trigger single-constructor behavior keyed on constructor *count*
  rather than `etaInfo`? Count-keyed triggers are the `Acc`/`Quot` trap.

## 7. Case law

Confirmed-by-probe findings, their fixes, and the regression tests that must stay green (rejecting).
The probe method — write the `False`-derivation first, confirm it typechecks, then fix, then flip
the probe into a must-reject test — is the standard procedure for anything on this page.

1. **Quot no-confusion** (fixed): match pruning + `Quot.mk`-as-constructor derived `False` from
   `Quot.sound` (disjointness *and* injectivity directions). → `apart`/stuck split; `noConfusion`
   flag. Tests: ConsistencyTests ("Quot.mk is not disjoint", "Quot.mk is not injective",
   "congruence failures under opaque heads"); QuotientTests ("genuine constructor disjointness
   still prunes").
2. **Unification mode conflation** (fixed): Solve-links consumed as refinement facts derived
   injectivity of arbitrary opaque functions. → `UnifyMode.Solve`/`Invert` split, links refused
   under non-invertible frames in Invert; Solve mode was later deleted outright with its clients,
   so all links are consequences. Tests: ConsistencyTests ("opaque function applications do not
   refine their arguments", "stuck opaque-head equations keep the refl case required");
   QuotientTests ("Quot.mk fields do not force implicit parameters" — under forced-implicit
   projection the same discipline holds at declaration time: no-confusion-less heads are not
   projection positions).
3. **Proof-constructor apartness vs irrelevance** (fixed): `Eq(Or(p,p), inl hp, inr hq)` is provable
   by irrelevance, yet reachability pruned refl on the inl/inr clash (irrelevance is gated off when
   the proofs are refinable) — axiom-free `False`. → `ProofEquation` now intercepts every proof
   representation before constructor apartness or invertible decomposition. Non-certified proofs
   erase to `VProof`; certified singleton constructors may remain operational but still provide no
   equality evidence (`proof-collapse.md`). Test: ConsistencyTests ("Constructor apartness does
   not apply to proofs").
4. **Prop-sort conflation** (fixed): `isPropValuedType` counted the sort `Prop` as a proposition, so
   `(n: Nat) -> Prop : Prop`, predicates became proof-irrelevant, and `Eq.mp ∘ congrFunP` derived
   `False`; the same conflation permitted large elimination with motive `Prop`. → §2 universe rules.
   Tests: ConsistencyTests ("Negative: predicates are not proof-irrelevant", "predicates are not
   proof-irrelevant through congrFun and Eq.mp", "Negative: elimination from Exists into
   Prop-the-sort is large elimination"); PropTests (Sort-2 classifier tests).
5. **Family-head apartness** (fixed pre-emptively): `Eq(Prop, And(T,T), Or(T,T))` pruned refl — one
   `propext` away from `False`. → family-head clashes are stuck. Test: ConsistencyTests
   ("Family-head clashes are not refutations").

6. **Positivity VLam blind spot** (fixed pre-emptively): `PositivityTarget.InductiveHead.mayOccurIn`
   returned false for `VLam`, so an inductive hidden in a lambda body under a stuck head passed
   positivity. Unreachable only because the surface grammar has no lambdas in type-argument position
   and no partial application — a grammar accident, not a justification. → `mayOccurIn` is now
   conservative for lambdas. (No language-level test is expressible until the grammar grows; the
   guard exists so that grammar growth cannot silently reopen the hole.)

7. **AstNodeId value identity** (fixed): distinct local Pi/Lam/neutral-thunk values could share a
   trusted `ValueKey` when separate parses reused a source-less offset namespace or quotation reused
   one caller span. → per-parse `SourceId`s and fresh synthetic ids for fabricated checked terms.
   Tests: ConsistencyTests ("separate parses give distinct local Pi identities", "quoted Pi siblings
   receive distinct identities while re-quotes remain definitionally equal").

**Open findings** (recorded, unfixed):

- **`TODO(propext)`** on `definitionallyInjectiveHead` (§5 design debt).

## 8. Consistency test policy

Every entry in §7 has a program that once derived `False` (or was one axiom away). Such programs are
permanent must-reject tests; they are the only test genre whose referent is the theory rather than
the implementation, so they cannot enshrine a bug. When a new hole is found: probe first, confirm,
fix, convert the probe. Do not delete or weaken these tests to make a feature land — a red
consistency test means the feature is unsound, not that the test is stale. The canonical suite is
`src/test/scala/com/raccoonlang/ConsistencyTests.scala`.
