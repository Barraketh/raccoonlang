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
| **Definitional conversion** `a ≡ b` | Interchangeable during type checking. Includes evaluation, congruence, proof irrelevance, level arithmetic. | `ValueEquivalence.defEq`, `checkFits`, Solve-mode unification residue |
| **Eliminator consequence** | What is *forced* in a match branch, given that the scrutinee is literally this constructor. Justified by the family's recursor (J-style): whole parameters/indices are equated; decomposing *inside* index values needs derivable injectivity (§5). | MatchChecker refinement (Invert-mode links) |
| **Propositional equality** `Eq A a b` | Provable equality in the object theory. Coarser than ≡ wherever axioms speak (`Quot.sound` today; propext/funext later). | Reachability pruning (`apart`), any "this type is uninhabited" conclusion |

Ordering: `≡` ⊆ eliminator-consequence ⊆ `=`. Evidence valid for a finer relation is **not**
automatically valid for a coarser one. In particular: definitional distinctness does not imply
propositional distinctness (pruning needs the latter), and a Solve-mode unifier solution implies
nothing at all (it is a choice).

## 2. Definitional equality specification

`defEq` (ValueEquivalence.scala) decides `≡`. Its components and their justifications:

- **Evaluation**: values are maximally reduced at construction (Interpreter); defEq compares WHNF-ish
  values. Beta/iota/builtin reduction (Quot.lift/ind on `mk`) are part of `≡`.
- **Structural congruence** per value class (`defEqStructural`), with extensional function comparison
  (run both lambdas on a shared fresh var).
- **Proof irrelevance** (definitional): any two values whose type is a *proposition* are equal.
  A proposition is a type that lives in `Prop`; the sort `Prop` itself is NOT a proposition
  (`Prop : Sort 1`). See §5 "Prop classification" for the hole this distinction fixed.
- **Levels**: semantically canonical representation `max(vᵢ + kᵢ, c)` (invariant: `c = 0` or
  `c > all kᵢ`); equality is representation equality, which coincides with `leq` both ways.
- **Cumulativity**: `checkFits` additionally accepts `Sort u ≤ Sort v` (`sortLeq`) — subsumption at
  the top level only, no deep/contravariant subtyping.
- **Identity keys** (`ValueKey`): `key1 == key2 ⇒ defEq` is trusted outright. The inputs for
  `VPi`/`VLam`/`NeutralThunk` keys are therefore explicit, unique `AstNodeId`s plus captures, not
  source spans alone. Every `parseProgram` call receives a fresh `SourceId` from the shared
  allocator (including preludes and loaded modules); checked source terms preserve their
  `span.nodeId`, while quoted or otherwise fabricated Pi/Lam/Match terms receive a fresh synthetic
  id from a reserved source. `Span` remains diagnostic metadata and need not be unique. The only
  accepted remaining identity risk is a 128-bit `ValueKey` hash collision.

### Universe rules

- `Prop = Sort 0`, `Type = Sort 1`, `Prop : Sort 1`.
- A Pi is impredicatively in `Prop` iff its **codomain is a proposition** (`getUniverse(out) ==
  Prop`). The sort `Prop` as codomain does NOT qualify: `(A: Type) -> Prop : Sort 2`. Conflating
  these made predicates proof-irrelevant → False (case law §7.4).
- Otherwise a Pi lives in `Sort(max(dom sorts, codomain sort))`.
- Telescopes are zoned `[implicit Levels][other implicits][explicits]` (`numLevelParams` recorded on
  Pi); call sites supply all non-level implicits or none; level implicits are always inferred.

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
| Proof irrelevance | **Present** (definitional) | `≡` at propositions is coarser than structure: constructor shape of proofs carries no evidence (inl/inr equal, Exists.intro not witness-injective). Planned: enforce by representation instead of by side-condition — collapse all proofs to a structureless `VProof` value (see `proof-collapse.md`). |
| `propext` | **Planned** (Mathlib) | `=` at `Prop` coarser than structure: distinct true propositions become equal (`And T T = Or T T`). Kills: apartness between propositions-as-values, injectivity of Prop-valued family formers in index positions. Audited: §5 rules already exclude these; residual TODO on `noConfusionHead` (index-position decomposition of Prop-sorted family instances). |
| `funext` | **Planned** (Mathlib) | `=` at function types coarser than intensional structure: extensionally equal, syntactically distinct functions become equal. Kills: any apartness between function values; makes "provable equations between stuck applications" constructible, which is why Invert-mode links under non-invertible frames had to be refused *before* funext lands. |
| Choice / LEM | **Planned** (Mathlib) | Anti-classical assumptions become inconsistent: notably *injectivity of type formers with large parameters* (Cantor). Family-former injectivity must never be propositional evidence. |
| Univalence | **Not planned** | Would kill generativity of Type-valued formers too. If this ever changes, re-audit §5 entirely. |

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
| **Solve-mode link** | TypeChecker `constrainFits`, InstanceSearch | The link records a leaf equation; the vars are the elaborator's to instantiate, so sub-equations reached through non-invertible frames (sufficient but not necessary) are acceptable. | Links allowed under any frame in Solve. |
| **Invert-mode link** (consequence) | MatchChecker refinement, `allowLargeElimination` | The link is forced when the scrutinee is literally this constructor: definitional invertibility of every enclosing frame. | `Ctx.invertibleFrame`; non-invertible: opaque/blocked heads, Pi binder/codomain, thunk captures, proof-valued applications. |
| **Apartness** (`UnifyFailure.apart`) | MatchChecker pruning (a case may be omitted) | *Propositional* no-confusion must be **derivable**: only a constructor clash of a Type-valued inductive (large elimination constructs the discriminating family). | `VCtor ≠ VCtor` + both `noConfusion` + neither side a proof. Family-head clashes (any sort), proofs, quotient ctors, occurs-failures, level failures: **stuck**, never apart. |
| **Stuck** (`apart = false`) | — | Means only "this algorithm cannot solve it". Must never justify pruning or disequality. | MatchChecker treats stuck ctors as reachable-unrefined (`EqStore.empty`). |
| **Frame invertibility** (failure pass-through & link transparency) | within tryUnify | Definitional injectivity: `≡` of two same-head applications forces component `≡`. True for inductive family formers and data constructors; false for proofs (irrelevance), arbitrary functions, Pi-former. | `noConfusionHead` + `isProofValue` exclusion. |
| **Large elimination permit** | MatchChecker `checkPropElimination` | Prop scrutinee eliminating into non-Prop needs subsingleton criteria: ≤1 reachable ctor and every non-proof field forced by the indices. Motive `Prop`-the-sort counts as large (it is data). | `allowLargeElimination` (Invert-mode unification of two fresh ctor copies). |
| **Prop classification** | TypeChecker `checkPi`, `checkPropElimination` | A type is a proposition iff it *lives in* `Prop`; the sort `Prop` never qualifies. | `isPropValuedType = getUniverse(v) == PropTpe`. |

**Design debt, agreed direction:** head-shape classification (`definitionallyInjectiveHead`, the
per-constructor `noConfusion` flag) is a proxy for the real predicate "the corresponding
no-confusion/injectivity theorem is derivable at the compared values' type" — Lean enforces this
implicitly because its equation compiler must cite generated lemmas that simply don't exist for Prop
inductives, type formers, or `Quot.mk`. Planned refactor: evidence grades (`Choices` /
`DefinitionalConsequences` / `PropositionalConsequences`) classified by the values' *type*;
MatchChecker decomposes the root family instantiation itself (eliminator-justified) and requests
only propositional-grade component evidence; the `noConfusion` flag is then derivable and deleted.
This closes the `TODO(propext)` and makes probe B's type-former injectivity (anti-classical, §4)
impossible to reintroduce. Sequencing: implement proof collapse (`proof-collapse.md`) first — it
deletes the proof cases this refactor would otherwise carry.

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
- **× cumulativity**: does it assume type equality where only `sortLeq` subsumption was checked?
- **× identity keys**: does it mint values from synthesized/quoted terms? Node-id collisions are an
  open hole; do not extend key-trusted surfaces.

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
   injectivity of arbitrary opaque functions. → `UnifyMode.Solve`/`Invert`, links refused under
   non-invertible frames in Invert. Tests: ConsistencyTests ("opaque function applications do not
   refine their arguments", "stuck opaque-head equations keep the refl case required");
   QuotientTests ("elaboration solves implicit metas through Quot.mk arguments" — the completeness
   Solve regained).
3. **Proof-constructor apartness vs irrelevance** (fixed): `Eq(Or(p,p), inl hp, inr hq)` is provable
   by irrelevance, yet reachability pruned refl on the inl/inr clash (irrelevance is gated off when
   the proofs are refinable) — axiom-free `False`. → proofs excluded from apartness and invertible
   decomposition (`isProofValue`). Test: ConsistencyTests ("Constructor apartness does not apply to
   proofs").
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
