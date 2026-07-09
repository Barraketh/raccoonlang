# Collapsed Proofs (`VProof`) — Design Spec

Status: **proposed, not implemented**. Companion to `kernel-theory.md` (amends §2's proof
irrelevance entry and deletes several §5 side-conditions when implemented).

## 1. Motivation

Proof irrelevance is currently a *semantic side-condition* scattered through the algorithms:
`proofIrrelevant` in defEq, the `canUseProofIrrelevance` gate in tryUnify, `isProofValue` exclusions
in apartness and frame invertibility. Each of those is a place where an algorithm holds structured
proof values and must remember not to read their structure — and forgetting was a derived-`False`
(kernel-theory §7.3).

This spec replaces the side-condition with a *representation invariant*: proofs have no structure to
read. A single value form represents every proof, so irrelevance violations become unrepresentable
rather than guarded against. This is Agda's `Prop` design (structureless, definitionally irrelevant
proofs) rather than Lean's (structured proofs + irrelevance in the conversion checker); this kernel
already chose definitional irrelevance, and collapse is its consistent endpoint.

## 2. The value form

```scala
case class VProof(tpe: Value) extends Value
```

- **Well-formedness**: `tpe` is a proposition (`tpe` lives in `Prop`; the sort `Prop` itself never
  qualifies — kernel-theory §2).
- **Equality**: `defEq(VProof(A), VProof(B)) = defEq(A, B)`. This *is* proof irrelevance; the
  `proofIrrelevant` special case in DefEq is deleted.
- **`synDeps`** = `tpe.synDeps`. Proof interiors contribute no dependencies (see §7).
- **`key`** = fresh tag mixed with `tpe.key`. All proofs of defEq propositions share a key.
- **Never a `Blocker`**: matches on proofs do not block-and-resume (see §5).

## 3. The two invariants

**(A) Collapse invariant** — *every value whose type is known to be a proposition is a `VProof`.*
"Known" is load-bearing: in a universe-polymorphic body, `x : A` with `A : Sort(u)` for generic `u`
is not known to be a proof and remains an ordinary value — which is *correct*, because irrelevance
does not hold at generic `u`. Collapse happens exactly when knowledge arrives (§4).

**(B) Witness invariant** — *`VProof(A)` is only ever created from an existing inhabitant of `A`.*
Collapse is erasure, never creation. In particular, `freshMetaValue`/placeholder creation for a
proof-typed implicit binder must produce an ordinary refinable `Var`, NOT a `VProof` — otherwise the
proof obligation silently vanishes. The meta becomes a `VProof` only by being linked to one.

Invariant (A) is assertable at chokepoints (`putLocal`, `addLink`, value construction) in debug
builds; invariant (B) is enforced by construction (the introduction rules below are the only
producers).

## 4. Introduction (collapse) points

Each rule names its witness, discharging invariant (B):

| Site | Witness |
|---|---|
| Constructor application whose result type is a proposition (`evalApply` VCtor case) | the application itself |
| Binder freshening when the binder type is a proposition (`BinderOps.freshenBinder`, match branch args for proof fields) | the bound hypothesis |
| Global publication of an axiom / def / opaque def of propositional type | the constant |
| `materialize` / `ascribe` when a value's type *resolves* to a proposition (deferred collapse after level/type metas solve, e.g. `u := 0`) | the value being collapsed |
| Match evaluation with a Prop motive (§5) | the match term (its branches were checked) |

Non-producers, deliberately: fresh metas, placeholders, unification.

## 5. Elimination (matches on proofs)

Evaluation currently reads stored constructor fields of proof values; collapse removes them, so the
three elimination shapes are handled separately:

- **Motive in Prop** (small elimination): every branch returns a proof of the same proposition, so
  evaluation returns `VProof(motive)` immediately — no branch selection, no thunk. (Type checking
  still checks every reachable branch, unchanged.)
- **Subsingleton large elimination** (motive in Type, ≤1 reachable ctor, fields forced): the
  forced-field mapping that `allowLargeElimination` already computes at check time is **recorded in
  the residual** (per-case bindings of pattern vars to index-derived terms). Evaluation reduces only
  when the scrutinee type's indices are definitionally diagonal (a runtime defEq check — the
  analogue of "Eq.rec reduces only on refl"); otherwise the match is stuck. Reducing on non-diagonal
  indices would produce a value at the wrong type; this must never be relaxed.
- **Empty elimination** (no reachable ctors): always stuck on a `VProof` scrutinee (an unblockable
  `NeutralThunk`), same as today's axiom-stuck behavior.

Check-time simplifications that fall out: the value probe in `computeReachableCtors` degenerates to
the type probe for Prop scrutinees (a Prop `ctorValue` is itself a `VProof`); the literal-VCtor
scrutinee fast path in `checkMatch` no longer arises for proofs.

**Application of proof-valued functions**: by impredicativity, `(a: A) -> P` with `P` a proposition
is itself a proposition, so functions returning proofs collapse too. `evalApply` gains a `VProof`
case: applying `VProof(pi)` returns `VProof(pi.codomain(args))`. (Quot.lift's `sound` argument is
such a value; `lift` never inspects it.)

## 6. What gets deleted

- `DefEq.proofIrrelevant` and the `propIrrelevant` flag threading (defEq's signature loses the
  parameter).
- The `canUseProofIrrelevance` gate in `tryUnify` — `VProof(A) ~ VProof(B)` simply unifies the
  types, so the solve-vs-shortcut tension disappears.
- `isProofValue` guards in apartness and frame invertibility (proofs have no heads to clash and no
  frames to descend).
- The Prop-scrutinee blocking/unblocking machinery in match evaluation for Prop motives.

kernel-theory §7.3's exploit class becomes unrepresentable rather than guarded.

## 7. Consequences to accept (decide before implementing)

1. **Structural recursion on proofs is removed.** `decreases structural(p)` on a Prop-typed argument
   currently inspects proof structure (TerminationTests pins only that irrelevance can't fake a
   decrease). Under collapse, proofs have no subterms; reject the declaration with
   `InvalidDecreaseSpec`. This is a semantic improvement — "structurally smaller" is ill-defined up
   to an equality that identifies `wrap x` with `base` — and well-founded recursion (`Acc`, needed
   for Mathlib) requires a dedicated mechanism in any case (cf. Lean's special-cased `Acc.rec`).
2. **Proof interiors vanish from `synDeps`.** A witness inside an `Exists` proof no longer
   contributes dependencies. Semantically fine (the interior can never matter), but escape/watermark
   checks lose visibility into proofs, and quoting changes (next item). Audit
   `canQuoteFromContext`, `newSolutionDependsOnFreshVar` during implementation.
3. **Quoting.** A `VProof(A)` has no syntax of its own. Since all proofs of `A` share a key, the
   quote map resolves it to *any in-scope proof term of `A`* — for locals this works today via the
   key-indexed quote context. Open question (§9): globals — either index global proof constants in
   the quote context, or carry an erased witness term on `VProof` (excluded from equality/key,
   used only for quoting and diagnostics).
4. **Diagnostics**: proofs print as `‹proof of A›`; error messages lose proof structure.

## 8. Implementation plan

- **Phase 1 (dual-running)**: add `VProof` + defEq/key/synDeps; collapse at constructor application,
  global publication, and binder freshening; keep the existing irrelevance paths and *assert
  agreement* wherever both apply. All 287 tests must stay green.
- **Phase 2 (elimination)**: Prop-motive fast path; forced-field recording in the residual +
  diagonal-check reduction for subsingleton elimination; empty-elim stuckness. This is the bulk of
  the work (MatchChecker, ElabAst.Case, Interpreter.evalMatch).
- **Phase 3 (cutover)**: deferred collapse in `materialize`/`ascribe`; delete the §6 list; reject
  structural decrease on proofs; quoting strategy.
- **New tests**: implicit proof-typed metas are NOT auto-discharged (witness invariant — a program
  needing an unprovided proof must still fail); generic-`u` bodies compare uncollapsed values
  correctly; casts along axiom-stuck proofs stay stuck; existing ConsistencyTests and irrelevance
  tests unchanged in outcome.

## 9. Open questions

- **Global witness for quoting** (§7.3): erased-witness field vs. quote-context indexing of global
  proof constants. Recommendation: erased witness field (`witness: () => ElabAst.Term`, excluded
  from `equals`/`key`), because it also serves diagnostics and avoids growing the quote context.
- **Ordering vs. the evidence-grades refactor** (kernel-theory §5 design debt): collapse first —
  it deletes the proof cases the evidence refactor would otherwise have to carry.
- **`Acc` / well-founded recursion**: out of scope here; requires its own spec when Mathlib porting
  reaches it. Collapse makes the need explicit rather than creating it.
