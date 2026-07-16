# Canonical Proof Representation

Status: **implemented** (2026-07-15). Companion to `kernel-theory.md` and
`mathlib-export-port.md`.

## 1. Decision

Proof irrelevance requires more than making all proofs definitionally equal. Evaluation must also
be congruent with that equality: two equal proofs cannot expose different computations merely
because one arrived as a constructor and the other as an axiom or neutral.

Raccoon therefore chooses a proof's runtime representation solely from its exact proposition. It
keeps everything that the proposition itself reconstructs and erases everything else:

1. If a declaration-certified constructor can be reconstructed at the exact proposition, the
   canonical value is that `VCtor`.
2. If the proposition is a Pi, the canonical value is a synthetic eta `VLam`. Applying it
   reconstructs the canonical proof of the instantiated codomain.
3. Otherwise the canonical value is the structureless `VProof(proposition)`.

For example, every inhabitant of `Eq(Nat, Nat.zero, Nat.zero)` is represented as
`Eq.refl(Nat.zero)`, including an axiom. An inhabitant of `Eq(Type, Nat, Bool)` remains `VProof`:
the exact type does not determine a valid `refl` constructor.

This is canonicalization, not proof search. The inductive checker compiles a finite reconstruction
recipe into family metadata. Runtime executes that recipe and validates its result; it never runs
unification, searches constructors, or solves indices.

## 2. Declaration-time constructor recipes

The relevant metadata is:

```scala
sealed trait ProofStorage
object ProofStorage {
  case object Erase extends ProofStorage
  final case class Reconstruct(info: ProofConstructorInfo) extends ProofStorage
}

sealed trait ProofFieldRecipe
object ProofFieldRecipe {
  final case class ResultArgument(index: Int) extends ProofFieldRecipe
  case object ErasedProof extends ProofFieldRecipe
}
```

`Reconstruct` is recorded exactly when:

1. the family's declared result universe may reduce to `Prop` (its level is not provably positive);
2. the family has one constructor; and
3. every stored constructor field is either:
   - known to be Prop-valued, producing `ErasedProof`; or
   - definitionally equal to a direct argument of the constructor's result-family application,
     producing `ResultArgument(index)`.

Leading family parameters are not stored fields. A fixed positive-universe family can never have a
Prop instance, so it records `Erase` without retaining a dead reconstruction recipe. A field that
is not known to be Prop-valued at a generic universe is conservatively treated as data and must
occur directly in the result.

This is intentionally the simple singleton rule:

| Family shape | Metadata | Reason |
|---|---|---|
| `Eq.refl (x : A) : Eq A x x` | reconstruct | `x` occurs directly in the result |
| `True.intro : True` | reconstruct | one constructor, no fields |
| `And.intro (p : P) (q : Q)` | reconstruct | both fields are proofs |
| `Idx.intro (y : A) : Idx y` | reconstruct | `y` is a direct result argument |
| `Exists.intro (w : A) (h : P w)` | erase | the data witness is not in the result |
| `Nonempty.intro (w : A)` | erase | the data witness is unforced |
| `Or.inl` / `Or.inr` | erase | more than one constructor |
| `Wrapped.intro (n : Nat) : Wrapped (Nat.succ n)` | erase | `n` occurs only under `Nat.succ` |

Empty propositions use `Erase`; empty large elimination is justified separately by reachability.
The metadata may be computed for a family declared in `Sort u`, but affects only instances that
are actually known to live in `Prop`.

## 3. Exact-type reconstruction

`ProofReconstruction.reconstruct(P)` interprets the recorded recipe at an exact proposition `P`:

1. Read the family parameters from the family instance in `P`.
2. Instantiate the constructor telescope from left to right.
3. For each data field, copy its recorded result argument.
4. For each proof field, construct a shallow `VProof` at its instantiated binder type.
5. Check each argument against its binder type and check that the instantiated constructor result
   is definitionally equal to `P`.

Any failed check means that the constructor is not reconstructible at that exact type. There is no
fallback search.

For `Eq.refl`, the recipe copies the first endpoint into the stored `x` field. Instantiating its
result gives `Eq(A, x, x)`. Thus:

```text
reconstruct(Eq(Nat, zero, zero)) = Eq.refl(zero)
reconstruct(Eq(Type, Nat, Bool)) = failure
```

Repeated or constant indices are therefore constraints checked by ordinary conversion, not
unknowns solved by runtime unification.

Proof fields are deliberately shallow. For a recursive proposition such as:

```raccoon
inductive Loop : Prop
  | mk (next : Loop) : Loop
```

canonicalizing a `Loop` produces one `Loop.mk(VProof(Loop))` layer. Binding `next` in a match
canonicalizes that exposed field and produces the next layer. This permits any finite observation
without constructing an infinite value eagerly.

The recipe's constructor head is temporarily unavailable while that constructor is itself being
installed. Reconstruction simply declines during this interval and becomes available when the
declaration completes its small constructor-head promise; family metadata retains no environment
snapshot for this lookup.

## 4. Canonical proof functions

A Pi whose codomain is Prop-valued is itself a proposition. Every proof of such a Pi canonicalizes
to an actual `VLam(_, _, LamBody.ProofEta)`, whether it originated as a source lambda, an axiom, an
opaque constant, or `VProof(Pi)`.

The source body is still fully checked, including termination checking. It is discarded only after
validation; the checked residual syntax is not rewritten. Applying the canonical eta-lambda:

1. checks/ascribes its arguments against the Pi telescope;
2. evaluates the instantiated codomain type; and
3. canonicalizes a proof of that codomain by the same rules in this document.

Consequently a result such as `Eq(Nat, n, n)` becomes `Eq.refl(n)`, a nested proof Pi becomes
another eta-lambda, and a non-reconstructible proposition becomes `VProof`. The original theorem
body never executes at runtime.

This removes the former checker-time proof-body rewriting pass. There is no special evaluator rule
that treats `VProof(Pi)` as an applicable neutral; canonical values of Pi propositions are ordinary
`VLam`s.

## 5. Canonical erased values and quotation

`VProof` contains only its proposition. It carries no erased witness, local variable, or original
body. Quotation is canonical:

```text
quote(VProof(P)) = proof(quote(P))
```

`proof(P)` is a residual-only `ElabAst` intrinsic of type `P`. It is absent from source `CoreAst`,
so source programs cannot use erasure to synthesize an obligation. Evaluating it constructs a
proof and immediately canonicalizes by exact type; a quoted `proof(Pi)` therefore evaluates to the
canonical eta-lambda rather than preserving `VProof(Pi)`.

Refinable metas remain `Var`s. Erasing a placeholder would silently discharge an unsolved proof
obligation. A rigid proof binder is canonicalized only after binder checking establishes that an
inhabitant is in scope. Constructor heads and raw recursive checker lambdas are also temporarily
exempt because they must remain applicable; the validated result later crosses the ordinary
canonicalization boundary.

Forced-implicit compilation needs no exception to this representation. When a later explicit
argument type contains a proof-valued position of the implicit binder's proposition, the checker
records the structural projection path to that position. At a call, any proof recovered there is
a valid argument by proof irrelevance. No proof identity or witness is stored in `VProof`.

## 6. Proof irrelevance and conversion

Representation does not define proof equality. The conversion rule remains uniform:

```text
p : P, q : Q, P and Q propositions
-----------------------------------
p ≡ q  iff  P ≡ Q
```

Therefore proof constructor fields provide neither injectivity nor apartness; different proof
constructors of the same proposition are equal; and unification compares proofs only through
their propositions. Canonicalization adds operational congruence: equal proof values at the same
exact type also expose the same reconstructible outer form.

The latter property is what fixes the bad split:

```text
p ≡ q by proof irrelevance
match Eq.refl ... computes
match erasedProof ... stays stuck
```

If the exact proposition reconstructs `Eq.refl`, both values are now `Eq.refl`. If it does not,
both are `VProof`.

## 7. Elimination

### 7.1 Check time

A match from a proposition into a non-Prop motive is accepted when either:

- no constructor is reachable at the scrutinee type; or
- the family carries a `Reconstruct` certificate.

Reachability may use checker unification to establish impossible indexed cases and refine branch
types. That is separate from runtime representation and never upgrades an `Erase` family.

A Prop-valued motive is ordinary small elimination and remains available for every proposition.

### 7.2 Evaluation

Evaluation sees canonical values:

- a reconstructed `VCtor` selects its ordinary constructor branch;
- a non-reconstructible `VProof` immediately produces a canonical proof for a Prop-valued result,
  and leaves a data-valued match stuck;
- binding a stored proof field at a branch boundary canonicalizes one exposed layer.

For example:

```raccoon
axiom zeroEq : Eq(Nat, Nat.zero, Nat.zero)
axiom natIsBool : Eq(Type, Nat, Bool)

def diagonal : Bool :=
  Eq.subst(zeroEq, Level.one, fun (_ : Nat): Type => Bool, Bool.true)

def impossibleCast : Bool :=
  Eq.subst(natIsBool, Level.one, fun (A : Type): Type => A, Nat.zero)
```

`diagonal` reduces to `Bool.true`, because `zeroEq` canonicalizes to `Eq.refl(Nat.zero)`.
`impossibleCast` stays stuck, because the type cannot reconstruct `refl`.

No interpreter path invokes `tryUnify`.

## 8. Interaction with recursion and polymorphism

Structural and measure recursion still reject proof-valued metrics. Canonical constructor form is
not termination evidence, and proof constructor structure never participates in the strict
subterm relation.

The canonical eta-lambda is particularly important for the Abel–Coquand loop: after its source
body is checked, applications compute only the instantiated proposition and its canonical proof.
They never re-enter the discarded self-referential proof computation.

For a `Sort u` family, the declaration certificate is universe-independent and conservative. At a
non-Prop instance it has no effect. Once an instance is known to live in `Prop`, exact-type
canonicalization applies uniformly to constructors, neutrals, axioms, and functions. Generic code
does not gain a runtime unification rule after level substitution.

Generated K6 Prop induction principles are bodiless proofs of Pi propositions. Publication turns
them into canonical eta-lambdas; applying one produces the canonical proof of its instantiated
conclusion without executing proof recursion.

## 9. Consequences

- An explicit `Eq.refl` and an axiom at the same diagonal equality have the same `VCtor` form.
- Equality elimination computes on both diagonal values and stays stuck on non-diagonal axioms.
- Proof functions have one type-directed `VLam` form and never execute their checked source bodies.
- `And`, `True`, `Eq`, and directly indexed one-constructor propositions reconstruct constructors.
- `Exists`, `Nonempty`, `Or`, and similar propositions retain no constructor data.
- A Prop-level `Quot` instance erases its representative, so data-valued `Quot.lift` remains stuck;
  this is a known completeness question for the Mathlib port.
- Proof irrelevance remains definitional for every representation.
- The evaluator performs only recorded reconstruction and conversion checks, never unification.

The implementation is pinned by `ProofCollapseTests`, the Prop large-elimination tests, the
constructor-apartness consistency probes, the Abel–Coquand regression, and the full kernel suite.

## 10. Possible extensions

These are deliberately not part of the current rule.

### 10.1 Pairwise overlap analysis

A more permissive declaration-time certificate could use this rule:

> For every pair of constructor instances whose result types can coincide, the constructors have
> the same identity and every non-Prop field is forced equal by the common result type.

This could support injectively nested indices such as
`Wrapped.intro n : Wrapped (Nat.succ n)` and disjoint indexed constructors such as
`zeroCase : Shape zero` / `succCase n : Shape (succ n)`. It would still produce a finite recorded
recipe and would not restore interpreter-time unification.

Mathlib has proposition shapes where this could shorten Raccoon-side bridges, including indexed
relations such as `List.IsChain` and `Sum.LiftRel`. It is not required for faithful translation:
Lean does not grant general Sort elimination to arbitrary multi-constructor propositions.

The cost is a substantially more complex trusted certificate: declaration checking must compare
fresh constructor pairs, distinguish apart from stuck failures, prove field correspondence, handle
mutual blocks, and preserve the result through universe substitution.

### 10.2 Partial data-field erasure

Another extension would introduce a typed `Erased(T)` field value. A one-constructor proposition
could then retain its constructor and forced fields while replacing only unforced data fields.
That could permit constant data eliminations that do not inspect those fields, but still could not
extract an `Exists` or `Nonempty` witness.

Soundness requires an explicit relevance discipline: branch checking must prevent erased fields
from flowing into data results; dependent later field types must remain meaningful; and quotation,
materialization, projections, native values, and unification must all understand field relevance.
The expected program payoff is modest, so this should be designed as a general relevance system
rather than a local evaluator exception.

## 11. Non-negotiable invariants for extensions

Any future relaxation must preserve all of the following:

1. Reconstruction decisions and recipes are produced at inductive checking time.
2. The evaluator never invokes unification or searches for proof constructors.
3. A proof's canonical outer representation depends only on its exact proposition.
4. Proof constructor structure never provides apartness, injectivity, or termination evidence.
5. Proof irrelevance never manufactures source obligations; `proof(P)` is residual-only.
6. Recursive proof fields are exposed finitely rather than expanded into infinite values.
7. Generic-universe code cannot gain unchecked proof-driven data reduction at `u := 0`.
