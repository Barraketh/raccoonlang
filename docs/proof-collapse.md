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

This is canonicalization, not proof search. The inductive checker compiles a finite recovery plan
into family metadata. Runtime interprets the requested field slice and, for constructor
reconstruction, validates the result; it never runs unification, searches constructors, or solves
indices.

The same metadata governs the smaller question of which individual fields may be recovered from a
proof. The unifying principle is:

> Information escapes a proof exactly when it is a function of the exact proposition; the proof
> value is never consulted.

## 2. Declaration-time recovery plans

The relevant metadata is:

```scala
sealed trait ProofFieldSource
object ProofFieldSource {
  final case class ResultArgument(index: Int) extends ProofFieldSource
  case object Unavailable extends ProofFieldSource
}

final class ProofRecoveryInfo(
  fieldSources: Vector[ProofFieldSource],
  projectionInfo: ProjectionInfo,
  definitelyComplete: Boolean
)
```

An optional `ProofRecoveryInfo` is recorded exactly when:

1. the family's declared result universe may reduce to `Prop` (its level is not provably positive);
2. the family has one constructor.

Every stored field gets `ResultArgument(index)` when the field itself occurs directly in the
constructor's result-family application, and `Unavailable` otherwise. Proposition fields do not
need a stored source: recovery evaluates the instantiated field type and produces a shallow
`VProof` whenever that actual type lives in `Prop`. This instance-sensitive classification is
load-bearing for a declaration in `Sort(u)` instantiated at `u := 0`.

Leading family parameters are not stored fields. A fixed positive-universe family can never have a
Prop instance, so it retains no dead recovery plan. `definitelyComplete` is only a performance hint:
it records that declaration-time classification already proves every field recoverable and keeps
repeated canonicalization of certified constructor proofs constant-time. It never changes which
fields recovery accepts at an actual instance.

`ProjectionInfo.fieldDependencies(i)` stores the precise syntactic transitive set of preceding
fields needed to form field `i`'s type. The constructor result is deliberately absent: an occurrence
there does not make an independent later field harder to type.

This is intentionally the simple singleton rule:

| Family shape | Recovery   | Reason |
|---|------------|---|
| `Eq.refl (x : A) : Eq A x x` | complete   | `x` is a direct result argument |
| `True.intro : True` | complete   | no fields |
| `And.intro (p : P) (q : Q)` | complete   | both instantiated fields are proofs |
| `Idx.intro (y : A) : Idx y` | complete   | `y` is a direct result argument |
| `HasProof.intro (w : A) (h : True)` | partial    | `h` is recoverable; hidden `w` is not |
| `Exists.intro (w : A) (h : P w)` | incomplete | `w` is hidden and needed to form `h`'s type |
| `Nonempty.intro (w : A)` | incomplete | the witness is not a function of the proposition |
| `Or.inl` / `Or.inr` | no plan    | more than one constructor |
| `Wrapped.intro (n : Nat) : Wrapped (succ n)` | incomplete | `n` occurs only under `succ` |

Empty propositions have no one-constructor plan; empty large elimination is justified separately
by reachability.

## 3. Field recovery and exact reconstruction

`ProofReconstruction` interprets a recovery plan only when the major family instance is known to
live in `Prop`. Ordinary data projections continue to inspect their major value.

For each requested field, left to right:

1. Recover its precise preceding type dependencies.
2. Evaluate its field type at the actual family instance.
3. If that type is a proposition, construct a shallow `VProof`.
4. Otherwise copy its `ResultArgument`, checking that argument against the instantiated field type;
   `Unavailable` fails.

The proof value is never read. Recovery has three consumers:

| Consumer | Required fields | Constructor-result check |
|---|---|---|
| Prop projection | selected field and its type dependencies | no |
| large-elimination eligibility | every field | no |
| canonical `VCtor` reconstruction | every field | yes |

Match reduction is not a fourth recovery mode: it occurs only on the canonical `VCtor` produced by
the last row. A `VProof` whose recovered fields fail the constructor-result comparison remains stuck
under a data-valued match. This separation is load-bearing for subject reduction at constrained
instances.

`recoverField(P, i)` deliberately does not validate the full constructor result. A recovered data
field is an argument already present in `P`; repeated or constrained occurrences choose the first
recorded direct result position deterministically. This is a choice of path, not evidence that the
constructor result equals `P`.

`reconstruct(P)` additionally recovers every field and checks that the instantiated constructor
result is definitionally equal to exact proposition `P`. There is no fallback search.

For `Eq.refl`, the plan copies the first endpoint into the stored `x` field. Instantiating its
result gives `Eq(A, x, x)`. Thus:

```text
reconstruct(Eq(Nat, zero, zero)) = Eq.refl(zero)
reconstruct(Eq(Type, Nat, Bool)) = failure
```

Repeated or constant indices are therefore constraints on canonical constructor reconstruction,
checked by ordinary conversion rather than runtime unification.

Proof fields are deliberately shallow. For a recursive proposition such as:

```raccoon
inductive Loop : Prop
  | mk (next : Loop) : Loop
```

canonicalizing a `Loop` produces one `Loop.mk(VProof(Loop))` layer. Binding `next` in a match
canonicalizes that exposed field and produces the next layer. This permits any finite observation
without constructing an infinite value eagerly.

The plan's constructor head is temporarily unavailable while that constructor is itself being
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
- every constructor field is recoverable at the actual Prop instance.

Reachability may use checker unification to establish impossible indexed cases and refine branch
types. Recovery eligibility does not validate the constructor result: a constrained instance may
therefore check while its evaluation remains stuck. Instance-sensitive proof classification also
means a `Sort(u)` singleton whose fields become proofs at `u := 0` may large-eliminate at that Prop
instance even when those fields were not known proofs at declaration.

A Prop-valued motive is ordinary small elimination and remains available for every proposition.

### 7.2 Evaluation

Evaluation sees canonical values:

- a result-validated reconstructed `VCtor` selects its ordinary constructor branch;
- a non-reconstructible `VProof` immediately produces a canonical proof for a Prop-valued result,
  and leaves a data-valued match stuck, blocked on the proposition's syntactic dependencies;
- binding a stored proof field at a branch boundary canonicalizes one exposed layer.

When materialization sees a store that solves any recorded dependency, it re-evaluates the stuck
match. Reduction still occurs only if result-validated reconstruction now produces a `VCtor`; a
failed result equation simply re-sticks the match with its remaining dependencies. This wakeup is
reduction, not a new proof-recovery rule, and invokes no unification.

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

For a `Sort u` family, result-argument sources and syntactic dependencies are universe-independent.
At a non-Prop instance the recovery plan has no effect. Once an instance is known to live in `Prop`,
field propness is classified at that instance, so a generic checked projection continues to work
when its field becomes a proof at `u := 0`. Canonicalization still applies uniformly to constructors,
neutrals, axioms, and functions, and no level substitution introduces runtime unification.

Generated K6 Prop induction principles are bodiless proofs of Pi propositions. Publication turns
them into canonical eta-lambdas; applying one produces the canonical proof of its instantiated
conclusion without executing proof recursion.

## 9. Consequences

- An explicit `Eq.refl` and an axiom at the same diagonal equality have the same `VCtor` form.
- Equality elimination computes on both diagonal values and stays stuck on non-diagonal axioms.
- Proof functions have one type-directed `VLam` form and never execute their checked source bodies.
- `And`, `True`, `Eq`, and directly indexed one-constructor propositions reconstruct constructors.
- A projection may recover a forced data field or an independent proof field even when the whole
  constructor is not reconstructible; large match elimination still requires every field.
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

1. Data sources and precise field dependencies are produced at inductive checking time.
2. The evaluator never invokes unification or searches for proof constructors.
3. A proof's canonical outer representation depends only on its exact proposition.
4. Proof constructor structure never provides apartness, injectivity, or termination evidence.
5. Proof irrelevance never manufactures source obligations; `proof(P)` is residual-only.
6. Recursive proof fields are exposed finitely rather than expanded into infinite values.
7. Generic-universe code cannot gain unchecked proof-driven data reduction at `u := 0`.
8. Only full recovery plus the exact constructor-result check may manufacture a branch-firing `VCtor`.
