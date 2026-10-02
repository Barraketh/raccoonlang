# Nominal Type families

Status: **implemented** (2026-10-01); [kernel rules](../kernel.md#nominal-type-families) and the
[reviewed informal model](../nominal-model.md) are authoritative. Second of three specs, after `docs/proposals/PROP_SEPARATION.md` (which it assumes:
every family is declared either in `Prop` or in a `Type`) and before `docs/proposals/REFINEMENT_CERTIFICATES.md` (which uses the
principles stated here).

Before this change, match refinement treated every inductive family head as injective: from `w : W(List(y))`, where `W`'s only
constructor is at `W(List(Nat))`, it concludes `y = Nat`, and from `Eq(Type, I(F), I(G))` it concludes `F = G`. No
eliminator justifies either step, and the second, for `I (F: Type -> Type) : Type`, is Hur's injective-type-constructor
principle, which is inconsistent with excluded middle (Agda issue 292). `ConsistencyTests` now refuses the small declaration and checks injectivity for its level-one replacement.

This document makes injectivity a stated principle of the kernel, adds generativity beside it, and restores
consistency with a size rule on family arguments.

## 1. The principles

For **`Type` families** (declared in a `Type`, not in `Prop`), with `F` and `G` inductive family heads:

- **N1, injectivity.** `F(ā) = F(b̄)` implies `ā = b̄`: the parameters and indices, as one dependent tuple.
- **N2, generativity.** `F(ā) = G(b̄)` implies `False` when `F` and `G` are different heads.
- **N3, distinct forms.** An instance of a `Type` family, a Type-valued function type and a universe `Type { … }` are pairwise
  unequal. Universe conversion requires equal level, kind and scope; failures of those comparisons stay stuck.

Their scope is exact:

- **Inductive heads only.** Nothing is claimed about an axiom of type `Type`, or a type-level
  application that is stuck: `axiom T : Type` may be `Nat`. A type that evaluates to a family instance is compared by
  its head after evaluation, as conversion already does.
- **Not `Prop` families.** A `Prop` family head is neither injective nor generative. Refinement decomposes it only at the
  root of the scrutinee's own type, where the eliminator justifies it (`docs/proposals/REFINEMENT_CERTIFICATES.md` §2). Two
  reasons, the first sufficient on its own:
  - With an impredicative `Prop` and proof irrelevance, a proposition carries no more than a truth value. So an
    injective `Prop` family is an injection of a large type into a tiny one. Miquel's observation, reported by Hur on
    the Agda list in 2010 and recalled by Pujet, Tabareau et al. ("Observational Equality Meets CIC", TOPLAS 2025,
    §2.3), is that this gives Russell's paradox with no axioms.
    - **Before this change**, Raccoon decomposed `Eq` nested in an index and admitted a complete `False` proof:
      `i(F) := Eq((x: Prop) -> Prop, F, F)` was injective, and `R(x) := ∃F. x = i(F) ∧ ¬F(x)` gave
      `R(i(R)) ↔ ¬R(i(R))`. The permanent Russell regression now rejects the initial injection with `TypeMismatch`.
    - **The same construction works through a `Type` family** that fails the size rule of §2:
      `I (F: (X: Type) -> Prop) : Type`. `NominalFamiliesTest` refuses that small declaration.
  - Propositions are extensional: with propositional extensionality, `And(T, T) = Or(T, T)`.
- **Sealed families** are families like any other.

Together, N1–N3 say `Type` families are *nominal*: a family instance is determined by its head and its arguments, as a
datatype declaration is in ML, Haskell or Rust. This rules out, for good, identifying two declarations with the same
constructors, structural record types that identify across declarations, and univalence. Raccoon already excludes
univalence: `Eq` is in `Prop` with definitional proof irrelevance, which gives uniqueness of identity proofs.

## 2. The size rule

N1 lets a type determine its arguments, so a type must be able to *contain* them. The following sufficient restriction makes nominal labels fit the
family's universe; conservative rejection does not assert that every rejected declaration is individually inconsistent. Hur's argument, for `I (F: Type -> Type) : Type` with N1:
1. with excluded middle, define `J(X)`, the unique `F` with `I(F) = X` if there is one;
2. let `D(X) := J(X)(X) -> Empty` and `X0 := I(D)`;
3. N1 gives `J(X0) = D`, so `D(X0) = (D(X0) -> Empty)`, and `False` follows.

Fields already obey a size rule: a field's *type* must be in the family's universe, since the family's values contain
all of its values. An argument is different: a type contains *one* argument value, so what must fit is each *value*.
Hence:

**Every parameter and index type of a `Type` family at level `ℓ` must be small at `ℓ`**, where:

| Argument type `T` | small at `ℓ` when |
|---|---|
| a universe `Type { level = m, … }` | `m ≤ ℓ`: a type is an element of its universe |
| `Prop`, or a proposition | always: a proposition, or any proof, fits anywhere |
| a Type-valued function type `(x: A) -> B` | `A`'s ordinary classifier level is `≤ ℓ` (the full domain fits), and `B` is small at `ℓ` (each result fits) |
| anything else | its ordinary classifier level is `≤ ℓ` |

A universe `Type_m` costs `m` as an argument's type or in codomain position; in domain position it costs its
ordinary classifier level `succ(m)`. Kernel annotation parameters are exempt.
That is the polarity condition of strict positivity, one level up: positivity keeps a type from containing functions
out of itself, and this keeps a type from containing functions out of its universe. Both block a diagonal argument.

| Family | Small? |
|---|---|
| `List (A: Type) : Type` | yes |
| `Sigma (A: Type)(B: A -> Type) : Type` | yes: domain `A` fits, codomain is the universe |
| `Subtype (A: Type)(p: A -> Prop) : Type` | yes |
| `Quot (A: Type)(r: A -> A -> Prop) : Type` | yes |
| `I (F: Type -> Type) : Type` | no: the domain `Type` is at level one. Declare it at `Type { level = one }` |
| `Indexed (A: Type) indices (F: Type -> A) : Type { level = one }` | yes (already at level one) |

A family that fails is refused, with the diagnostic `FamilyArgumentTooLarge(family, argument, level)`, whose message
names the level to declare. `Prop` families need no size rule: they are not injective.

**Prior art.**
- **Pitts and Abel (2010).** Andrew Pitts proposed restricting injectivity by size on the Agda list: "allowing Set to
  contain a (Set → Set)-indexed family of mutually distinct names for the empty set seems dangerous because Set is 'too
  small'; whereas allowing it in Set1 seems uncontentious". Andreas Abel likened the check to positivity.
- **Agda today.** Agda requires the types of indices to fit the datatype's sort under `--without-K`
  (`--no-large-indices`, the default).
- **Pujet, Tabareau et al. (TOPLAS 2025, §2.3)** consider allowing inductive definitions only "in a universe that is
  sufficiently large to accommodate their parameters". They reject it because Coq's sections turn section variables
  into parameters.
- **What is new here.** That coarse form counts an argument by its type's level, which would move `List (A: Type)` up a
  universe. The elementwise rule above does not: a universe as an argument's type, or in codomain position, pays its
  level rather than its successor. Only quantification over a universe in domain position does, which is rare in parameters. Raccoon has no
  sections.

**Cost.** None of the 191 family declarations in the preludes, the GPU library or the test `.rac` files fails.
Among existing families written in Scala test strings, four need migration: the ConsistencyTests injectivity probe (which becomes a test
that the declaration is refused, and that at `Type { level = one }` the injectivity holds) and one positivity-metadata
test (`Higher (F: Type -> Type) : Type` in `InductiveCheckTest`), which moves to level one, plus
`Wrap(p: Pack)` and `UsesF(F: CoupleU(Type, Type))` in projection tests. Their containing declarations are
raised where required by the unchanged field bound; their coverage is retained.

## 3. Why the principles are consistent

The detailed [informal relative-consistency construction](../nominal-model.md) was reviewed independently before
implementation. It distinguishes the elementwise nominal-label bound from extension smallness. Small erased
majorants bound actual payloads; monotone guards retain dependent typing and independent erased Prop witnesses.
Joint guarded least fixed points handle indexed, nested and mixed Prop–Type mutual families. Recursive values
carry external typing rather than their complete family type annotations.

The construction supports N1–N3, impredicative Prop, recovery-based large elimination, quotients, propositional
extensionality, structure eta and annotation/universe polymorphism. It models the stated calculus relative to
inaccessible cardinals and a consistent trusted prelude. It is not a machine-checked implementation theorem:
the existing finite-hash equality shortcut and coverage/refinement implementation remain separate boundaries.

## 4. What changes in the kernel

- **Declaration.** The size rule of §2, a traversal of each parameter and index type beside positivity in `InductiveChecks`, under a freshly evaluated dependent telescope.
- **Refinement.**
  - Decomposing a `Type`-family head is justified by N1 at any depth. This behavior is now
    stated and bounded by §2.
  - A `Prop`-family head decomposes only at the root of the scrutinee type. That needs a root-versus-nested marker on
    the unifier's context: the explicit `tryUnifyMatchTypes` entry point clears this permission on every structural descent.
  - Two different `Type`-family heads, or two different forms (N3), are **apart**. Such a clash was previously stuck.
- **Heterogeneous equations.** With N2 and N3, an equation between types that clashes at the head is refuted, so a
  telescope of index equations whose later equations depend on an earlier type equation (the `Tag(A: Type)(a: A)` shape)
  resolves at that type equation. Value clashes across families (`Bool.true` against `Two.one`) stay stuck, as since
  `921fa3f`: the refutation, when there is one, comes from the type equation before them.
- **Documentation.** `docs/kernel.md` gets a section "Nominal families" stating N1–N3, their scope and the size rule,
  beside quotient soundness as the kernel's stated principles. "Apartness" and "Refinement unification" cite it.

`docs/proposals/REFINEMENT_CERTIFICATES.md` then turns these from unifier behaviour into principles a proof term may use: its
exclusion certificates invoke narrowly trusted private N1–N3 theorem premises with independently checked signatures
and typed family/form assumptions. Constructor pruning now requires an ordinary checked refutation; successful
unifier links and their classification remain unchanged and trusted. No link certificates are implemented.

## 5. Tests

- `I (F: Type -> Type) : Type` is `FamilyArgumentTooLarge`; at `Type { level = one }` it is accepted and `injI` checks.
- `List`, `Sigma`, `Subtype`, `Quot` and the GPU library's families are accepted unchanged.
- `W(List(y))` refines to `y = Nat` (N1).
- A match on `Tag(Two, Two.one, …)` with only `mk : Tag(Bool, Bool.true, …)` prunes `mk` (N2 on `Two` against `Bool`).
  The empty match now checks; writing the excluded `mk` branch produces `UnreachableCase`.
- `Nat` against `Nat -> Nat`, and `Type` against a family declared at level one in an index, are apart (N3).
- A `Prop`-family head nested in an index does not decompose: `Eq(Prop, And(P, Q), And(R, S))` gives no link
  `P := R`.
- An axiom type does not decompose or clash: `axiom T : Type` against `Nat` is stuck.
- The existing soundness regressions stay green.

## 6. Steps

1. **N0, the model argument**, written out in full as `docs/kernel.md`'s justification of N1–N3, then given an
   adversarial theory review of its own. The review must check the model against every feature at once:
   - impredicative `Prop` and its large elimination;
   - quotients;
   - propositional extensionality (planned);
   - struct eta, and proof irrelevance in conversion;
   - value keys (conversion must never identify two types with different codes);
   - kinds, lifetimes and sealing;
   - universe polymorphism.
2. **N1, the size rule** at declaration, with its diagnostic and tests.
3. **N2, refinement:**
   - `Prop`-family heads decompose only at the root;
   - `Type`-family and form clashes are apart;
   - `kernel.md`.

N1 and N2 come after `PROP_SEPARATION` step P1. All three are trusted-core changes: implementers at medium effort, the
N0 review and the hostile code reviews at high.

## 7. Decisions for review

1. **Generativity (N2)** adopted with injectivity, as one "nominal families" principle.
2. **Distinct forms (N3)** included: family instances, function types and universes are pairwise unequal.
3. **A failing family is refused**, not accepted as a non-injective family. Every `Type` family is then nominal,
   uniformly.
