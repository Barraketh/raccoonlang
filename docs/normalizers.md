# Normalizers in Raccoon

This document describes the **normalizers** feature in Raccoon: what problem it solves, how it appears in the language, and how it is implemented in the current codebase.

## What a normalizer is

A normalizer is a first-class value of type `Normalizer` that can be brought into scope inside a function body with a `use` statement.

Its purpose is to extend **definitional equality** in a controlled, local way. In ordinary dependent type theory, some equalities are computational and others require explicit proof terms. In Raccoon, a normalizer can make additional equalities computational for a particular carrier type.

The current implementation is deliberately narrow and explicit:

- a normalizer is an actual runtime value, not a magical global rule
- it is activated only in a lexical scope via `use`
- it is selected by the carrier type of the values being compared
- it participates only in equality checking and unification

In other words, normalizers are **scoped extensions to conversion**, not unrestricted rewrite hints.

## Surface model

The user-facing pieces are:

- the builtin type `Normalizer`
- the builtin constructor-like function `add_normalizer`
- the `use` statement inside a body block

Example:

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

stable def add (a: Nat)(b: Nat): Nat := {
  match b as _ returning Nat with
  | Nat.zero => a
  | Nat.succ x => add (Nat.succ a) x
}

inline def nat_add_normalizer : Normalizer := add_normalizer Nat Nat.zero add

inductive Eq (A: Type) indices (x: A) (y: A) : Sort Level.one
 | refl (x: A) : Eq A x x

inline def addComm (a: Nat)(b: Nat): Eq Nat (add a b) (add b a) := {
  use nat_add_normalizer
  Eq.refl Nat (add a b)
}
```

Without the `use nat_add_normalizer`, the same definition fails to typecheck. With it, the equality is treated as computational in that scope.

## What problem this solves

The feature is aimed at equalities that are mathematically simple but not definitionally equal under the language's ordinary evaluator.

For example, with a recursive definition of addition on `Nat`:

- `add a Nat.zero = a` may reduce directly, depending on the form of `a`
- `add Nat.zero a = a` usually does **not** reduce definitionally
- `add a b = add b a` certainly does not reduce definitionally
- `add x (add y z) = add (add x y) z` also does not reduce definitionally

The additive normalizer can make these equal by normalizing both sides into a canonical additive form before comparison.

This is especially relevant in a system that wants to keep the kernel small and explicit while still allowing selected domains to enjoy richer computational behavior.

## Current syntax and scope rules

A `use` statement appears only inside a body block:

```raccoon
{
  use some_normalizer
  let x := ...
  ...
}
```

In the current parser and AST, a body consists of:

- zero or more `use` statements
- zero or more `let` bindings
- a final result term

So normalizers are attached to a body scope, not to an entire file or module.

## The semantic model

At the value level, `Normalizer` is a top-level value type, and each normalizer provides three things:

- a `name`
- a `carrierKey`
- a `normalize(v, eqStore)` function

Conceptually, the `carrierKey` says **what type of values this normalizer applies to**. The `normalize` function maps values of that carrier into a more canonical form for comparison.

## How normalizers are selected

Normalizers are stored in a `NormalizerMap`, keyed by carrier.

Today the carrier key is intentionally simple. It is extracted from the type of the value being compared, and it is recognized only for a few shapes:

- a constant type head like `Nat`
- an application whose head is a constant
- a type variable

So the current system is set up for carrier-indexed normalization rather than arbitrary rewrite databases.

When the typechecker compares two values `v1` and `v2`, it:

1. looks at `v1.tpe` and `v2.tpe`
2. extracts carrier keys from those types
3. if the keys are equal and a normalizer is in scope for that key, applies that normalizer to both sides
4. then runs ordinary definitional equality on the normalized results

The same mechanism is also used by unification.

This detail matters: normalizers are not applied because a term syntactically contains `add`; they are applied because the **values being compared live in a carrier type whose normalizer is active**.

## Where they participate in the implementation

In the current codebase, normalizers affect two places:

- `TypeChecker.defEq`
- `Unify.unify`

Both paths first choose a normalizer function with `TypeChecker.getNormalizerF`, then normalize each side, then continue with the usual comparison or unification logic.

That means the feature is part of the trusted equality/conversion path, not merely an elaborator convenience.

## The builtin additive normalizer

The only builtin normalizer today is `add_normalizer`, introduced in the initial environment as:

```raccoon
(A: Type)(zero: A)(add: A -> A -> A): Normalizer
```

Given a carrier type `A`, a distinguished zero element, and a binary addition-like function, it constructs a normalizer for that carrier.

### What it does

The implementation treats `add` as defining a commutative monoid-style normalization scheme.

For a value `v`, it:

1. recursively flattens nested applications of `add`
2. removes occurrences of `zero`
3. sorts the remaining summands into a canonical order
4. rebuilds the term by folding `add` back over the sorted list
5. returns `zero` if the list is empty, or the single element if only one term remains

So expressions such as these normalize to the same form:

- `add a b`
- `add b a`
- `add a (add b Nat.zero)`
- `add (add a b) Nat.zero`

and similarly for associativity and identity.

### Why stable definitions matter

In the examples, addition is defined with `stable def add ...` rather than `inline def`.

This relates to how evaluation preserves a stable head for blocked applications. The implementation explicitly notes that this behavior exists so normalizers can still recognize and rewrite expressions even when unfolding does not fully complete. Roughly speaking, if a function is marked stable, blocked computations can still retain the original function head instead of disappearing behind intermediate unfolding.

That is an implementation choice made partly in service of normalizer-based rewriting.

## What the tests demonstrate

The strongest behavioral summary comes from the tests.

With the additive normalizer in scope, all of the following typecheck using `Eq.refl` alone:

- right identity of addition
- left identity of addition
- commutativity of addition
- associativity of addition

Without the normalizer, the commutativity proof and left-identity proof are explicitly expected to fail.

That is exactly the intended contract of the feature: a chosen equality theory can be made computational in a local scope, but it is not silently built into the language everywhere.

## What normalizers are not

A few boundaries are important.

### They are not global

Normalizers must be brought into scope with `use`. There is no ambient global rewrite table.

### They are not arbitrary theorem automation

A normalizer does not search for proofs. It computes a canonical form and then relies on ordinary definitional equality.

### They are not currently compositional in a rich way

`NormalizerMap.use` rejects multiple normalizers for the same carrier. So today there is at most one active normalizer per carrier type in a scope.

### They are not arbitrary term-indexed rewrites

Selection is by carrier type, not by scanning terms for all possible patterns.

## Design implications

This feature is interesting because it sits between two familiar extremes:

- a tiny kernel with only builtin conversion
- a large proof-automation layer with external rewriting tactics

Raccoon instead gives you a small, explicit hook into conversion itself.

That has several attractive properties:

- the extension point is visible in the term language
- the scope is lexical and easy to audit
- the mechanism is simple enough to test directly
- domain-specific equalities can become computational without turning the whole language into a tactic-driven system

For work in theorem verification or verified code generation, this is potentially useful because many important equalities are algebraic or structural and benefit from canonicalization.

## Current limitations

The current implementation is intentionally minimal.

- Only one builtin normalizer is present: `add_normalizer`.
- Carrier selection is coarse and based on the compared values' types.
- The additive normalizer assumes a commutative-and-associative-with-identity style interpretation; it is not separately parameterized by proofs of those laws.
- There is no general framework yet for combining multiple normalizers on the same carrier.
- There is no separate metatheory document yet describing what conditions a user-defined normalizer would need to satisfy for the overall equality theory to remain well-behaved.