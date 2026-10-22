# Type programs: values that do not compute their types

> **Historical proposal.** This document predates removal of Raccoon's
> `Lifetime` and sort-scope feature. Any lifetime or scope forms mentioned in
> the proposal are unsupported and do not describe current semantics. See the
> [language reference](../language.md) and [kernel reference](../kernel.md).
> The pre-removal source is retained at revision `4af124c4`; view it with
> `git show 4af124c4:docs/proposals/TYPE_PROGRAMS.md`.

Status: proposal, 2026-10-05. Not implemented.

Scope: type-checking speed. This proposal builds on
[INTERNED_WORDS_AND_BYTECODE.md](INTERNED_WORDS_AND_BYTECODE.md), whose Part 3
compiles each function to a body program and a type program. It does not change
definitional equality, any key's equality classes, or any output.

## Purpose

Every value carries an evaluated type today, and computing that type is work
done whether or not anything reads it:

- **Constructor applications** compute their result type
  (`VPi.constructorResultType`). For a parameterized family, a miss in the
  four-entry per-`VPi` cache evaluates the codomain and allocates a fresh type
  value, such as `List(A)`.
- **Stuck applications** evaluate their head's codomain when built
  (`CoreEvaluator.applyFunction`, `residualRecursiveApplication`).
- **Stuck matches** evaluate their motive when built
  (`Interpreter.evalTerm(matching.term.motive, env)` in the run loop).
- **Every binding** asks `Sorts.isProposition(value.tpe)` to canonicalize
  proofs, and 11 other sites ask the same question.
- **Dependencies** include the type's (`VApp.synDeps` unions in `tpe.synDeps`),
  and **keys** mix the type in (`ValueKey.application(head, args, tpe)`).

The kernel reads `.tpe` in 277 places. Most of the types it computes are never
read.

Principle: **a value stores what determines its type, never the type itself.**
Each function is two programs. Its **body program** computes values. Its **type
program**, the Pi's codomain, computes result types. Evaluation runs body
programs only. Checking runs a type program when it needs a type, and a body
program when a type mentions a computation. A type is computed on first demand
and memoized.

## Terms

- **Type program**: compiled code that computes a type from the values that
  determine it. Three kinds:
  - a Pi's codomain, from the arguments;
  - a match's motive, from its environment and scrutinee;
  - an indexed family constructor's index code, from its fields.
- **Determinants**: the stored data from which a value's type follows.
- **Family instance**: a family head together with its parameter values, the
  constructor's leading `numErasedFamilyArgs` arguments. It is interned when
  closed (INTERNED_WORDS Part 1). For a family without indices, the instance
  determines the type. For an indexed family, the type also needs the indices,
  which the constructor's index code computes from the fields.
- **Class bits**: a few bits per value, recording whether its type is a
  proposition and whether it is an eta-eligible structure. They are computed
  from static information, never from the value's type.
- **`typeOf(v)`**: runs `v`'s type program on its determinants and memoizes the
  result.

## 1. What each value stores

| Value | Stores | `typeOf` runs |
|---|---|---|
| constructor application | head, family instance, stored fields | the index code (none for a family without indices) |
| word (INTERNED_WORDS Part 2) | layout, which names the instance, and bits | nothing: the layout's instance |
| packed value, context value | codec, instance | nothing |
| stuck application | head, arguments | the head type's codomain over the arguments |
| stuck match | term, environment, scrutinee, as today | the motive |
| lambda | its `VPi`, as today | nothing |
| variable | its binder's type, as today | nothing |
| proof (`VProof`), deferred evidence | its proposition, as today; the proposition is the proof's content | nothing |
| Pi, sort, level, kind, lifetime | as today | its sort |

Constructor applications today store their fields and their evaluated type, but
not their parameters. They now store the interned instance in place of the
type, so a value has the same number of references.

## 2. Static facts instead of runtime type tests

- **Proofs in slots.** Whether a slot holds a proof follows from its binder's
  checked type, which is known when the code is compiled. Proof
  canonicalization at a binding reads that fact instead of the value's type.
- **Class bits.** They are computed at construction from information that
  needs no type program. Since `01f9817` separated `Prop` from the data
  universes, whether a type is a proposition is fixed when it is formed, so:
  - for a constructor application, the family's declared sort (`Prop` or a
    `Type`), the same for every instance;
  - for an application, the Pi's prop-valuedness (`VPi.isPropValued`);
  - for a stuck match, its motive's sort.
- **The 11 `isProposition(….tpe)` sites** read class bits instead.
- **Eta eligibility** follows from the family head.
- **Validated native operations** are already identified by their published
  lambdas, so their capability checks need no value type.

A canonical proof still computes its proposition, because canonical proof
representation chooses its form from that proposition (kernel.md, "Proofs and
elimination"). The laziness applies to data.

## 3. Dependencies and keys

Every type is a function of its value's determinants, so:

- **Dependencies** are computed from the determinants: head, instance,
  arguments and environment. They equal today's, because the type's
  dependencies are contained in the determinants'.
  - For a constructor application, the indices come from the fields.
  - For a stuck application, the head's type is covered by the head's own
    dependencies. Inductively, a variable's dependencies include its type's.
- **Keys** mix the determinants instead of the evaluated type:
  - `(head, instance, determining fields)` for a constructor application;
  - `(head, arguments)` for a stuck application.

  Values with equal determinants have equal types, so the key equality classes
  do not change. `nil@Nat` and `nil@Bool` still differ, now by instance.

## 4. Conversion

Conversion keeps its current untyped structure. Each place that reads a value's
type either reads a determinant or calls `typeOf`, and only where the type is
really needed:

- **Proof irrelevance.** Class bits decide that both sides are proofs. Their
  propositions are then compared: stored in a `VProof`, or `typeOf` of a
  canonical constructor proof.
- **Constructor applications** compare instances instead of full types. Equal
  heads, equal instances and equal fields give equal indices, so equal types.
- **Variable linking** keeps its cheap check, then calls `typeOf(other)` only
  when that check does not settle it.
- **Stuck matches** with the same match term and convertible environments have
  equal motives, so equal types. Otherwise `typeOf` runs both motives.
- **Lambdas** compare their stored `VPi`s, as today.

Making conversion type-directed would avoid even these `typeOf` calls. It is a
possible later optimization, not a prerequisite.

## 5. Interaction with INTERNED_WORDS

- **Part 1** interns closed family instances, so storing an instance is a table
  lookup. No codomain is evaluated and no type value is allocated.
- **Part 2**'s layout id is the instance. A word's type needs no program.
- **Part 3** compiles each function's type program, each match's motive and
  each constructor's index code as separate `Code`. The body path never runs
  them. `typeOf` runs them through the same VM.

## Stages

Each stage keeps outputs byte-identical.

1. Add `typeOf` beside the eager `tpe`, and an assertion mode checking
   `typeOf(v) ≡ v.tpe` for every value built.
2. Add class bits and static proof facts. Move the 11 `isProposition` sites and
   proof canonicalization onto them, and assert agreement with
   `isProposition(v.tpe)`.
3. Compute dependencies and keys from determinants. Assert equal dependencies,
   and assert that key equality agrees with the old keys on every compared pair.
4. Move conversion's type reads onto determinants and `typeOf`.
5. Audit the remaining `.tpe` readers. Each becomes a determinant read or
   `typeOf`.
6. Make `tpe` lazy. Construction no longer evaluates codomains, motives or
   constructor result types.

## Not in scope

- Type-directed conversion.
- Removing the memoized type slot to save memory. v1 keeps one lazily filled
  reference per value. A side table is a later measurement.
- A runtime for closed programs, and caching across runs.

## Required validation

1. **Type agreement.** With assertions on, `typeOf(v) ≡ v.tpe` for every value
   built by the test suite and by every generation example in
   `../lemur-raccoon`.
2. **Class bits.** They agree with `isProposition(v.tpe)` and eta eligibility
   everywhere in the same runs.
3. **Dependencies and keys.** Determinant-based dependencies equal today's.
   Determinant-based keys induce the same equality on every pair of values that
   conversion compares.
4. **Outputs.** Byte-identical generation outputs, and `sbt validate` in both
   repositories, after every stage.
5. **Demand.** Count type programs run per check, against types computed
   eagerly today. This is a measuring instrument, not a target.
6. **CPU.** The paired protocol of interpreter-performance.md after stages 4
   and 6. No stage may regress.

## Open questions

- Should the memoized type live in the value or in a side table keyed by
  identity?
- Could a canonical proof bound to an explicit binder keep its proposition as a
  program until a consumer reads it?
- Which conversion paths, once measured, would justify type-directed
  conversion?
