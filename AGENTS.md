RaccoonLang – Agent Quickstart and Working Notes

Overview

- Language: Scala 2.13, sbt 1.9.x
- Entry points (core):
  - `src/main/scala/com/raccoonlang/Interpreter.scala` — runtime values, evaluator, base env
  - `src/main/scala/com/raccoonlang/TypeChecker.scala` — type synthesis/checking, unification
  - `src/main/scala/com/raccoonlang/Errors.scala` — structured error types (preferred)
  - `src/main/scala/com/raccoonlang/ErrorReporter.scala` — pretty error rendering with spans
  - `src/main/scala/com/raccoonlang/CoreAst.scala` / `SurfaceAst.scala` — ASTs
  - `src/main/scala/com/raccoonlang/LanguageParser.scala` — surface parser
  - `src/main/scala/com/raccoonlang/Elaborator.scala` — surface → core elaboration
  - `src/main/scala/com/raccoonlang/PrettyPrinter.scala` — value/term printing

Running & Debugging

- Run all tests and capture output:
  - `sbt -no-colors test &> out.txt`
  - Inspect: `sed -n '1,240p' out.txt` (or `tail -n 200 out.txt`)
- Run a single suite:
  - `sbt -no-colors "testOnly com.raccoonlang.MatchExhaustivenessTests" &> out.txt`
- Compile only:
  - `sbt -no-colors compile`

Code Layout & Key Concepts

- Values (`Interpreter.Value`): `VUniverse`, `VPi`, `VConst`, `VLam`, `VApp`, `Var`, `StuckMatch`.
  - `VLam` includes `id: Option[LamId]` (e.g., `LamId.Const(name)`) to short-circuit lambda equality during unification.
  - `VPi.env` is a var to allow mutually recursive closure environments.
- Environment (`Interpreter.Env`): scoped name map + var-link map (`varLinks`) used by unifier.
  - `addVarLink` throws typed errors on illegal linking (`VarAlreadyLinked`, `CannotLinkToBottom`).
- Type errors are structured (subtypes of `TypeError`) — prefer throwing specific errors over generic messages.
  - Attach spans precisely with `TypeError.withSpan(err, span)`.

Typechecking & Unification

- `TypeChecker.typecheck(term, env)` synthesizes a `Value`.
- `check(v, ty, env)` enforces `v.tpe` ≡ `ty` by calling `unify`.
- Unification highlights:
  - Extensional for `VPi` types (binder-by-binder, then codomain).
  - `VLam` equality: try `id` equality, then `eq`, else extensional by applying shared fresh vars.
  - Occurs check throws `OccursCheckFailed`.
  - Generic unify failure throws `UnificationFailed`.
  - Note: constraint propagation from `check` does not thread the returned `Env` (known limitation).

Pattern-Match Checking

- `TypeChecker.tyecheckMatch` performs a pre-pass for coverage:
  - Finds inductive head by peeling `VApp` with `peelHead`.
  - For each constructor, attempts `unify(scrutinee, ctorApplied)` to decide reachability.
  - Errors:
    - `UnknownConstructor` at the case span
    - `DuplicateCase` at the second occurrence span
    - `UnreachableCase` at the case span
    - `NonExhaustiveMatch` at match span (with simple missing-case skeletons)

Spans & Error Reporting

- Application errors attach the application node’s span (`typecheckApply(..., span)`).
- Match coverage errors use branch spans where relevant.
- Parser lookups throw `NotFound(name)` tagged at the identifier’s span.
- Pretty-print errors:
  - Use `ErrorReporter.pretty(err: TypeError, Source(src))` in tests if you want inline, caret-style rendering.

Tests

- Location: `src/test/scala/com/raccoonlang`.
- Style:
  - Positive tests: `runProgram(...)` and compare shape/printed form as needed.
  - Negative tests: intercept specific `TypeError` subtypes (e.g., `NonExhaustiveMatch`, `OccursCheckFailed`).
- Useful tests to read:
  - `TypingTests.scala` — basic typing scenarios and negative checks
  - `MatchRefinementTests.scala` — dependent pattern refinement
  - `MatchExhaustivenessTests.scala` — coverage diagnostics
  - `EqualityCommTests.scala` — example proofs (`succAdd`, `zeroAdd`, `addComm`)

Common Workflows (Agent Tips)

- Search quickly: `rg -n "pattern" src`
- Print file snippets: `sed -n '1,200p' path` (stay under ~250 lines)
- Patch files: use the `apply_patch` tool with cohesive edits; avoid changing unrelated code.
- Prefer throwing/propagating `TypeError` subtypes over strings; add new variants if needed.
- When adding new match checks or unifier rules, update/extend tests to intercept the specific new error type.

Language Snippets (for quick repros)

- Inductive + inline function:
  -
    inductive Nat : Type
     | zero : Nat
     | succ : Nat -> Nat

    inline def add (a: Nat)(b: Nat): Nat := {
      match b as _ returning Nat with
      | Nat.zero => a
      | Nat.succ x => add (Nat.succ a) x
    }

- Equality family:
  -
    inductive Eq : (A: Type) -> A -> A -> Type
     | refl (A: Type)(x: A) : Eq A x x

    def symm (A: Type)(x: A)(y: A)(p: Eq A x y): Eq A y x := {
      match p as _ returning Eq A y x with
      | Eq.refl A0 w => Eq.refl A w
    }

Known Limitations & Notes

- Constraint propagation: `check` calls `unify` but the updated `Env` is not threaded through the rest of checking. This can cause missed refinements in some dependent scenarios (e.g., indices). Design choice; plan a threaded-Env refactor when needed.
- Performance: unifier does normalization-as-needed (lambda application in head-to-head compares). For heavy terms, consider WHNF-aware tweaks if profiling shows hotspots.

Adding New Features

- New error kinds: add a `final case class` in `Errors.scala`, then use it in call sites; prefer attaching spans at the most local site possible (application node, case branch, identifier) before the top-level catch.
- New match diagnostics: integrate in `tyecheckMatch` pre-pass; keep the same error structure.
- Subpatterns: consider extending Core with a `Pattern` AST and generalizing the match refinement (see prior design notes).

