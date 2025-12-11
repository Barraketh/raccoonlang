# RaccoonSurface Parser Specification
_Grammar, desugaring rules, and parser-oriented examples_

This document defines **RaccoonSurface**, the user-facing syntax. RaccoonSurface desugars **deterministically** to RaccoonCore.

Scope of this version:
- Surface universes are inferred with a simple, deterministic algorithm; core remains explicit.
- Transparency: declarations are opaque by default; the only surface modifier is `inline`.
- Keep equations-style definitions out-of-scope (single `:=` only).
- Keep optional features (`implicit[...]`, holes) out of the kernel.

## 1) Design constraints

- **No implicit parameters:** every binder is explicit.
- **Dependent matches must include an explicit motive** using a `returning` clause.
- Optional: `implicit[T]` denotes an explicit elaboration-time resolution site (**not** in the kernel).
- Optional: holes `?h` (and tactics) are tooling; **kernel never sees holes**.

---

## 2) Grammar (EBNF)

```ebnf
Program ::= { Decl }

Decl ::= DataDecl | DefDecl | TheoremDecl | AxiomDecl

ModDef  ::= "inline"                             // only defs may be marked inline
LParams ::= ".{" Ident { "," Ident } "}"        // optional explicit level params (naming/arity hints)

DataDecl ::= "data" Ident LParams? Params ":" Ty
             "where" "{" { CtorDecl } "}"
CtorDecl ::= "|" Ident { Binder } ":" Ty         // ctor telescope must start with params

DefDecl ::= ModDef? "def" Ident LParams? Params ":" Ty ":=" Term
TheoremDecl ::= "theorem" Ident LParams? Params ":" Ty ":=" Term
AxiomDecl ::= "axiom" Ident LParams? Params ":" Ty

Params ::= { Binder }
Binder ::= "(" Ident ":" Ty ")"
         | "(." Ident ":" Ty ")"                // irrelevant binder (erased), no match allowed

Term ::= Ident
       | "Type" Level                            // explicit universe level
       | "Type" "_"                               // introduce a fresh universe variable (to be inferred)
       | "\\" Binder "=>" Term                     // lambda
       | "forall" Binder "->" Term                 // Pi (nest for multiple binders)
       | Term Term                                 // application (left-assoc)
       | "let" Ident ":" Ty ":=" Term "in" Term     // surface let is always relevant
       | "(" Term ":" Ty ")"                       // type ascription

       | "match" Term "as" Ident "returning" Ty "with" "{"
            { "|" Pattern "=>" Term }
         "}"

       | "implicit" "[" Term "]"                 // elaboration-time resolution site (optional)
       | "?" Ident                               // named hole (optional)

Pattern ::= Ident { Ident }                       // ctor name plus remaining binders only

// Types (restricted grammar used where a type is expected)
Ty   ::= ForallTy | ArrowTy
ForallTy ::= "forall" Binder "->" Ty
ArrowTy  ::= AppTy { "->" Ty }                    // right-assoc
AppTy ::= AtomTy { AtomTy }                        // left-assoc application
AtomTy ::= Ident | "Type" Level | "Type" "_" | "(" Ty ")"
```

Levels:

```ebnf
Level ::= NatLit | Ident | "succ" "(" Level ")" | "max" "(" Level "," Level ")"
```

---

## 3) Deterministic desugaring to RaccoonCore

### 3.1 Universes, types, and modifiers

- Level params in headers are optional. If omitted, elaboration performs universe inference and synthesizes explicit level params in the core output. Explicit level params may be used to pin naming/arity.
- Types are restricted by `Ty` (no `let`, `match`, or `lambda` directly in types). Use `forall`/`->`, application, identifiers, and `Type`/`Type _`.
- Transparency: default is `opaque`. The only surface modifier is `inline` (applies only to `def`), which marks a definition for δ-unfolding. `theorem` and `axiom` are always treated as `opaque`.

Examples (surface, with inferred levels using `Type _`):

```text
data Vec (A : Type _) : Nat -> Type _ where {
| nil  : Vec A zero
| cons (n : Nat) (a : A) (xs : Vec A n) : Vec A (succ n)
}

inline def id (A : Type _) (x : A) : A := x
theorem refl (A : Type _) (x : A) : Eq A x x := ?h
```

The elaborator infers and inserts explicit universe parameters in the generated core (e.g., `.{u}`) and on `Type u` occurrences.

### 3.2 Multi-argument binders

Surface binders desugar to nested `Pi`/`Lam` in RaccoonCore.

```text
Surface:
  def f (x:A) (y:B x) : C := t

Core:
  f := Lam(Rel, x:A, Lam(Rel, y:B x, t))
```

### 3.3 Match desugaring (explicit motive required)

```text
Surface:
  match v as w returning R w with {
  | C a b => t1
  | D x   => t2
  }

Core (schematic):
  Match(
    scrut = v,
    w = w,
    motive = Lam(Rel, w:T, R w),
    cases = {
      Case(C, binders=[a:A1, b:A2], body=t1),
      Case(D, binders=[x:B1],       body=t2)
    })
```

### 3.4 Index refinement for dependent inductives

For indexed inductives (e.g. `Vec A n`), the elaborator computes:
- which constructors are **reachable** given the scrutinee type
- which constructor arguments are **forced** by indices

Forced arguments may be omitted from the surface pattern and are not bound in the core case. Explicit `Ctor(x := t)` bindings are not supported in this version; indices are handled by refinement only.

### 3.5 Universe inference (elaboration)

Universe inference runs during elaboration (Surface → Core) and produces explicit levels in the core. It is deterministic and does not depend on term-level metavariables.

Constraint forms generated:
- Equality: `u = v` (from reusing the same `Type` level or explicit annotations)
- Inequality: `u ≤ v` (from subtyping of universes, e.g., cumulative rules in types of types are avoided; see below)
- Max: `u = max(u1, u2, ...)` (from Π-types and composite type formation)
- Type formation: `Type u : Type (succ u)`

Generation sketch:
- Each `Type _` introduces a fresh universe variable; `Type l` uses the given level.
- For `Pi(x : A) -> B`, if `A : Type uA` and `B : Type uB`, then the Π type has `Type (max(uA, uB))` (emit `uΠ = max(uA, uB)`).
- For applications and inductive heads, propagate constraints from declared types (e.g., if `I : ... -> Type uI`, uses of `I` constrain result to `uI`).
- For inductive declarations and constructors, equate the inductive's result level with the `max` dictated by its parameters/indices’ levels.

Solving:
- Use union-find for equalities to compute representatives.
- Encode `≤` as edges in a DAG over representatives; topologically assign minimal solutions.
- Encode `u = max(S)` as `s ≤ u` for all `s ∈ S`, and prefer the minimal solution satisfying all incoming edges.
- Apply `succ` constraints for `Type u : Type (succ u)` as needed in kind-checking.

Result:
- Core terms receive explicit, normalized level expressions; declarations receive explicit level parameter lists synthesized from the free level variables of their types.

Example: `v : Vec A (succ n)` forces the `cons` index argument to be `n`, and `nil` is unreachable.

---

## 4) Examples (parser test suite)

### 4.1 Nat and Vec definitions (surface, with inferred levels)

```text
data Nat : Type 0 where {
| zero : Nat
| succ (n : Nat) : Nat
}

data Vec (A : Type _) : Nat -> Type _ where {
| nil : Vec A zero
| cons (n : Nat) (a : A) (xs : Vec A n) : Vec A (succ n)
}
```

### 4.2 Non-dependent match (constant motive)

```text
def head (A : Type 0) (n : Nat) (v : Vec A (succ n)) : A :=
  match v as w returning A with {
  | cons a xs => a
  }
```

Note: the pattern `cons a xs` omits the index argument because it is forced by the scrutinee type `Vec A (succ n)`.

### 4.3 Dependent match with scrutinee binder available

```text
def isNil (A : Type 0) (m : Nat) (v : Vec A m) : Type 0 :=
  match v as w returning Type 0 with {
  | nil => Type 0
  | cons a xs => Type 0
  }
```

### 4.4 Irrelevant binders (use-time proof irrelevance)

```text
def ignoreProof
  (A : Type 0)
  (x : A)
  (.p : Eq A x x)
  : A
:= x
```

### 4.5 Zero-case matches (empty reachable set)

```text
def absurdVecZeroSucc (A : Type _) (n : Nat) (v : Vec A (succ n)) : False :=
  match v as w returning False with { }
```

If no constructors are reachable by index refinement, the empty match is accepted and has type `False` for any `v`.

### 4.6 Optional explicit search sites

```text
def step (x a b : Nat) : Nat :=
  ifDec
    (Or (Lt x a) (Lt b x))
    (implicit[Decidable (Or (Lt x a) (Lt b x))])
    Nat
    (\(.h : Or (Lt x a) (Lt b x)) => zero)
    (\(.h : Not (Or (Lt x a) (Lt b x))) => succ zero)
```

### 4.7 Optional holes (not allowed in kernel output)

```text
theorem demo (A : Type 0) (x : A) : Eq A x x := ?goal
```

The parser may accept holes, but the kernel must reject them. A separate elaboration/tactic phase must eliminate holes before kernel checking.

---

Notes
- Type ascriptions `(t : T)` guide checking only and do not change the core term beyond cached type annotations.
- Surface `let` is always relevant; irrelevant `let` is not supported in the surface grammar (initially).
- Unreachable/extra cases in a match must be rejected by the elaborator.

---
