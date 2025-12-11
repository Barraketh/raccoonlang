# RaccoonCore Kernel Specification
_AST, typing rules, definitional equality, and match/index refinement_

This document specifies **RaccoonCore**, the **trusted kernel language**. The kernel accepts only fully explicit terms:
- **No holes**
- **No tactics**
- **No implicit arguments**
- **No instance search**
- **All dependent matches must provide an explicit motive**

## 0) High-level pipeline

1. **Parse RaccoonSurface** (user syntax).
2. **Elaborate / desugar** to **RaccoonCore**:
   - expand multi-arg binders
   - expand surface `match`/equations to core `Match` with explicit motive
   - run **index refinement** per `match` (small unification problem over indices)
   - perform **universe inference** on surface `Type`/declarations and synthesize explicit levels in core (deterministic; no dependence on term metavariables)
   - optionally expand `implicit[T]` (instance search) if you include it (**not** in kernel)
3. **Kernel check** RaccoonCore program:
   - verify declarations
   - typecheck terms
   - definitional equality via WHNF + spine comparison

Only step (3) is trusted. Surface syntax determines defaults (e.g., transparency), but the kernel relies solely on explicit core fields (e.g., `ConstDecl.transparency`).

---

## 1) RaccoonCore AST

### 1.1 Levels (non-cumulative)

```text
Level =
  | LNat(n: Nat)           // 0,1,2,...
  | LSucc(l: Level)
  | LMax(a: Level, b: Level)
```

Canonical form and equality:
- Maintain a simple normal form for levels (e.g., flatten `max`, keep `succ` as an integer offset per atom) and compare structurally on the normal form.
- Definitional equality of `Type`s uses this normalized `levelEq`.
- Levels are always explicit in kernel terms and declarations (produced by elaboration’s universe inference or explicit surface annotations).

### 1.2 Relevance

```text
Rel = Rel | Irr
```

### 1.3 Terms

Implementation should use **de Bruijn indices**; this spec uses names for readability.

```text
Term =
  | Var(x)
  | Const(c)
  | Type(level)

  | Pi(rel, x, A, B)              // (x : A) -> B  or (.x : A) -> B
  | Lam(rel, x, A, body)          // binder type A stored for checking
  | App(fn, arg)

  | Let(rel, x, A, val, body)

  | Match(scrut, scrutTy, w, motive, cases)
```

Notes:
- `scrutTy` is an optional cache for performance; the checker must verify it is convertible to the inferred scrutinee type.
- `motive` must be a lambda over `w`, and its type must be `Pi(Rel, w : scrutTy, Type(u))` for some `u`.

### 1.4 Cases (index-refined)

A case binds only the constructor args that remain **after** index refinement.

```text
Case =
  | Case(ctorName, binders, body)

Binder = (rel, x, A)     // A may be cached; kernel re-derives from ctor type
```

---

## 2) Global environment

The environment contains constant and inductive declarations.

```text
ConstDecl = {
  name: Name,
  type: Term,
  value: Option[Term],          // only for definitional (inline) constants
  transparency: Opaque | Inline // delta unfolds Inline only
}

InductiveDecl = {
  name: Name,
  params:  List[Binder],        // parameters (not refined)
  indices: List[Binder],        // indices (refined by matches)
  universe: Level,
  ctors: List[CtorDecl]
}

CtorDecl = { name: Name, type: Term }
```

Notes:
- `params` and `indices` are part of the inductive head type.
- `CtorDecl.type` must begin with the **same params telescope** as the inductive.

Enforcement:
- During declaration checking, verify that each constructor’s telescope starts with a sequence convertible (in `MIrr`) to the inductive’s parameters (same arity, relevance, and types up to conversion). Emit a targeted error on mismatch.

(You can add positivity checks later; the rest of the kernel still works without them.)

---

## 3) Context and modes (irrelevance discipline)

Each local binder carries relevance:

```text
CtxEntry = (rel, x, A)
Γ = list[CtxEntry]
```

Typechecking uses a **mode**:

```text
Mode = MRel | MIrr
```

- In `MRel`, **Irr variables may not be used**.
- In `MIrr`, both `Rel` and `Irr` variables may be used.

Rules of thumb:
- **Types** are checked in `MIrr`.
- **Irrelevant arguments** are checked in `MIrr`.
- Most term bodies are checked in `MRel`.
- Pattern matching on irrelevant values is forbidden by the variable rule in `MRel` and should be rejected explicitly in match typing.

---

## 4) Kernel judgments

Bidirectional typing:

```text
infer(Γ, mode, t) -> A
check(Γ, mode, t, A) -> ok
isType(Γ, t) -> Level
conv(Γ, t, u) -> bool
```

---

## 5) Typing rules (algorithmic)

### 5.1 Variables / constants

**Var**

```text
infer(Γ, mode, Var(x)):
  (rel_x, x, A) = lookup(Γ, x)
  if mode == MRel and rel_x == Irr: error
  return A
```

**Const**

```text
infer(Γ, mode, Const(c)):
  return Env[c].type
```

### 5.2 Universes

```text
infer(Γ, mode, Type(u)) = Type(LSucc(u))
```

### 5.3 Π types

```text
infer(Γ, mode, Pi(rel,x,A,B)):
  u = isType(Γ, A)                 // check A in MIrr
  Γ' = Γ + (rel, x, A)
  v = isType(Γ', B)
  return Type(LMax(u, v))
```

Helper:

```text
isType(Γ, T) -> Level:
  infer(Γ, MIrr, T) must be convertible to Type(u) for some u
  return u
```

### 5.4 Lambdas

Lambdas are checked against an expected Π type.

```text
check(Γ, mode, Lam(rel,x,Aann,body), expected):
  expected' = whnf(expected)
  expected' must be Pi(rel2, y, A, B)
  require rel == rel2
  require conv(Γ, Aann, A)
  Γ' = Γ + (rel, x, A)
  check(Γ', mode, body, subst(B, y := Var(x)))
```

### 5.5 Application

```text
infer(Γ, mode, App(f,a)):
  Tf = whnf(infer(Γ, mode, f))
  Tf must be Pi(rel, x, A, B)

  if rel == Rel: check(Γ, mode, a, A)
  if rel == Irr: check(Γ, MIrr, a, A)

  return subst(B, x := a)
```

### 5.6 Let

```text
infer(Γ, mode, Let(rel,x,A,val,body)):
  isType(Γ, A)

  if rel == Rel: check(Γ, mode, val, A)
  if rel == Irr: check(Γ, MIrr, val, A)

  Γ' = Γ + (rel, x, A)
  Tbody = infer(Γ', mode, body)

  return subst(Tbody, x := val)     // zeta at type level
```

### 5.7 Match (explicit motive + index refinement)

Match typing requires:
1) infer scrutinee type `T` and identify inductive head `I` with params+indices
2) check `motive : (w : T) -> Type(u)` for some `u`
3) compute **reachable constructors** and **forced substitutions** by unifying indices
4) typecheck each case body at `motive` applied to the reconstructed constructor value
5) result type is `motive scrut`

Algorithm:

```text
infer(Γ, mode, Match(scrut, scrutTy?, w, motive, cases)):

  Ts = infer(Γ, mode, scrut)
  T  = whnf(Ts)
  require T is (I p1..pm i1..in) for some inductive I

  // motive check (types are checked in MIrr)
  // motive : Pi(Rel, w : T, Type(u)) for some u
  infer motive, then require conv to Pi(Rel, w:T, Type(u))

  reachable = {}
  for each ctor C of I:
    θ = refineIndices(Γ, T, C.type)
    if success: reachable.add((C, θ))

  require cases cover exactly the ctor names in reachable
  // If reachable is empty, cases must be empty (zero-case matches are allowed)

  for each (C, θ) in reachable:
    case = lookupCase(cases, C.name)

    // derive remaining ctor binders after applying θ
    ΓC, ctorApp = instantiateCtorContext(Γ, C.type, params=p1..pm, θ, case.binders)

    branchTy = App(motive, ctorApp)
    check(ΓC, mode, case.body, branchTy)

  return App(motive, scrut)
```

---

## 6) Index refinement unification (first-order, WHNF-aware)

Purpose: decide whether a constructor can produce the scrutinee type and compute forced ctor-arg assignments.

```text
refineIndices(Γ, T = I p.. i.., Ctype):

  // strip inductive params from Ctype, check they match p..
  // remaining: Π (a1:A1) ... Π (ak:Ak). I p.. j1(a..) ... jn(a..)

  create fresh unification vars ?a1.. ?ak
  unify each index pair: ji(?a..)  ~  ii

  return θ = assignments for some subset of ?aj, or Fail
```

instantiateCtorContext(Γ, Ctype, params, θ, surfaceBinders):
- Instantiate the ctor type with the given `params`.
- Apply the forced assignments θ to the ctor telescope.
- Drop binders whose values are fully determined by θ (forced by indices).
- The remaining binders, in original order and with original relevance, must correspond 1-1 to `surfaceBinders`.
- Extend Γ with these remaining binders to form ΓC.
- Build `ctorApp` as the constructor applied to `params` and all ctor arguments (forced arguments filled from θ; remaining from the local binders in ΓC).
- Return (ΓC, ctorApp).

### Unification procedure `unifyIndex(Γ, lhs, rhs)` (sketch)

- reduce both sides to WHNF (β/ζ/ι + δ-inline)
- if both are the same constructor/const/var, recurse on subterms
- if `lhs` is a unification variable `?aj`:
  - occurs check (`?aj` not in `rhs`)
  - assign `?aj := rhs` (must be well-typed at its expected type)
- symmetric for `rhs` being a unification variable
- otherwise fail

**Restriction:** only solve for ctor-arg variables that appear in indices (or become forced while unifying indices). This avoids higher-order behavior and keeps it fast/predictable.

---

## 7) Definitional equality and reduction

### 7.1 WHNF

`whnf(Γ, t)` performs:
- β: `App(Lam(..., body), arg)` → substitute
- ζ: `Let(..., body)` → substitute
- δ: unfold `Const(c)` only if `Inline`
- ι: reduce `Match` when scrutinee WHNF is a constructor application with a matching case

```text
whnf(t):
  repeat:
    if t = App(Lam(..., body), arg): t = subst(body, x := arg)     // beta
    else if t = Let(..., body): t = subst(body, x := val)          // zeta
    else if t = Const(c) and c is Inline and has value: t = value  // delta-inline
    else if t = Match(...) and scrut reduces to ctor app:
            t = branchAppliedToCtorArgs                            // iota
    else break
  return t
```

### 7.2 Conversion (irrelevance-aware)

```text
conv(Γ, t, u):
  t = whnf(t); u = whnf(u)

  if both are Type(l1), Type(l2): return levelEq(l1,l2)

  if both are Pi(rel,x,A,B) and Pi(rel',y,A',B'):
     rel==rel' and conv(A,A') and conv(Γ+(rel,x,A), B, subst(B',y:=Var(x)))

  else:
     (h1, as) = decomposeApp(t)
     (h2, bs) = decomposeApp(u)
     require convHead(h1,h2)
     Ty = inferHeadType(Γ, h1)
     return convSpine(Γ, Ty, as, bs)

convSpine(Γ, Ty, as, bs):
  while as,bs nonempty:
    Ty = whnf(Ty) must be Pi(rel,x,A,B)
    a = pop(as); b = pop(bs)

    if rel==Rel: require conv(Γ,a,b)
    if rel==Irr: // ignore a and b

    Ty = subst(B, x := a)

  require both empty

convHead(h1,h2):
- Reduce heads to WHNF and require they are the same syntactic head:
  - same variable de Bruijn index, or
  - same constant name, or
  - same constructor name, or
  - both are stuck `Match` heads (handled by 7.3), or
  - both are the `Type` constructor (handled earlier).
  Otherwise, fail.
```

Notes:
- This yields **use-time proof irrelevance**: irrelevant args do not affect definitional equality.
- Optional typed η may be added as a *comparison rule* (not required for this spec).

### 7.3 Stuck `Match` terms
If two `Match` terms cannot ι-reduce, compare structurally:
- scrutinee by `conv`
- motive by `conv`
- cases by ctor name and body comparison under the case telescope

For a first implementation, recursive structural `conv` is acceptable.

---

## 8) Performance requirements (for RL-friendly typechecking)

Minimum required engineering:
- de Bruijn indices + hash-consing (or strong sharing)
- WHNF cache keyed by (term, transparency mode)
- conversion cache keyed by (term1, term2, transparency mode)
- cache inferred types of neutral heads (`inferHeadType`)
- keep δ unfolding restricted (Inline-only) by default

Notes:
- All caches must include the current transparency mode in their keys to avoid unsound hits across Inline/Opaque contexts.

---
