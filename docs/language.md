# Language conveniences

Surface features that cost the kernel nothing: each is checked by turning it into terms or messages the checker
already knows. [kernel.md](kernel.md) has the kernel's rules.

## Rewriting

`rewrite h in e` proves the type expected of it from `e`, where `h` proves an equation `Eq(A, l, r)`: it rewrites `l`
to `r` in the goal, and checks `e` against the result, as Lean's `rw [h]` does. `rewrite <- h in e` rewrites `r` to `l`.
A list applies its steps in order, each to the goal the earlier ones leave:

```raccoon
def forward (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Nat.le(b, 3)) : Nat.le(a, 3) := rewrite e in p

def chain (a: Nat)(b: Nat)(c: Nat)(e1: Eq(Nat, a, b))(e2: Eq(Nat, c, b))(p: Nat.le(c, 5)) : Nat.le(a, 5) :=
  rewrite [e1, <- e2] in p
```

`rewrite [h1, h2] in e` is `rewrite h1 in rewrite h2 in e`. The body `e` extends as far as a lambda's. `rewrite` is no
keyword: a term that starts with it, whitespace, its steps and `in` is a rewrite, and elsewhere `rewrite` is an
identifier.

### What it means

A step is the call a user would write, and is checked as that call. Against the goal `T`, `rewrite h in e` with
`h : Eq(A, l, r)` is

```raccoon
Eq.substProp(Eq.symm(h), fun (x: A): Prop => T[x/l], e)
```

and `rewrite <- h in e` is `Eq.substProp(h, fun (x: A): Prop => T[x/r], e)`. The motive `T[x/l]` is `T` with its
occurrences of `l` abstracted. `e` is checked against the motive at the other side, `T[r/l]`, as a term written with
that type would be, so a match or a later step inside `e` sees it. The call's type, the motive at `l`, must convert
with `T`. The checked term, the residual a definition keeps, is the call; nothing after checking knows rewrites.

The checker does not trust the motive. `TypeChecker.checkRewrite` hands the step, the type of `h` and the goal to
`Rewrite.plan`, which only builds source syntax, and checks the call it returns as it checks any application. So an
abstraction that goes wrong can only fail to check: a motive left ill-typed is reported as the rewrite's failure, with
the motive, and so is a call whose type does not give back the goal.

### Occurrences

The goal is abstracted as it evaluates. `Rewrite.plan` quotes the goal's value with every value of the key of `l`
(`ValueKey`, structural) read as the motive's variable, so an occurrence is a subterm of the goal's evaluated form that
evaluation built the same way as `l`. This finds a computed scrutinee that the goal as written only names through a
definition:

```raccoon
def pick (n: Nat) : List(Nat) := Bool.cond(isZero(n), List(Nat), List.cons(n, List.nil(Nat)), List.nil(Nat))

def member (n: Nat)(z: Eq(Bool, isZero(n), Bool.true)) : List.Mem(Nat, n, pick(n)) :=
  rewrite z in List.Mem.head(n, List.nil(Nat))
```

`pick(n)` evaluates to a `Bool.cond` stuck on `isZero(n)`, which the motive abstracts; at `Bool.true` the motive
evaluates to membership in `[n]`, which `List.Mem.head` proves. A rewrite of the proof's own type could not do this:
evaluation has already removed `Bool.true` from it.

A match written on a computed scrutinee is stuck on the scrutinee's value, which it holds in place of the scrutinee's
code ([stuck matches](kernel.md#stuck-matches)), so a rewrite finds it there as well:

```raccoon
def coordinate (n: Nat)(k: Nat): Option(Nat) := {
  match Nat.ble(2147483648, n) returning Option(Nat) with
  | Bool.false => Option.some(Nat.add(n, k))
  | Bool.true => Option.none(Nat)
}

def low (n: Nat)(k: Nat)(h: Eq(Bool, Nat.ble(2147483648, n), Bool.false))
    : Eq(Option(Nat), coordinate(n, k), Option.some(Nat.add(n, k))) :=
  rewrite h in Eq.refl(Option.some(Nat.add(n, k)))
```

The motive matches on its variable where `coordinate` matches on `Nat.ble(2147483648, n)`; at `Bool.false` it takes
the first case.

- Every occurrence is abstracted. To rewrite some only, write the `Eq.substProp` call with its motive.
- Matching is structural on evaluated values, not up to conversion: a subterm that converts with `l` but evaluates to
  another form, such as a part of a canonical Nat sum (`a + b` inside `a + b + c`), is no occurrence.
- An occurrence that evaluation removed from the goal cannot be abstracted: `Nat.lt(n, n)` evaluates to
  `Eq(Bool, Bool.false, Bool.true)`, which no longer mentions `n`. Write the motive there.
- Abstracting an occurrence that something else's type depends on, such as the index of a local's type, leaves the
  motive ill-typed, which is reported.
- The motive is the goal's evaluated form, so it can be larger than one written by hand; that costs checking time,
  not source text.

A step whose side does not occur in the goal is refused, since it would change nothing and the direction is the likely
mistake: the message says when the other side occurs (the step may need, or not need, `<-`), and when the two sides
convert, so the step is redundant.

### Where the goal comes from

A rewrite needs the type expected of it; Raccoon otherwise checks terms bottom-up. It has one:

- as a `let` 's value with a type, `let x : T := rewrite h in e`;
- as a definition's or a lambda's body, against its declared result type;
- as a block's result or a match case's body, against the type expected of the block or the match, refined in the case;
- as an argument whose parameter's type captures nothing (no `$x`), so that the earlier arguments fix it, as in
  `small(a, rewrite e in p)` for `small (n: Nat)(h: Nat.le(n, 3))`, or the third argument of `Eq.substProp`;
- as the body of an earlier step.

Elsewhere, in an unannotated `let` or at a parameter such as `Or.inl` 's `(left: $a in Prop)`, whose type is read off
the argument's own, it is refused with a message that asks for the type: `let x : T := rewrite h in e`.

A rewrite proves propositions; a goal in `Type` is refused (`Eq.subst` casts data).

## Inferred list arguments

The prelude's permutation, membership and `flatMap` laws take the lists they relate and the element type as explicit
arguments. Each also has a form that captures them from the proofs it takes (`$` patterns, as `Eq.symm(p: Eq($A, $x,
$y))` does), under its own name, so existing callers keep working. The kernel's `List.Perm.cons` and `List.Perm.trans`
are constructors, whose stored fields cannot become captures, so their forms are prelude definitions too.

| Explicit form | Captured form |
|---|---|
| `List.Perm.trans(A, xs, ys, zs, p, q)` | `List.Perm.chain(p, q)` |
| `List.Perm.symm(xs, ys, p)` | `List.Perm.flip(p)` |
| `List.Perm.of_eq(xs, ys, e)` | `List.Perm.fromEq(e)` |
| `List.Perm.cons(A, x, xs, ys, p)` | `List.Perm.push(x, p)` |
| `List.Perm.append_left(F, xs, ys, p)` | `List.Perm.prepend(F, p)` |
| `List.Perm.append_right(xs, ys, F, p)` | `List.Perm.append(p, F)` |
| `List.Mem.perm(a, xs, ys, p, m)` | `List.Mem.along(p, m)` |
| `List.Mem.append_left(a, xs, ys, m)` | `List.Mem.append(m, ys)` |
| `List.Mem.append_right(a, xs, ys, m)` | `List.Mem.prepend(xs, m)` |
| `List.Mem.tail(a, x, xs, m)` | `List.Mem.push(x, m)` |
| `List.Mem.cons_cases(a, x, xs, m)` | `List.Mem.cases(m)` |
| `List.Mem.nil_absurd(a, m, C)` | `List.Mem.absurd(m, C)` |
| `List.flatMap.mem(A, B, f, xs, a, b, inside, here)` | `List.flatMap.member(inside, B, f, here)` |
| `List.flatMap.perm(A, B, f, xs, ys, p)` | `List.flatMap.permuted(p, B, f)` |

`push`, `prepend` and `append` name what happens to the related lists: `Perm.append(p, F)` relates `xs ++ F` to
`ys ++ F`. `flatMap.member` and `flatMap.permuted` keep `B` and `f`, which no proof's type holds before they are
needed. A law with no proof argument, such as `Perm.middle(a, xs, ys)` or `Perm.swap(A, x, y, xs)`, has nothing to
capture and no second form.

## Type mismatches

A mismatch names the expected type as the source writes it, where the checker has that, the actual type, and the first
pair of subterms where the two differ:

```text
Type mismatch: expected type: Eq(Bool, Machine.Build.isGroup(Machine.Lists.get(C, 3)), Bool.true), actual: Eq(Bool, Bool.true, Bool.true); first difference: expected Bool.false, actual Bool.true; the expected type evaluates to Eq(Bool, Bool.false, Bool.true)
```

- **Expected type as written.** For a term checked against a stated type (a `let` 's, a definition's or a lambda's
  result, a match's `returning`), that type. For an argument, its parameter's type, with the earlier parameters shown
  as the call's arguments and the signature's captures as their values; an argument or value longer than 40 characters
  shows as the parameter's or capture's own name. Otherwise, the expected type's value.
- **Actual type**, as a value.
- **First difference.** The first pair of subterms that do not convert: through applications of one head, the first
  argument pair; through kernel lists, the first element pair, or what follows the elements they share; through
  function types and local lambdas of as many binders, their codomains or bodies on shared variables; through
  projections of one field, their bases; through stuck matches of one code, their scrutinees' values, then the first
  pair of captured values. Two short values, such as numerals, that are arguments of an application, are shown with
  it. Omitted when the whole types are the pair.
- **The expected type as it evaluates**, when it prints differently from the written one.

A value prints whole up to 240 characters. A longer one prints along the path to the difference: every other argument
longer than 72 characters as `…`, a list's three elements before the one that differs and none after it, and the
differing part in outline; every part is clipped at 600 characters. So a mismatch in a large type stays a few hundred
characters, where printing the normal forms whole took tens of kilobytes. Messages are computed when read, so a
mismatch that the checker catches and recovers from costs nothing to describe.
