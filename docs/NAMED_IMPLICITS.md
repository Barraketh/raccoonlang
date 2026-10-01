# Naming an implicit argument

Status: **proposal** (2026-10-01), not implemented. A quality-of-life feature for the GPU encoding
(`gpu/encoding/NOTES.md`, "Readability refactor": the `first`/`rest` wrappers). It is the escape hatch the forced-implicit
design kept for when projection is not enough: implicit arguments written as source syntax.

## 1. The feature

`f{a := e}` gives the implicit binder `a` of `f`'s type the argument `e`. The result is `f` with that binder
instantiated, and is used as `f` would be: applied to its remaining arguments, or passed as a function.

The GPU roles write one loop body generic in `OState`, and `loopPeeled` takes it twice, at `fresh` and at `held`.
Today each role wraps the body twice. Each wrapper restates the body's binder and result types, because a function
with an implicit binder does not fit a function type without it (`docs/language.md`, "Implicit parameters"):

```raccoon
let first := fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, Wg))(st: Softmax(q, x, m, OState.fresh))
    : Pair(Ctx(n, Wg), Softmax(q, x, m, OState.held)) => block(n, i, e, st)
let rest := fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, Wg))(st: Softmax(q, x, m, OState.held))
    : Pair(Ctx(n, Wg), Softmax(q, x, m, OState.held)) => block(n, i, e, st)
let (e, (c, wa)) := loopPeeled(e, blocks, fixed, (c, wa), first, rest)
```

With the feature:

```raccoon
let (e, (c, wa)) := loopPeeled(e, blocks, fixed, (c, wa), block{o := OState.fresh}, block{o := OState.held})
```

## 2. The rules

- **The binder.** `f`'s synthesized type must be a function type whose first binder is implicit and named `a`;
  otherwise `ImplicitNotFound`, naming the binders `f`'s type has. Several are instantiated in order,
  `f{a := e1}{b := e2}`.
- **The argument.** `e` is checked against the binder's type. The result's type is the codomain at `e`'s value.
  `e` is unrestricted, as every implicit argument is: an implicit binder of linear type is never forced, and is
  rejected.
- **Forcing is unchanged.** A declaration's implicit binders must still be forced by later explicit arguments.
  Naming one at a call site supplies it, and the call no longer projects it. The other implicits of the call are
  forced as before.
- **No position is widened.** Every remaining argument is checked against the instantiated type, which compares sorts
  exactly, scope included. So a named argument accepts only what the projection would have read: a lifetime named
  explicitly fits only arguments whose types are at exactly that scope. A callback's result type bound outside the
  callback's lifetime binder, as `withLease`'s `A`, is written outside that binder too, so it cannot name the
  callback's lifetime.
- **Scope.** `f{a := e}` captures `e`. As any function value, it belongs to every scope its code captures
  (`docs/SCOPE_CONTAINMENT.md`).
- **Evaluation.** `f{a := e}` applies `f` to `e` as its implicit argument. A residual prints it as written.

## 3. Why it is safe

The feature adds no function that eta-expansion could not write. `f{a := e}` behaves as
`fun (x̄: T̄[a := e]) => f(x̄)`. In that lambda, every implicit of `f`, `a` included, is forced from `x̄` as today. The
declaration forces `a` through a later explicit argument, so the projection reads `e` back from `T̄[a := e]`. The
feature saves spelling out `T̄[a := e]` and the result type. It accepts the same arguments and computes the same
value.

## 4. Implementation

- **Parser:** a postfix `{ident := term}` on an application head, the same position as an argument list. It does not
  collide with closures, which come before a function type's binders, or with blocks, which stand alone.
- **Surface and Core ASTs:** an implicit-instantiation node holding the head, the binder's name and the argument.
- **Checker:** synthesize the head; require an implicit first binder of that name; check the argument; the type is
  the codomain at its value.
- **Applications:** a call whose head is an instantiation forces the remaining implicits only.
- **Evaluation and printing.**

## 5. Tests

- The `first`/`rest` pattern: a generic body passed twice at two instantiations, checked and evaluated.
- A wrong name: `ImplicitNotFound`.
- A later binder named first: `ImplicitNotFound`. Only the first binder can be instantiated.
- A lifetime named explicitly does not widen: an argument at a narrower scope is `TypeMismatch`.
- `withLease{A := T}` with a callback returning the lease: refused, since `T` cannot name the callback's lifetime.
- A residual prints `f{a := e}`.

## 6. Decisions

1. **Named, not positional**, so that the call says which binder it fills, and fails when the binders change.
2. **First binder only**, in order, rather than any implicit binder: a later binder's type may mention an earlier
   one, which would then be out of scope at the call.
3. **Implicit binders stay forced at declaration.** Naming one is a call-site choice, not a way to declare
   unforceable binders.
