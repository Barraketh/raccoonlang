# Scopes contain values

Status: **draft for review** (2026-09-30). Amends `docs/kernel.md` "Universes and function types" and "Scopes and
atoms", and `docs/language.md` "Closures" and "Scopes".

## 1. The feature

`scope l => e` opens a **scope** named `l`. The scope is open while `e` runs and closed afterwards. `l` is a
**lifetime**: the name of a scope, or of several. A value **belongs to** `l` when its type mentions `l`, and
`Type { scope = l }` declares a family whose values belong to `l`.

The guarantee:

> **Once a scope closes, nothing can hold, create or use a value that belongs to it.**

Which values belong to which scopes:
- **Data** belongs to the scopes its type's arguments name. A `List(Lease(l))` belongs to `l`.
- **A function** belongs to the scopes of what it captures, and to the scopes its code mentions.
- **When a scope closes**, its result's type may not mention it.

A lifetime is not data: no field or list holds one. So these two are the only ways a value can belong to a scope.

## 2. Examples

```raccoon
inductive Lease (l: Lifetime) : Type { scope = l }
 | mk : Lease(l)

def use {l: Lifetime}(h: Lease(l)): Nat := 7
```

| # | Program | Verdict |
|---|---|---|
| 1 | `scope l => use(Lease.mk(l))` | accepted: the result `7 : Nat` belongs to no scope |
| 2 | `use(scope l => Lease.mk(l))` | rejected: the result is a `Lease(l)`, and `l` has closed |
| 3 | `scope l => List.cons(Lease.mk(l), List.nil(Lease(l)))` as a result | rejected: a `List(Lease(l))` belongs to `l` |
| 4 | `fun (u: Unit): Nat => use(h)`, with `h := Lease.mk(l)` made inside the scope, as its result | rejected: the function captures `h`, so its type is `{ scope = l } Unit -> Nat` |
| 5 | `scope l => fun (u: Unit): Nat => use(Lease.mk(l))` as a result | rejected: the function's code mentions `l`, so it belongs to `l` too |
| 6 | the functions of 4 and 5, applied inside the scope | accepted: `l` is open there |
| 7 | `scope l => fun (u: Unit): Nat => 3` as a result | accepted: the function belongs to no scope |

Example 5 is what this document adds. Without it, the function would leave with type `Unit -> Nat` and, called later,
build and use a lease of a closed scope.

**A library that lends a scope:**

```raccoon
// In Lease's module, which seals the family, so only it can call Lease.mk.
def withLease {S: Lifetime}{A: Type { scope = S }}{Sf: Lifetime}
    (f: { scope = Sf } (l: Lifetime) -> Lease(l) -> A): A :=
  scope l => f(l, Lease.mk(l))

// A client: accepted.
def ok : Nat := withLease(fun (l: Lifetime)(h: Lease(l)): Nat => use(h))

// Rejected: A is chosen outside the callback, so it cannot mention the callback's l.
def no : Nat := use(withLease(fun (l: Lifetime)(h: Lease(l)): Lease(l) => h))
```

**Linear tokens.** A token `Tok(l)` declared `{ kind = lin, scope = l }` must be used exactly once, and belongs to
`l`. So it is used up before `l` closes, and after it closes nothing can make another.

**In the GPU library.**
- **C blocks.** `Gpu.loop` opens a scope for its body's C block. A `Val(m, …)` is a C variable of that block, so the
  guarantee is "no use of a variable after its block ends".
- **Shared reads.** A read lease that many threads share is copyable and belongs to a scope. When the scope closes,
  every copy is gone, so the owner gets the buffer back whole without counting readers (`docs/SEPARATION_PILOT.md`
  §5).

## 3. The rule this adds

**A function belongs to every scope its code mentions.** Concretely:
- **A lambda.** A lifetime that its body mentions counts as a capture, whether it is a scope's name or a lifetime
  parameter from outside the lambda. It joins the lambda's closure scope, as a captured lease's scope does. Mentions
  inside types written in the body count too. The lambda's own lifetime parameters don't count: whoever calls it
  supplies them.
- **A function type.** It belongs to the scopes its parameter types and result type mention, other than its own
  lifetime parameters. They are code too: each time the type is instantiated they run, and they could build a lease.
  For example, this is rejected:

  ```raccoon
  def T : Type := scope l => (x: Nat) -> Vec(Nat, count(Lease.mk(l), x))
  ```

**Unchanged:**
- **Applications.** An application runs at once, so one that mentions `l` and returns data keeps nothing of `l`
  (example 1).
- **Level and kind variables.** A lambda that mentions a `Kind` or `Level` variable gains no scope.
- **Repeated scopes.** One `scope` term, evaluated twice or re-entered by recursion, is one scope. Each callback still
  sees its own `l`, so two of them cannot mix.

## 4. Why the rule is enough

A value can reach a scope only through what it is made of:

| A value made of | belongs to its scopes through |
|---|---|
| constructor fields | its family's declared scope, which includes every field's |
| captured values | the lambda's closure scope |
| code that mentions a lifetime | the lambda's closure scope, or the function type's scope (§3) |
| a type | the type's own `scope` |

Two kinds of value hold a scope without belonging to it, and neither runs:
- **Blocked computations.** One blocked on an opaque definition or an axiom never runs. While checking, a computation
  blocked on a parameter only computes types.
- **Proofs.** A proof never runs.

So once a scope closes, nothing that can run belongs to it. The scope's result doesn't belong to it, by §1's closing
rule, and nothing alive before the scope opened could reach it either.

One question from the 2026-09-28 review must be re-examined, not assumed settled: an implicit argument reconstructed
inside a lambda. It is read from an argument's type, which a parameter type or a capture already accounts for, but the
review withdrew this rule over that case before the current rules on function types and families were adopted.

## 5. For implementers

The kernel's terms:
- a scope's identity is an **atom**;
- a value belongs to `l` when **its type's sort's scope** contains `l`'s atom;
- "may not mention it" is the existing **`LifetimeEscapes`** check.

The change:
- `Interpreter.lambdaCaptures`, and the derived closure scope, admit locals of type `Lifetime`, which contribute the
  lifetime they hold. Locals of type `Level` and `Kind` still contribute nothing.
- `Interpreter.piClassifierFromChecked` adds the `Lifetime` locals that a function type's binder types and codomain
  mention, other than its own binders.
- A written closure scope that omits such a lifetime is `ScopeExceeded`.

Documents:
- `kernel.md` "Scopes and atoms": the paragraph beginning "Evaluation never makes the check. A value computed under a
  scope may leave it…" is replaced by §1's guarantee and §4. "A global value may hold an atom, though never a variable"
  becomes "only inside a blocked computation".
- `language.md`:
  - "Closures": "a variable of `Kind` or `Lifetime` contributes nothing" becomes §3's lambda rule.
  - "Scopes": its `Unit -> Nat` example becomes example 5, rejected. Its prose uses §1's vocabulary.
- `LEMUR_ON_RACCOON.md` §4.2's "A lifetime is not a capability" is superseded.

Tests and corpus changes:
- `ScopeTests`' "a value whose type's sort does not name the atom may leave its scope, even when it holds the atom":
  its closure cases become rejections, and its blocked-computation cases stay accepted.
- `examples/leases/main.rac`'s `later` is example 5, so it moves to the file's list of rejected variants.
- Callbacks that mention an enclosing lifetime gain it in their closure scope. The `Gpu` combinators take
  `{ scope = Sf }` callbacks, which accept that. A callback checked against an arrow written without a closure is
  refused, and step 1 counts how often that happens.

## 6. Steps

1. **Measure.** Implement §5 in a worktree, run `sbt test` and `gpu/check.sh`, and classify each new rejection: a
   value that really belonged to a closed scope, or an arrow written without a closure. An implementer at medium effort.
2. **Attack.** A hostile reviewer at high effort tries to make a value that belongs to a scope without its type
   saying so: through implicit arguments, evidence, re-evaluated residuals, destructuring, the eta view, packed
   literals, and a scope entered twice.
3. **Land.** The kernel change; tests for every row of §2 and §4, each an accepted program plus the smallest change
   that is rejected; the amended documents. `gpu/check.sh` must stay green with byte-identical kernels.

## 7. Decisions for review

1. **Function types count too**, not only lambdas (§3's `T`).
2. **Mentions inside types count**, as they do for other captures. That is simpler, and safe: a type in a lambda's
   body runs when the lambda does.
3. **No restriction on who mints at a lifetime.** Once every function belongs to the scopes it mentions, minting at a
   closed scope is impossible. Who may mint at an open one stays sealing's job.
4. **One scope per `scope` term**, not one per evaluation. Callbacks keep evaluations apart.
5. **The documents use "scope" and "belongs to"**, with "atom" kept to `kernel.md`.
