# Scopes contain values

Status: **draft for review** (2026-09-30). Amends `docs/kernel.md` "Universes and function types" and "Scopes and
atoms", and `docs/language.md` "Closures" and "Scopes".

Today a `scope` confines types: no position outside `scope l` is given a type that names `l`'s atom. It does not confine
values. A closure whose code names `l` but captures nothing scoped has type `Unit -> Nat` and leaves the scope; applied
later, it can build values at `l` and use them. Both programs below are accepted, and each spends a token of a lifetime
whose scope has closed:

```raccoon
// In the module that owns Lease and Tok.
def stash : Unit -> Nat := scope l => fun (u: Unit): Nat => redeem(issue(Lease.mk(l)))

// In a client, given an export `forge (l: Lifetime): Lease(l)`.
def late : Unit -> Nat :=
  withLease(fun (l: Lifetime)(h: Lease(l)): Unit -> Nat => fun (u: Unit): Nat => redeem(issue(forge(l))))
```

So "nothing confined to `l` outlives its scope" holds today only for modules that never mint from a bare lifetime and
never let minting code leave a scope: a discipline nothing checks. lemur2's regions design had the guarantee as a lemma
(`../lemur2/experimental/REGIONS.md` §3: the regions a value holds, through closures and suspended computations, lie
within its type's bound). Its computation type `Gpu S e A` recorded in `S` every region a computation touches. lemur3
removed the computation type (its D9), and with it the half of the guarantee that covered code.

This document restores it with one rule: **a lifetime that a closure's code names is one of its captures.**

## 1. The guarantee

**C1, reach.** A value reaches only the atoms its type's sort names. It reaches an atom through its fields, its
closure's captures, its type and the code of its closures. The exceptions are computations that never run: one blocked
on an opaque definition or an axiom, and, while checking, one blocked on a parameter.

**C2, containment.** While no evaluation of a `scope` term is in progress, no evaluation produces, binds or uses a value
whose type names that term's atom.

C2 follows from C1 and the existing confinement check: the `scope`'s result type does not name its atom, so its result
cannot reach it, and neither can anything that was live before the scope opened. A linear value confined to `l` is
therefore consumed inside the scope, and none is minted after it, whatever the owning module does. Sealing decides who
may make a value at a live lifetime; it is no longer needed to decide when.

An atom still names a `scope` term, not an entry into it. Two evaluations of one term, a recursive one included, share
the atom; the values of each are kept apart by the lifetime variable a callback binds, as now.

## 2. The rule

**Lambdas.** A local of type `Lifetime` that a lambda's body mentions is a capture, and contributes itself to the
derived closure scope. A `scope`'s binder is such a local, bound to its atom; so is a lifetime parameter or lifetime
binder bound outside the lambda. A local of type `Level` or `Kind` still contributes nothing, so naming a kind variable
does not make a lambda linear. Mentions in types written in the body count, as they do for other captures. A written
closure scope must contain the lifetime, else `ScopeExceeded`. The residual carries the capture as it carries any other,
and evaluation derives the field from the lifetime the local holds.

**Function types.** A function type's scope also counts the lifetime locals that its binder types and codomain mention,
other than its own binders. They are code: a later binder type and the codomain are evaluated each time the type is
instantiated, by checking and by evaluation alike, and can build values at a lifetime that appears only in an index:

```raccoon
// Rejected: the type's codomain builds a lease whenever it is instantiated.
def T : Type := scope l => (x: Nat) -> Vec(Nat, count(Lease.mk(l), x))
```

Nothing else changes. An application's arguments are evaluated before it, so an application that names `l` and
returns unscoped data keeps nothing of `l`: `scope l => useV(V.mk(l))` still leaves at type `Nat`.

## 3. Why the rule suffices

C1 by induction on values, with the existing rules:

| Value | Reaches | Counted by |
|---|---|---|
| Constructor application | its fields' atoms | the family's scope, the union of its lifetime parameters, which contains every field's type's scope (kernel.md "Inductives and matching") |
| Lambda | its captures' atoms, and the lifetimes its code names | the derived or written closure scope: captures by their types' sorts, lifetime locals by themselves (§2) |
| Function type | its components' atoms, and the lifetimes its binder types and codomain name | its sort's scope (§2) |
| A family instance or a sort, as a value | the lifetimes among its arguments, or its `scope` field | its sort's scope: a family names its lifetime parameters, and a sort's sort has its scope |
| A lifetime | — | never stored: no field or index has a sort parameter's type (kernel.md "Universes and function types"), so data holds a lifetime only in its type's arguments |
| Proof | — | a proof never runs; deferred evidence is evaluated from its callee's type and arguments, which are counted |
| Blocked computation | anything its code names | nothing: it never runs (§1's exception) |

The step that lemur2's lemma needed and Raccoon lacked is the lambda row: code is the one place a value holds a lifetime
without holding a value of a type that names it.

Implicit reconstruction reads an implicit off an argument's type, and that type's scope counts it. It is not a capture
(kernel.md "Universes and function types"), and needs none: a lambda can read an implicit at `l` only from an argument
whose type names `l`, which its domains then count, or from a capture, which counts. A review on 2026-09-28 withdrew
this rule over implicit reconstruction. Domains counting toward a function type's scope, and every family naming its
lifetime parameters, were adopted after it. §5 step 2 must re-examine that case rather than assume it closed.

## 4. What changes

- `stash` and `late` above are refused.
  - `stash` with `LifetimeEscapes` at its `scope`, whose type is now `{ scope = l } Unit -> Nat`.
  - `late` with `TypeMismatch`: its inner lambda now has type `{ scope = l } Unit -> Nat`, not the callback's written
    result `Unit -> Nat`. Writing that result instead names the callback's own binder, so `withLease`'s `A` cannot be
    reconstructed.
- `examples/leases/main.rac`'s `later` is refused the same way. It moves to the file's list of rejected variants.
- `ScopeTests`' "a value whose type's sort does not name the atom may leave its scope, even when it holds the atom": the
  closure cases become rejections. The stuck case (`count(n)` and `Eq.refl(count(n))`) stays accepted.
- Of commit `92950ef`'s acceptances, `Eq.refl(later)` goes with `later`; propositions about `withLease(f)` for a
  parameter `f`, and `congrArg` over `withLease`, stay accepted.
- Callbacks that name an enclosing lifetime get that lifetime in their closure scope. The library's combinators take
  `{ scope = Sf }` callbacks, which accept it; a callback checked against an arrow written without a closure is refused.
  §5 step 1 measures how often.

`kernel.md` "Scopes and atoms" loses the paragraph beginning "Evaluation never makes the check. A value computed under a
scope may leave it…", which C1 and C2 replace, and "a global value may hold an atom, though never a variable" becomes
"a global value holds an atom only inside a computation blocked forever". `language.md` "Closures" replaces "a variable
of `Kind` or `Lifetime` contributes nothing" with the lambda rule of §2, and "Scopes" replaces its `Unit -> Nat` example
with the refused `stash`. `LEMUR_ON_RACCOON.md` §4.2's "A lifetime is not a capability" is superseded.

## 5. Steps

1. **Measure.** Implement §2 in a worktree: `Interpreter.lambdaCaptures` and the derived scope admit lifetime locals,
   and `piClassifierFromChecked` adds the lifetime locals a function type's binder types and codomain mention. Run
   `sbt test` and `gpu/check.sh`. Classify every new rejection as intended (a value that reached an atom) or collateral
   (an arrow written without a closure). An implementer at medium effort.
2. **Attack.** A hostile reviewer at high effort tries to build a value that reaches an atom its type's sort omits:
   through implicit reconstruction, evidence, residual re-evaluation, destructuring, the eta view, packed literals, and
   two evaluations of one `scope` term.
3. **Land.** The kernel change, its tests (§4, with one admitted program and the smallest mutation reaching
   `LifetimeEscapes` or `ScopeExceeded` per row of §3), the amended documents, and `gpu/check.sh` green with the kernels
   byte-identical.

## 6. Decisions for review

1. **Function types count** the lifetimes their binder types and codomain name, rather than only lambdas. Without it,
   §2's `T` mints at a closed lifetime each time its codomain is instantiated.
2. **Mentions in types count**, as for other captures, rather than only term positions. It is the simpler rule and the
   conservative one: a type in a lambda's body is evaluated when the lambda runs.
3. **No restriction on minting**, such as lemur2's rule that only a scope primitive introduces authority for its region.
   After §2, a module minting at a bare lifetime cannot outlive the lifetime. Who may mint stays sealing's job.
4. **Atoms stay per term**, not per evaluation. C2 is stated for when no evaluation of the term is in progress, and
   activations are separated by parametricity, as today.
