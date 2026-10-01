# A match that names its equation

Status: **implemented** (2026-10-01). A quality-of-life feature for `gpu/proofs/NOTES.md` F2 ("no `inspect`") and
`gpu/encoding/NOTES.md` item 3 ("no dependent `if` for evidence").

## 1. The feature

`match h : e returning M with …` binds `h` in every case. In the case for constructor `C` with fields `x̄`:

```text
h : Eq(T, e, C(p̄, x̄))
```

Here `T` is `e`'s type, `p̄` its parameters, and `e` the scrutinee as written. Nothing else changes: the cases, the
motive and coverage are as for `match e`.

The point is that a computed value's case knows what it was computed from. A function that needs a fact about `c` can
branch on the test and pass the equation on:

```raccoon
// Loads columns 8c … 8c+7 of every chunk from c on, while 8(c + 1) ≤ n: loadAcc8 needs that fact as evidence.
def loadFrom (…)(c: Nat)(left: Nat): … decreases structural(left) := {
  match left returning … with
  | Nat.zero => done
  | Nat.succ more => {
    match fits : Nat.ble(Nat.mul(8, Nat.succ(c)), n) returning … with
    | Bool.true => { let (e, v) := loadAcc8(e, ring, full, c)[fits]  … loadFrom(…, Nat.succ(c), more) }
    | Bool.false => done
  }
}
```

`Nat.le(a, b)` is `Eq(Bool, Nat.ble(a, b), Bool.true)`, so `fits` is exactly the evidence `loadAcc8` asks for. Today
the library writes the 16 calls out, because evidence is discharged by evaluation only at literal indices.

The same form gives proofs the equation F2 asks for, in place of a mirror definition per match.

## 2. The rules

- **Unrestricted scrutinee.** The scrutinee's type must be unrestricted. A linear scrutinee would put a token in a
  proposition, which is `LinearInType`.
- **No indices.** The scrutinee's family has no indices, so `C(p̄, x̄)` has type `T` in every case and the equation is
  well typed without refinement. An indexed family is `MatchEquationIndexed`, located at `h`. Allowing it is an
  extension: the equation would be stated at the case's refined type.
- **`h` is a proof, used freely.** It is a local of a proposition, so it is unrestricted, and it is confined like any
  local by its type's scope.
- **No rewriting.** The motive and other hypotheses are not rewritten by the equation. A proof that needs `e` replaced
  uses `h` with `Eq.subst`. Rewriting the goal is a larger feature, and a separate one.
- **Evaluation.** A case runs only when the scrutinee's value is `C` applied to the fields' values. There `h`'s
  proposition is `Eq(T, C(p̄, v̄), C(p̄, v̄))`, and `h` is bound to its canonical proof, `Eq.refl`, as every proof is
  canonicalized. A match that blocks binds nothing.
- **Residual.** The checked match keeps `h`. A residual prints as `match h : e`.

## 3. Why it is safe

`h` adds a hypothesis to each case, and that hypothesis is true whenever the case runs: the scrutinee's value is that
constructor applied to those fields, so the equation holds by reflexivity.
- **Checking.** A case is checked with its fields and `h` as locals. Any proof built from `h` is a proof of something
  that holds in every run of that case.
- **Unreachable cases.** When no run reaches the case, `h` is an unprovable hypothesis in an unreachable branch, which
  is how a case is already checked against impossible field values.
- **No new reduction.** Evaluation never reduces by `h`; it is a canonical proof like any other.

## 4. Implementation

- **Parser:** `match ident : term returning …`.
- **Surface and Core ASTs:** `Match.equation`, the equation's local and where it is written.
- **Elaborator:** binds `h` in every case's scope, after the fields.
- **`MatchChecker`:** in each case, binds `h` at `Eq(T, scrutinee, C(p̄, x̄))`, built from the checked scrutinee and the
  case's fields, then checks the body. `MatchEquationIndexed` and the linearity rule are checked once, at the match.
- **Evaluation:** binds `h` to the canonical proof, deferred like evidence, when a case is taken.
- **Printer.**
- **`Eq`:** the trusted prelude's, validated at the end of prelude loading as exactly the equality family
  (`docs/kernel.md#equality`), so a module's own `Eq` cannot make `h` false. Without one, and in the prelude's own
  declarations, a named equation is `MatchEquationUnavailable`.
- **Combined with a wildcard case** (`docs/WILDCARD_CASE.md`): each expanded case gets its own `h` at its own
  constructor.

## 5. Tests

- The `loadFrom` pattern: a structural recursion that passes `fits` as evidence. The recursion checks and evaluates;
  without `fits` it is `EvidenceNotDischarged`.
- F2's example: `t` proved with `match h : Nat.isZero(n) …` and `Eq.subst`.
- An indexed family: `MatchEquationIndexed`.
- A linear scrutinee: rejected.
- `h` on a blocked match: nothing bound, no evaluation of the branch.
- A wildcard case with an equation: each expansion's `h` names its constructor.
- The residual prints `match h : e`.

## 6. Decisions

1. **The syntax `match h : e`**, rather than `match e as h` or a separate `inspect` function.
2. **No indexed families yet** (`MatchEquationIndexed`), rather than a heterogeneous or refined equation now.
3. **No goal rewriting.** The equation is a hypothesis, and `Eq.subst` uses it.
