# Proof by evaluation

Status: **approved design, not yet implemented** (review 2026-09-30). As each change lands, `docs/language.md` and
`docs/kernel.md` state its rules, and this document stays as the design record.

Proof by reflection proves a property in three steps:
1. Write a decision procedure in Raccoon, `check : D -> Bool`.
2. Prove it sound once, `sound : (d: D) -> Eq(Bool, check(d), Bool.true) -> Good(d)`.
3. Discharge each concrete instance by evaluation: `sound(d, Eq.refl(Bool.true))` checks when `check(d)` evaluates to
   `Bool.true`, because conversion compares the evaluated types.

It suits Raccoon, where conversion is evaluation, and it keeps automation out of the kernel: the procedure and its
proof are ordinary checked code. It is the plan for verifying the GPU library (`gpu/OBLIGATIONS.md` §8), whose
obligations are properties of data the library builds (a CUDA AST), so no reification of goals is needed.

Two things stand in the way today:
1. **Every instance must be written.** Every call site writes `Eq.refl(…)`, and a function cannot ask for a fact about
   its arguments without its callers proving it by hand. The GPU library already writes `Eq.refl(0)` for alignment
   and `Eq.refl(Bool.true)` for positivity.
2. **Evaluation does not scale.** Every walk over a term or a value is host recursion: a list of about 700 elements
   overflows the default stack, printing is quadratic, and exhaustion crashes the JVM with no diagnostic.

This document specifies:
- **evidence arguments**, discharged by evaluation at the call site (§1);
- **an evaluator that scales** to the data reflection runs over (§2).

§3 shows the two in use, §4 collects diagnostics and test obligations, and §5 records alternatives and the decisions
made in review. Both changes are in the trusted core (`docs/kernel.md`, "trust boundary"). Where this
document is silent on a case, the implementation stops and reports the gap rather than choosing.

## 1. Evidence arguments

**1.1 Syntax.** A binder `[h: P]` declares an evidence parameter. It may stand in a definition's parameter telescope,
a lambda's, a function type, or a constructor's (§1.8):

```raccoon
def storeAcc {n: Lifetime}{f: Nat}(e: Ctx(n, Group.warps(f, 4)))[aligned: Eq(Nat, Nat.mod(f, 4), 0)] … 

def render (p: Program)[ok: Eq(Bool, Gpu.wellFormed(p), Bool.true)]: String := …

struct Fin (n: Nat) : Type
 | mk (i: Nat)[h: Nat.lt(i, n)] : Fin(n)
```

`P` must be a proposition, a type whose sort is `Prop`; otherwise it is `NotAProposition`. `P` may mention only
earlier binders. At a call site an evidence argument is not written: `Gpu.render(p)`. It may be supplied explicitly
in a bracket group after the explicit arguments, `Gpu.render(p)[proof]`, with one proof per evidence binder, in
order.

**1.2 Discharge.** At an application whose evidence argument is omitted, the checker runs its telescope-order pass
(the pass that already evaluates each binder type once earlier arguments are known). When it reaches `[h: P]`, it
evaluates `P`, with every earlier argument known, to a value `P′`, and discharges `P′`, by one of two rules:
1. **Determined.** `P′` is an instance of an inductive family in `Prop` that has a constructor whose fields are all
   determined by its result type: each field is itself one of the arguments of the constructor's result type, so its
   value is read off `P′` at that position (a field inside an argument, as `x` in `F(g(x))`, cannot be read back), and
   the constructor applied to those values has a result type convertible with `P′`. The proof is
   that application. A fieldless constructor is the case with no fields to read.
2. **Through evidence fields.** `P′` is an instance of an evidence-eligible family (§1.9), and each of its constructor's
   evidence fields, in order, has a proposition that, evaluated with `P′`'s arguments, discharges in turn. The proof is
   the constructor applied to those proofs.

`Eq(A, l, r)` is discharged exactly when `l` and `r` evaluate to convertible values: `Eq.refl`'s field `x` occurs in
its result type `Eq(A, x, x)`, so it is read off `P′` as `l`, and `Eq(A, l, l)` must be convertible with `Eq(A, l, r)`.
`True` is discharged by `True.intro`, which has no fields. A family whose every constructor has a field that its
result type does not determine (`And`, `Or`, `Exists`, an inductive `Le`) is never discharged by this rule, since that
field would have to be invented. This is what makes discharge sound without checking fabricated fields:
`ProofReconstruction` fabricates proof fields unchecked, so "reconstructs to some constructor" would accept
`And(False, False)`, while every field read off `P′` is a value `P′` already holds, and the conversion check validates
the whole.

Otherwise the application is `EvidenceNotDischarged`, reported at the application. It shows the proposition that
failed, as evaluated, and, if it was reached through evidence fields, the path of fields to it. For example
`GemmShape.nOk: Eq(Nat, 192, 128)` names the conjunct that failed, and `Eq(Bool, Bool.false, Bool.true)` shows which
check did. A `P′` that stays neutral, as it does in generic code that knows no concrete arguments, is not discharged
either.

**1.3 Explicit evidence.** A supplied evidence argument is checked against `P` as any argument is. It is how generic
code forwards a proof it has: inside a function with `[h: P]`, a call that needs `P` passes `[h]`. Supplying the wrong
number of evidence arguments is `ArityMismatch` (counting evidence).

**1.4 Locality.** Evidence comes from the callee's type and the call's other arguments, never from the expected type,
the same locality as forced implicits (`docs/kernel.md`, invariant 13). Checking stays synthesis followed by
equality. Nothing is searched for:
- the constructor, if several fit rule 1, is the first declared, and proof irrelevance makes the choice
  unobservable;
- no hypothesis in scope is consulted (§5.2).

**1.5 Types.** The evidence mode is part of a function type's identity, as implicitness is. `[h: P] -> A` and
`(h: P) -> A` are different types, and unification compares modes. A lambda `fun [h: P] => …` has an evidence
binder.

An evidence binder is not an explicit parameter: it does not count for arity, and since forcing projects implicits
from explicit arguments' types, it forces nothing.

An unforced implicit binder of a proposition stays `NonForcedImplicitParam`, whose message points to `[h: P]`.

**1.6 Evaluation.** Proofs are erased at run time (proof collapse, `docs/kernel.md`). Running a function binds its
evidence parameters to erased proofs without evaluating their propositions, so a decision procedure runs at check
time only, once per application, and never when the program runs. The checker caches `P′` for the application
rather than evaluating it again for the result type.

**1.7 Decidability.** Discharge evaluates and compares, and never searches: rule 1's constructor is chosen as §1.4
says, and an evidence-eligible family has one constructor. It terminates (§1.9), so checking still does. Its running
time now includes the decision procedures that programs call, which are total but may be costly: evaluation may
duplicate a proposition, so discharge through evidence fields can take time exponential in their nesting. That is
the point of the feature, and why §2 matters.

**1.8 Evidence fields.** A constructor's evidence binder is an evidence field. Constructing is applying, so at a
construction an evidence field is discharged or supplied exactly as an evidence argument is: `Fin.mk(3)` at
`Fin(5)` discharges `Nat.lt(3, 5)`, `Fin.mk(3)` at `Fin(2)` is `EvidenceNotDischarged`, and generic code writes
`Fin.mk(i)[h]`. An evidence field is a stored proof field:
- patterns and destructuring bind it in order among the stored fields, `| Fin.mk i h =>` and `let (i, h) := x`;
- a struct selector returns it, `x.h`;
- it takes part in the eta view as proof fields do, and, proofs being irrelevant, two values that differ only in an
  evidence field are equal.

Its proposition may mention the family's parameters and earlier fields, and is checked as any field's type is
(positivity, universes). For §1.2's first rule an evidence field is a field like any other: a constructor whose evidence field its result type
does not determine is not used by that rule.
At run time, as in §1.6, a construction stores an erased proof without evaluating the proposition. Implicits written
on a constructor must still be forced; an evidence field is not an implicit and needs no forcing.

**1.9 Termination of discharge.** A family `F` is **evidence-eligible** when:
1. `F` is in `Prop`, has one constructor and no indices (a `struct`);
2. `F` is not recursive: no field's type mentions `F` or a member of its mutual block;
3. every field of its constructor is an evidence field.

§1.2's second rule applies to an instance `F(ā)` of an eligible family only when its arguments `ā` are first-order:
those that are not types or propositions contain no function. Otherwise only the first rule is tried. This is checked
on the evaluated arguments at discharge.

Discharge then terminates. The obligation is to prove it, and the proof is to be written out in `docs/kernel.md` when
this lands. Its argument:
- Order the program's symbols (families, constructors, definitions) by declaration, a well-founded order, since
  Raccoon requires declaration before use. A closure counts as the symbol of the definition whose code built it, and
  literals as minimal constants.
- A discharge step goes from `F(ā)` to `Qᵢ`, the value of the i-th field's type evaluated with `ā` (and earlier fields'
  proofs, which are erased). By condition 2 and declaration before use, that type mentions only symbols declared
  before `F`, so its evaluation runs only code declared before `F`.
- That code cannot run code declared after `F`: a parameter that is a type or proposition can be copied but not
  inspected (Raccoon has no case analysis on types), and the other parameters contain no function to apply. So `Qᵢ`
  is built from symbols declared before `F` and from copies of subterms of `ā`.
- Such a `Qᵢ` is smaller than `F(ā)` in the recursive path ordering whose precedence is declaration order: `F` exceeds
  every symbol built around the copies, and each copy is a subterm of `F(ā)`. That covers duplication, as in a field
  `[a: Both(p, p)]`, and descent into a parameter, as in `Both(Both(X, Y), Z)`. The recursive path ordering over a
  well-founded precedence is well-founded (Dershowitz), so no chain of discharge steps is infinite.
- Each step's evaluation is total, and the base case, rule 1, is a conversion check between closed values, which
  terminates.

What the conditions exclude:
- `inductive Loop : Prop | mk [h: Loop]` fails condition 2.
- `struct App (f: Nat -> Prop)(n: Nat) : Prop | mk [a: f(n)]` has a function among its arguments. Both are discharged
  by rule 1 only, and so, having no constructor whose fields its result type determines, not at all.

As defence in depth, the implementation also bounds the depth of discharge, and reports `EvidenceNotDischarged` if
the bound is reached. Under the proof the bound is never reached, and a test pins that.

## 2. Evaluation that scales

**2.1 The defects.** Measured on `lemur_gpu` at d9eb2c7, GraalVM 21, macOS aarch64:

| Workload | Default 2MB stack | 64MB stack | Where it fails |
|---|---|---|---|
| summing a list, non-tail recursion | ~700 elements | ~25k | interpreter recursion, about 9 host frames per call |
| summing a list, accumulator (tail) recursion | ~920 | ~32k | the same: no tail calls |
| `Eq.refl(Bool.true)` against a check over a list | ~690 | ~31k | interpreter recursion |
| a list published as a global | ~3.3k | ~112k | `synDeps` walk (`Env.assertClosedGlobal`) |
| comparing two big lists | ~1.3k | ~43k | `synDeps`, then key assertion's structural walk |
| printing a list or a computed `String` | ~2.2k | ~100k, quadratic time | `PrettyPrinter.print` |

`gpu/examples/gemm.rac` checks at the default stack and then overflows printing its 3,358-character result. Stack
exhaustion is not caught: the JVM crashes with no diagnostic and no location. Closed arithmetic on literals is not
affected, since native operations compute on `BigInt`.

**2.2 Printing.** `PrettyPrinter.print` becomes iterative, with an explicit work stack and a single output buffer, and
linear in its output. A `String` value whose characters are all known prints as a string literal whether it was
written or computed; today only a written literal does. The CLI gains `--raw`: a `String` result prints as its
characters, unquoted and unescaped. Code generators then need no post-processing: `gpu/gen.sh` drops `render.py`.

**2.3 Value metadata at construction.** A value's `synDeps`, `key` and `needsStructuralDefEq` are computed when the
value is built, in constant time from its children's, instead of lazily by a walk. Publishing a global, materializing,
and deciding equality by key then do no deep walks. The key-assertion check (on by default) keeps re-deriving every
key-decided equation structurally, but with an explicit work stack.

**2.4 Tail positions run in a loop.** `evalTerm` loops, instead of recursing, when the term to evaluate next is its
result:
- a block's result;
- a match's chosen branch;
- a scope's body;
- the body of a core lambda applied in tail position.

A procedure written with accumulators, using `match` rather than `Bool.and` for short-circuiting (evaluation is
strict), runs in constant host stack. Recursion that is not in tail position remains bounded by the stack.

**2.5 Exhaustion is a diagnostic.** Checking and evaluation run on a dedicated thread whose stack is set by a
`--stack` flag (default 256MB). A stack overflow is caught at the boundary of the declaration being checked or the
program being evaluated, and reported as `EvaluationTooDeep` at that declaration. Checking then stops, since the
pipeline's global state (fresh-name counters, the linear-subterm table) is not safe to continue from.

**2.6 Targets.** At the default JVM stack of the launching process:

| Workload | Target |
|---|---|
| print a computed `String` of 1,000,000 characters, `--raw` | < 1 s, no overflow |
| publish, and compare by `Eq.refl`, two separately built lists of 1,000,000 elements | no overflow |
| an accumulator-style check over a 1,000,000-element list, discharged as evidence | constant stack, < 2 s |
| non-tail recursion | limited by `--stack` alone; exhaustion is `EvaluationTooDeep` at the declaration |
| `gpu/gen.sh` on every GPU example | no `-Xss`, no `render.py`, output byte-identical |

**2.7 Not done.**
- **A full explicit-continuation (CEK) machine.** The evaluator is re-entered from the checker, the unifier, native
  bodies and Pi codomains, and deep values are a second source of depth (§2.3), so a CEK evaluator alone would not
  suffice. §2.2–2.5 remove each measured source directly.
- **Raising `MaxUnfoldedLiteral`.** It concerns only symbolic arguments.
- **Native list operations.** That would add trusted surface with T5-like obligations.

## 3. In use

The reflection pattern, with a procedure over unrestricted data (`All` is a user-defined family, the proposition that
every element satisfies a predicate):

```raccoon
def allBelow (xs: List(Nat))(n: Nat): Bool := …          // a decision procedure

def allBelowSound (xs: List(Nat))(n: Nat)[h: Eq(Bool, allBelow(xs, n), Bool.true)]
    : All(xs, fun (x: Nat): Prop => Nat.lt(x, n)) := …    // proved once, by induction on xs

def ok : All(big, fun (x: Nat): Prop => Nat.lt(x, 4096)) := allBelowSound(big, 4096)   // discharged by evaluation
```

Two uses in the GPU library:
- The library's `Eq.refl(0)` and `Eq.refl(Bool.true)` arguments become evidence binders that callers never write.
- `Gpu.render` takes `[ok: Eq(Bool, Gpu.wellFormed(p), Bool.true)]`, which is discharged when a client renders its
  concrete kernel. Every printed kernel then carries a checked certificate of `gpu/OBLIGATIONS.md`'s structural
  invariants, and `sound` turns it into their statement.

Propositions are stated over unrestricted data: `Eq` takes unrestricted types, so a procedure inspects a kernel's
AST, which is data, not the linear tokens that built it.

## 4. Diagnostics and test obligations

```text
EvidenceNotDischarged
EvaluationTooDeep
NotAProposition
```

All three are new: `EvidenceNotDischarged` (§1.2), `EvaluationTooDeep` (§2.5), and `NotAProposition` for an evidence
binder whose type is not a proposition (§1.1). Existing diagnostics gain cases:
- `ArityMismatch`: the wrong number of explicit evidence arguments (§1.3);
- `TypeMismatch`: an explicit evidence argument of another proposition, and a function type whose binder modes
  differ (§1.5).

A bracket group that is empty or follows no application is a parse error.

Every rule is a test obligation: one program it admits, and the smallest mutation that reaches its named diagnostic
and no earlier one. Beyond those:
- **Soundness of discharge.** `EvidenceNotDischarged` for `False`, `And(True, True)`, `Exists(…)`, an `Eq` whose sides
  differ, and a proposition that stays neutral. `And(True, True)` is the case that separates "determined" from
  "reconstructs".
- **Discharge through evidence fields.**
  - `Both(True, Eq(Nat, 2, 2))`, a nested `Both(Both(…), …)`, and a field that duplicates a parameter
    (`[a: Both(p, p)]`) are discharged.
  - A failing field is reported with its path, depth first in field order.
  - `Loop` (recursive) and an `App`-style family applied to a function are refused promptly, without a hang.
  - A multi-constructor family whose constructors have only evidence fields is not recursed into.
  - The depth bound is not reached anywhere in the suite, and a direct test of the bound covers the report.
- **Evidence fields.**
  - `Fin.mk(3)` at `Fin(5)` is discharged; at `Fin(2)` it is `EvidenceNotDischarged`.
  - Generic `Fin.mk(i)[h]` works.
  - A match, a destructuring and a selector each bind the proof.
  - Two `Fin` values with equal `i` are equal.
  - Constructing in a run-time loop evaluates no proposition.
- **Generic code.** Discharge fails where `P` is neutral; forwarding `[h]` works; a caller with concrete arguments
  discharges.
- **Run time.** A program that calls an evidence-taking function in a loop runs no decision procedure. Pin it with a
  procedure whose cost would dominate the run.
- **Types.** `[h: P] -> A` and `(h: P) -> A` do not unify; a higher-order argument keeps its evidence mode.
- **Forcing.** `def f {n: Nat}[h: Eq(Nat, n, 3)]: …` is `NonForcedImplicitParam`: an evidence binder, supplied or
  not, is no source for forcing.
- **§2.6's targets**, as tests where they are cheap enough. The rest are measured by hand and recorded in this
  document, until a benchmark suite exists.
- **The GPU library as client.** `storeAcc`'s alignment, `tiledKernel`'s positivity and `ceilDivC`'s divisor become
  evidence, and `gpu/check.sh` stays green with its generated kernels unchanged.

## 5. Decisions and alternatives

1. **A new binder mode, not a reinterpreted `{h: P}`.** Making an unforced implicit proposition mean evidence would turn
   today's definition-site error into call-site behaviour and blur two mechanisms. `[ ]` is free since the
   instance-binder syntax was removed.
2. **No hypothesis lookup.** Discharging from a proof in scope of a convertible proposition would be deterministic,
   since proof irrelevance makes the choice unobservable, but it is a search over the context. Explicit forwarding
   (§1.3) covers generic code; lookup can be added later without changing what any program means.
3. **Recursive discharge through evidence fields only, of eligible families only** (§1.2, §1.9).
   - **Through evidence fields.** Ordinary fields, as in `And(P, Q)`, are never discharged: that would guess what a
     field means.
   - **Eligible families only.** One constructor means no search. Non-recursion and first-order arguments give the
     termination proof.
   - **Why not rule 1 alone.** Adopted in review over that alternative for its diagnostics, which name the failing
     conjunct. It only adds programs that are accepted: nothing rule 1 alone accepts changes meaning.
   - **Rule 1 reads determined fields.** In implementation, "fieldless" was found to exclude `Eq.refl`, whose field
     occurs in its result type, contradicting the rule's own example. Rule 1 was corrected to read such fields off
     `P′`: that invents nothing, which was the point of "fieldless".
4. **Reflection before tactics.** Metaprogramming (elaboration-time Raccoon programs building terms) is the route to
   automation for goals that are not about data. It is left for when layer 3 of `gpu/OBLIGATIONS.md` §8 needs it.
5. **Key assertions stay on.** They become iterative (§2.3); turning them off by default in the CLI would change a
   documented default of the trusted core.
6. **Constructors carry evidence uniformly** (§1.8). Constructing is applying, so no new mechanism is needed. An
   evidence field is stored, so a match recovers the fact its value certifies.
7. **Settled in review:**
   - explicit evidence is written `f(x)[h]`;
   - `--stack` defaults to 256MB (a native-image build must be checked to honour it, if Raccoon ships as one);
   - the raw output flag is `--raw`.
