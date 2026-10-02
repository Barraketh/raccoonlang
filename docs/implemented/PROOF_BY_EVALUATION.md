# Proof by evaluation

Status: **approved design, partly implemented** (review 2026-09-30). Implemented: §1 (evidence arguments and fields,
both discharge rules, the depth bound), §2.2 (printing), §2.3 (value metadata), §2.4 (tail positions), §2.5 (stack
exhaustion). Open: the §2.6 measurements. `docs/language.md` and `docs/kernel.md` state the implemented rules, and
this document stays as the design record.

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
construction an evidence field is discharged or supplied exactly as an evidence argument is: `Fin.mk(5, 3)`
discharges `Nat.lt(3, 5)`, `Fin.mk(2, 3)` is `EvidenceNotDischarged`, and generic code writes `Fin.mk(n, i)[h]`.
(`Fin`'s parameter `n` is an explicit argument of `Fin.mk`: it occurs only in the evidence field's proposition, which
forces nothing.) An evidence field is a stored proof field:
- patterns and destructuring bind it in order among the stored fields, `| Fin.mk i h =>` and `let (i, h) := x`;
- a struct selector returns it, `x.h`;
- it takes part in the eta view as proof fields do, and, proofs being irrelevant, two values that differ only in an
  evidence field are equal.

Its proposition may mention the family's parameters and earlier fields, and is checked as any field's type is
(positivity, universes). For §1.2's first rule an evidence field is a field like any other: a constructor whose evidence field its result type
does not determine is not used by that rule.
At run time, as in §1.6, a construction stores an erased proof without evaluating the proposition. Implicits written
on a constructor must still be forced; an evidence field is not an implicit and needs no forcing.

**1.9 Termination of discharge.** A family `F` is **evidence-eligible** at a discharge site when:
1. `F` is declared in `Prop`, and has one constructor
   and no indices (a `struct`);
2. `F` is not recursive: no field's type mentions `F` or a member of its mutual block;
3. every field of its constructor is an evidence field;
4. its constructor is accessible at the site: a sealed family's only in its module, as for rule 1.

Rule 2 applies to any instance `F(ā)` of an eligible family, whatever its arguments: they may be open, and may hold
functions, as in `Both(All(xs, fun (x: Nat): Prop => …), Q)` or `struct App (f: Nat -> Prop)(n: Nat) : Prop | mk [a:
f(n)]`.

**The depth bound.** Discharge counts the rule-2 steps on its current path, from the application's `P′` to the
proposition being discharged. A proposition that would be discharged by a rule-2 step at depth greater than
`N = 1024` is not discharged: the application is `EvidenceNotDischarged`, which reports the path and that the bound was
reached. The bound is part of what a program means, fixed by the language and not by a flag, so that whether a program
checks does not depend on how it is run.

Discharge then terminates, by a direct argument:
- each step evaluates a field's proposition, and evaluation is total;
- an eligible family's constructor has finitely many fields, so each step has finitely many successors;
- no path is longer than `N`, so the tree of steps is finite (König);
- rule 1 at a leaf is a conversion check between two values, which terminates.

Nothing here needs an ordering on terms, so nothing restricts the arguments. Conditions 1 to 4 are not needed for
termination either. They make rule 2 what §5.3 says it is: a step picks no constructor (condition 1), recurses only
where a field is evidence (condition 3), and respects sealing (condition 4). Condition 2 makes the one case that could
only ever reach the bound, a family nested in its own field, not eligible at all, so `inductive Loop : Prop | mk [h:
Loop]` is refused at once, as a proposition rule 1 cannot discharge.

The bound limits nesting, not work: evaluation may duplicate a proposition, so a tree of depth `d` may have
exponentially many leaves in `d` (§1.7). Nesting deeper than `N` needs a proposition built that deep, such as a chain
`Wrap(Wrap(…))` computed by a recursive definition, and such a proposition is a proof obligation for a lemma, not a
case for discharge.

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
strict), runs in constant host stack. **Current implementation:** the unified frame evaluator also stores non-tail
Core calls and pending expression work in explicit frames. The host-stack bounds measured in this historical proposal
no longer describe Core call depth; checker and semantic-helper recursion can still overflow and yield
`EvaluationTooDeep` at the same diagnostic boundaries.

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
BuiltinEvidence
```

All four are new: `EvidenceNotDischarged` (§1.2, with the path through evidence fields and, past the bound, the
reason `TooDeep`, §1.9), `EvaluationTooDeep` (§2.5), `NotAProposition` for an evidence binder whose type is not a
proposition (§1.1), and `BuiltinEvidence` for an evidence binder in a builtin's signature, since a builtin's native
body reads its arguments as values and nothing would force an erased proof for it. Existing diagnostics gain cases:
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
  - `Loop` (recursive) is refused at once, without being recursed into.
  - An `App`-style family applied to a function, and `Both` over a proposition that holds a function, are discharged
    when their fields are.
  - A multi-constructor family whose constructors have only evidence fields is not recursed into.
  - The bound: a chain `Wrap(Wrap(…(True)))` of `N` eligible steps is discharged, and one of `N + 1` is
    `EvidenceNotDischarged`, reporting the bound; the bound is not reached anywhere else in the suite.
- **Evidence fields.**
  - `Fin.mk(5, 3)` is discharged; `Fin.mk(2, 3)` is `EvidenceNotDischarged`.
  - Generic `Fin.mk(n, i)[h]` works.
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
   - **Eligible families only.** One constructor means no search, and only evidence fields are recursed into.
   - **Why not rule 1 alone.** Adopted in review over that alternative for its diagnostics, which name the failing
     conjunct. It only adds programs that are accepted: nothing rule 1 alone accepts changes meaning.
   - **Rule 1 reads determined fields.** In implementation, "fieldless" was found to exclude `Eq.refl`, whose field
     occurs in its result type, contradicting the rule's own example. Rule 1 was corrected to read such fields off
     `P′`: that invents nothing, which was the point of "fieldless".
   - **Termination by a depth bound, not by an ordering.** The approved version proved termination with a recursive
     path ordering on declaration order, which needed rule 2's arguments to be first-order. Implementation review found
     two gaps in it, each where code could run a function that the ordering did not account for: inference reading a
     function from a proof's proposition, and code opening a proof among the arguments by a cast to read its stored
     proofs, whose propositions are only convertible with what the code computes. The first was repaired by requiring
     the arguments to be closed and function-free everywhere; the second would have needed a further condition and a
     lemma, that conversion of closed function-free values is equality of normal forms, which the kernel does not
     state. A bound on nesting gives termination in four lines, and so the argument conditions went too: rule 2 now
     applies to propositions over functions. The costs are a constant in the semantics, and that an eligible
     proposition nested deeper than `N` is not discharged, which in practice means one built by recursion.
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
