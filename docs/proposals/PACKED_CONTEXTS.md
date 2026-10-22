# Packed contexts and step acceleration

Status: proposal, 2026-10-05. Not implemented.

This consolidates and replaces `COMPACT_NAT_VALUES.md`, which was folded in
on 2026-10-05. Its representation, matching and native-arithmetic rules are
replaced by §1, §2 and §4. Its live requirements are restated here: the
integration invariants (§1), the conversion of residual operations (§4) and its
validation.

## Purpose

Packed Nats currently get their behaviour on symbolic arguments from rules
written by hand in `Packed.nativeOp` (`compact`, `compare`, the `blt`
delegation). Anything those rules miss becomes an opaque residual. Then
`ValueEquivalence` reconciles residuals with the source definitions by
inspecting one layer of the source, and it does so during conversion only.
Nothing states which equations hold. Where a rule is missing, evaluation is
weaker than the source definition. For example,
`Nat.sub(Nat.succ(Nat.succ(x)), 1)` is `Nat.succ(x)` by the source. Reading
`compact`, it should stay a residual, so a `match` on it would be stuck. This
was found by reading the code, not by running it; validation item 3 confirms
it.

This proposal replaces those rules with three general mechanisms:

1. one compact representation for every symbolic Nat built from `succ` and
   `Nat.pred` (§1);
2. step summaries: each is derived once per declaration by evaluating one
   recursive layer, and lets evaluation take many layers of a structural
   recursion at once (§2);
3. tail calls modulo a context: a recursive call wrapped only in constructors
   runs as a tail call, and the wrapping is kept as one compact pending
   context instead of one frame per layer (§3).

Polynomial normal forms for `+` and `·` are planned as a follow-up (§6).
Unlike everything else here, they extend definitional equality.

Principle: **the checked source definitions decide definitional equality.**
Packing, summaries and native code change only how fast a value is reached,
never which value is reached. For every summarized function, the result is
exactly what ordinary eager evaluation of the source gives. Evaluation stays
eager. The magnitude of a number never selects a different rule.

## Current state

The working tree implements the compact Nat design that this proposal replaces:

- a compact successor prefix, `VNatPrefix`, built only by `Packed.natPrefix`. It
  represents `succ^offset(base)` with a `BigInt` offset;
- one constructor view over packed literals and prefixes
  (`Packed.natConstructorParts`);
- no `Packed.MaxUnfoldedLiteral`, so the magnitude of a literal no longer
  chooses between source unfolding and an opaque native call;
- per-operation rules for symbolic arguments in `Packed.nativeOp`, with other
  symbolic calls left as residuals;
- one-layer inspection of the exact checked source during conversion
  (`NativeEquation`).

That work was motivated by `NatBoundConversion.rac`. That file checked with 256
but failed with 257, because a native call made after refinement became opaque
under `MaxUnfoldedLiteral`. The real ring bound failed at 9216.

Measured on 2026-10-05, with the committed HEAD (`bfa2bc3`) against the working
tree:

| Check in `../lemur-raccoon` | HEAD | Working tree |
|---|---|---|
| `probes/NatBoundConversion.rac` | fails | passes |
| `probes/RingStorageBound.rac` | fails | passes |
| `probes/NativeNatOccurrence.rac` | passes | passes |
| `probes/NatBltSuccessor.rac` | passes | fails |
| `gpu/proofs/SharedMemory.rac` | passes | fails |
| `gpu/proofs/WellFormed.rac` (imports `SharedMemory`) | passes | fails |

- **Storage reproducer.** It once failed in `Regions.Layout.reserve`, because
  positivity checking rejected its index `Nat.add(base, bytes)` as a native
  residual.
  [Declaration-time positivity](../implemented/DECLARATION_TIME_POSITIVITY.md)
  replaced that check, and the reproducer now passes. The storage proofs
  themselves have not been re-run.
- **`Nat.blt(0, Nat.succ(m))`.** The compact-Nat rules introduced this
  regression; HEAD checks all three of the files that now fail. §2 and §4 remove
  those rules. Validation item 10 requires all three to check again.

The goals stay the same:

- eager evaluation, ordinary `zero`/`succ` elimination and structural
  induction;
- one representation and one reduction policy for small and large numbers;
- the GPU library's storage proof resumed without an unfolding lemma, and
  without changing its obligations.

## Terms

- **Push**: one `Nat.succ`. **Pop**: one application of the validated
  `Nat.pred`.
- **Context** `[k, j]`: pop `k` times, then push `j` times. `k` and `j` are
  non-negative `BigInt`s. On a closed number `n` it gives `(n ∸ k) + j`, where
  `∸` is truncated subtraction (`Nat.sub`).
- **Context value** `[k, j]·e`: a context applied to a neutral Nat `e`, its
  **base**. It stands for `succ^j(pred^k(e))`.
- **Known successors** of a Nat value: `n` for the literal `n`, `j` for
  `[k, j]·e`, and `0` for any other value.
- **Layer**: one entry into a recursive function's body, up to its recursive
  call.
- **Guard**: a parameter that the summarized layer requires to start with
  `succ`.
- **Closed jet**: a native implementation used only when every argument is a
  closed packed value.
- **Residual**: the opaque application `VApp(native, args)` that a native
  operation returns today when no rule applies.
- **Context builder**: an application of a constructor, or of the validated
  `Nat.pred`, considered with its last argument still to be evaluated.
- **Context position**: the last argument of a context builder that is itself
  in tail position or in a context position.
- **Pending context**: the composition of the context builders a frame still
  has to apply to the value it returns.

## 1. Context values

### Algebra

Applying `[k1, j1]` and then `[k2, j2]` gives:

- `[k1, j1 − k2 + j2]` when `j1 ≥ k2`;
- `[k1 + k2 − j1, j2]` otherwise.

The `t`-th power of `[k, j]`, for `t ≥ 1`, is:

- `[k, t·(j − k) + k]` when `j ≥ k`;
- `[t·(k − j) + j, j]` otherwise.

This is the bicyclic monoid: pop after push is the identity, but push after pop
is not. `succ^j(pred^k(e))` is a normal form for a neutral `e`, because `pred`
is stuck on `e` and nothing reduces an outer `succ`. The composition and power
formulas were checked exhaustively against direct application: for every
context with counts below 12, for powers below 15, and against every word of up
to 8 pushes and pops.

### Smart constructor

One constructor, `natContext(v, [k, j])`, is the only way to build these values:

- `[0, 0]` returns `v`;
- a literal `n` returns the literal `(n ∸ k) + j`;
- a context value `[k0, j0]·e` combines contexts:
  `natContext(e, [k0, j0] then [k, j])`;
- any other Nat value `e` builds the node `[k, j]·e`.

So a node's base is never a literal, a context value or a constructor
application, and every value has exactly one representation. Counts are
`BigInt` throughout, and no count passes through `Int` or `Long`. `VNatPrefix`
becomes the node with `k = 0`. `Packed.natPrefix` and the `succ` case of
`foldCtor` call `natContext(v, [0, j])`.

### `Nat.pred`

Nat family validation also validates the trusted `Nat.pred`. It must have
exactly one parameter and one match on that parameter, with `zero ↦ zero` and
`succ p ↦ p`. Its published value then applies as `natContext(v, [1, 0])`. This
is the same way native operations attach to their published lambdas. No other
code path builds `pred`'s stuck match, so every stuck `pred` is a context node.

### Matching, projection, termination

One constructor view serves evaluation, checking, projection, implicit readout
and termination:

- literal `0`: `Nat.zero`;
- literal `n > 0`: `Nat.succ` with predecessor `n − 1`;
- `[k, j]·e` with `j > 0`: `Nat.succ` with predecessor
  `natContext(e, [k, j − 1])`;
- `[k, 0]·e` with `k > 0`: blocked on `e`'s blockers;
- any other neutral: blocked.

Structural termination treats `natContext(e, [k, j'])` for any `j' < j` as a
strict subterm of `[k, j]·e`. When `k = 0`, `e` is one too. When `k > 0`, `e`
is **not** a subterm, because `pred` is not a constructor. Distinct bases are
never ordered by comparing counts. Structural descent keeps its existing
treatment of function applications of subterms, and of other inductives.

No consumer allocates a successor chain to inspect a context value.
Constructing `Nat.succ` uses the same smart constructor.

Implicit readout sees the same successor fields. A repeated predecessor path is
one `BigInt` count, and compiling or following it never enumerates the prefix.
Readout keeps the checked constructor and seal requirements of ordinary field
readout, and grants no inverse rule for arithmetic.

### Conversion and unification

- Two context values are equal exactly when their bases are equal and their
  contexts are identical. Because construction is canonical, this test is exact.
- Against a literal or another value with known successors, strip the common
  pushes in one step and compare what remains. This is the existing prefix
  rule.
- `[0, j]·?m ≡ n` with `n ≥ j` solves `?m := n − j`, as today.
- Pops are never inverted, because `pred` is not injective
  (`pred 0 = pred 1`). An equation with a pop over a blocked base postpones.
  Over a rigid base it compares structurally.
- If conversion compares a pop with a neutral that is not a context value, it
  unfolds one pop into `Nat.pred`'s checked match and compares that. The outcome
  is then what the source definition gives.

### Integration

- **Participation.** Context values take part in dependencies, blockers,
  occurrence and positivity summaries, materialization, equality keys,
  structural comparison, printing, constructor reconstruction and matching.
  Their dependencies, blockers and occurrence summaries are those of the base.
- **Keys.** They are built from the base key and both counts, and they obey the
  key-coherence checks. Values built through older constructor paths are
  canonicalized where they are built.
- **Substitution.** It rebuilds through the smart constructor. Substituting a
  literal for the base yields a literal. Substituting a context value combines
  the two contexts.
- **Printing** shows the counts, never the unfolded chain.
- **Admission.** A context value carries its exact Nat type. Construction keeps
  layout admission and constructor checks, so an untrusted lookalike
  declaration gets no packed or native behaviour. Other inductive families, and
  bare variables, are not wrapped.
- **Unchanged checks.** The existing conservative positivity treatment and
  linearity checks do not change.
- **One implementation** serves every consumer. The Core evaluator's scalar path
  and its general application path agree. No size-dependent path survives as a
  compatibility mode. The test-only source evaluator may remain, to check the
  host equations, but it is never the reduction policy.
- **The `Long` path stays.** The unboxed `Long` scalar path and its overflow
  fallback to arbitrary precision are kept. Symbolic reduction allocates no
  `BigInt` operands or packed values for ground operations that path already
  handles.

## 2. Step summaries

### Eligibility (first version)

A global declaration is summarized when:

- it is checked with `decreases structural(x)`, where `x` has the validated
  Nat type;
- every parameter and the result have the validated Nat or Bool type;
- its only recursive peer is itself.

Other declarations are never summarized and evaluate as today.

### The probe

The probe runs once, after the declaration is checked. Its result is stored
with the declaration and memoized like the declaration-time positivity scans.

1. Bind every parameter to a fresh variable, except the structural parameter
   `x`, which is bound to `succ(y_x)` for a fresh `y_x`. The guard set is `{x}`.
2. Evaluate the body once, with the recursive peer replaced by a **recorder**.
   The recorder is a native function that records its argument values and
   returns a fresh variable `R` of the result type. `NativeEquation.inspect`
   already runs a body with replaced peers, through `runLamWithRecursivePeers`.
3. If the result is blocked on the fresh variable of a Nat parameter that is
   not yet a guard, make that parameter a guard: rebind it to `succ(y)` for a
   fresh `y`, and restart. This happens at most once per parameter.
4. Otherwise, accept only if all of these hold:
   - the recorder was called exactly once;
   - the result is `R`, or `[k, j]·R` with constant counts (a Bool result must
     be exactly `R`);
   - for each guard `g`, the recorded argument is exactly `y_g`;
   - for each non-guard Nat parameter `a`, the recorded argument is `a`, or
     `[k, j]·a` with constant counts;
   - for each Bool parameter, the recorded argument is that parameter's
     variable.

   Anything else means no summary. That includes a block on `R`, on some `y`,
   or on any other neutral.

The summary is the guard set, one context `m_a` per non-guard Nat parameter,
and the result context `m`. Summaries of earlier declarations apply during the
probe, so a layer whose result is `Nat.add(R, 1)` is recognized as `[0, 1]·R`.

### Acceleration

When a summarized function is applied to argument values:

1. Let `t` be the smallest number of known successors among the guard
   arguments. If `t = 0`, apply the function normally.
2. Otherwise:
   - pop `t` from every guard argument;
   - apply `m_a^t` to every non-guard Nat argument;
   - leave Bool arguments unchanged;
   - apply the function normally to the new arguments, and apply `m^t` to what
     it returns.

The result is identical to taking `t` ordinary layers. An implementation may
therefore skip acceleration when `t` is small; that is a choice about cost,
never about meaning. The known successors of an unboxed scalar are its value.
Acceleration must not box closed scalars that the existing `Long` path
handles.

### Why this is sound

The probe evaluated one layer for fresh variables. It found that
`F(x⃗) = m · F(m_a · a, …, y_g, …)` whenever each guard `g` is `succ(y_g)`.

Evaluation is stable under substitution: evaluating with variables and then
substituting values gives the same value as evaluating with those values
directly. Refinement already relies on this. Two consequences follow:

- The equation holds for every argument tuple in which each guard has at least
  one known successor. Write the guard argument as `succ` of its predecessor,
  and substitute that predecessor for `y_g`.
- The layer never blocked on a non-guard argument. So substituting any value
  for one follows the same path.

Each layer removes exactly one known successor from each guard. By induction
on `t`, `F(v⃗) = m^t · F(m_a^t · a, …, pop^t(g), …)` whenever every guard has at
least `t` known successors.

The new trusted code is the context algebra of §1 and the acceleration rule.
No rule specific to one function is trusted. The differential tests below check
the substitution-stability assumption directly.

### What gets summarized

| Declaration | Guards | Non-guard contexts | Result context |
|---|---|---|---|
| `Nat.add(a, b)` | `b` | `a ↦ [0, 1]` | identity |
| `Nat.sub(a, b)` | `b` | `a` unchanged | `[1, 0]` |
| `Nat.beq(a, b)` | `a`, `b` | none | identity |
| `Nat.ble(a, b)` | `a`, `b` | none | identity |
| user `double(n)`, with `double(succ p) = succ(succ(double(p)))` | `n` | none | `[0, 2]` |

These are not summarized (§6 would summarize `mul` and `pow`):

- `Nat.mul`: its layer is `Nat.add(a, R)`, which is blocked on `R`.
- `Nat.pow`: its layer is `Nat.mul(R, a)`.
- Any layer whose effect depends on the predecessor, for example
  `sum(succ p) = add(succ p, sum(p))`.
- Two-layer descent, for example `half(succ(succ p))`.
- Tree recursion.

`Nat.pred`, `Nat.isZero` and `Nat.blt` are not recursive. `blt` evaluates its
body, `ble(succ(a), b)`, and so is accelerated through `ble`.

Each of these then costs O(1) `BigInt` operations:

- `add(x, 10^30) = [0, 10^30]·x`
- `sub(add(x, 5), 3) = [0, 2]·x`
- `add(sub(x, 3), 5) = [3, 5]·x`
- `ble(10^30, 10^30 + 1) = true`
- `sub(succ(succ(x)), 1) = [0, 1]·x`, which matches as `succ`

## 3. Tail calls modulo a context

The frame evaluator already runs a call in tail position by reusing the
caller's frame: `Compiler.node` marks tail positions, and `enterFromSlots`
reuses the frame. Any other call pushes a frame and a `Return` continuation.
So `List.length(cons(h, t)) = succ(length(t))` holds one frame per element,
each waiting to apply `succ`. When a call's pending work is only context
building, it needs no frame.

### Marking

The compiler marks candidate context positions syntactically: the last
argument of an application that is in tail position or in a candidate context
position. When the evaluator reaches a candidate, it has already evaluated the
application's head and its other arguments, because arguments run left to
right. It then confirms by identity, never by name, that the head is a
constructor or the validated `Nat.pred`. Otherwise it evaluates the candidate
normally.

### Evaluation

Each frame carries a pending context, initially empty.

- At a confirmed context position, compose the builder into the frame's
  pending context and evaluate the call as a tail call. The frame and its
  pending context carry over to the callee, as for any tail call.
- `Nat.succ` and `Nat.pred` builders compose as `[0, 1]` and `[1, 0]` in the
  §1 algebra, so a Nat frame's pending context is one count pair.
- Other builders are kept in a compact array. Each entry holds the constructor
  and its other, already evaluated, arguments.
- When the frame produces its value, apply the pending context before
  returning. A count pair applies as `natContext(v, [k, j])`. An array applies
  its entries innermost first, through the ordinary constructor path, so keys,
  packing and result types are computed exactly as ordinary evaluation computes
  them.

A summarized function is still accelerated on entry (§2). Context positions in
its body apply to the ordinary layers that remain.

### Why this is exact

Ordinary evaluation builds the same constructor applications around the same
returned value, from the inside out, with the same already evaluated
arguments. Count pairs compose by the §1 algebra, whose laws hold
definitionally: `pred(succ(x))` is `x` by matching. So the returned value is
identical, key for key.

Only constructors and `Nat.pred` are builders. An operation such as
`add(x, □)` is not. Turning `add(x₁, add(x₂, □))` into `add(x₁ + x₂, □)` uses
associativity, which holds only propositionally, and it changes the normal
form whenever the hole is later filled by a neutral. §6 would change that.

### What benefits

- `List.length` (`succ`), `List.append` and `List.map` (`List.cons`),
  `Nat.sub` (`Nat.pred`), and user recursions of the same shape, such as
  `double`.
- Unlike acceleration, this needs no trip count. It therefore also applies when
  the recursion walks cells that must still be visited, such as a cons list.

Not covered:

- `List.filter` as written: its recursive call is let-bound and used in two
  places.
- `List.any`, `List.all`, `Nat.mul`, `Nat.pow` and folds such as `sum`: their
  pending work is an operation, not a builder.
- A call that is not its builder's last argument.

A Nat frame keeps two counts instead of one frame per layer. A frame building
another type keeps one array entry per pending cell instead of a frame plus its
continuation entries; the cells themselves are output.

## 4. Native operations

A native operation now has two independent parts:

- **Closed jet.** Optional. It is used only when every argument is closed, and
  is checked against the source on closed values as today. Its only job is
  speed.
- **Symbolic behaviour.** For a summarized declaration, this is the source plus
  acceleration, so it produces exactly what the source produces. For any other
  declaration, it is the existing residual, described below.

Removed from `Packed.nativeOp`: `compact`, `compare`, `prefixParts`,
`exactZero`, and the `blt` delegation through `validatedBle`.
`natConstructorParts` becomes the constructor view of §1.

| Operations | Closed jet | Symbolic arguments |
|---|---|---|
| `add`, `sub`, `beq`, `ble`, `blt` | kept for the unboxed scalar path; keep or drop the `BigInt` jet by measurement | source plus acceleration; no residuals |
| `mul`, `pow` | kept | residual, unchanged |
| `div`, `mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight` (when a trusted prelude declares them) | kept | residual, unchanged |

For the residual operations, one generic rule replaces the zero rules written
by hand: if the structural argument is the literal `0`, take one ordinary layer
of the source. This reproduces today's `mul(a, 0) = 0` and `pow(a, 0) = 1`.
Otherwise the result is the existing residual. It keeps every blocker needed
to rerun after refinement, and it reruns with the same reducer. Closed jets
keep their validated host equations, and their explicit resource limits for
exponentiation and shifts.

### Conversion of residual operations

A residual must stay convertible with its source's constructor equations
wherever proofs need them. For example, `mul(a, succ(b))` must compare with
`add(a, mul(a, b))`. Native residuals must not silently lose those proofs.

- When no direct rule settles a comparison, conversion inspects one layer of
  the exact checked source body. Recursive peers in that inspection refer to the
  published native residual heads, so one layer never runs the whole recursion.
  This happens on demand, during conversion of a blocked computation.
  Evaluation stays eager.
- The inspection keeps the equation's source identity and typed environment.
  It never recognizes syntax by printed names.
- It compares under a non-invertible frame, discards partial choices when the
  comparison fails, and reports a failure as stuck.
- The same residual comparison is never repeated indefinitely, and no numeric
  cutoff returns under another name.

If preserving these equations needs a larger language change, report the
concrete failing proof before adding machinery or rewriting the proof around
it.

A known gap remains, unchanged from today: `mul(succ(x), 1)` is `succ(x)` by the
source, but it stays a residual, so a `match` on it is stuck. §6 would close
it.

Effect on positivity: `Nat.add(base, bytes)` with a neutral `bytes` is now
`add`'s stuck match, an ordinary neutral, rather than a native residual.
Declaration-time positivity handles it like any other stuck match. Re-run the
`Regions.Layout.reserve` case.

## 5. Later extensions (not in this version)

- **Acceleration over Lists and Strings.** The contexts are "drop `k`, then
  prepend the list `w`", with the same composition rules. The layer of `append` or `map` depends
  on the peeled element, so its `t`-th power is computed over the known prefix.
  That costs `O(t)` element work, but no interpretation per layer.
- **Deeper guards.** Allow a guard to require `d` successors, so `half` is
  summarized with `t = ⌊known / d⌋`.
- **Parametric contexts.** Allow counts that are parameters passed unchanged,
  as in `acc ↦ add(acc, c)`. This would cover an accumulating `mul` by a closed
  multiplicand. §6 needs them.
- **Mutual recursion and indexed families.**

## 6. Polynomial normal forms (planned follow-up)

Status: planned under the principle of making evaluation as fast as possible.
It needs its own spec. Today's code does not need it: in `../lemur-raccoon`,
Nats are closed during staging, and no data is transported along arithmetic
equalities.

### What changes

`Nat.add` and `Nat.mul` become a commutative semiring under definitional
equality. This extends the principle of this proposal rather than replacing
it: every source equation still holds, and the semiring laws hold in addition.

### Representation

- A Nat value is a polynomial with `BigInt` coefficients over atoms:
  `Map[Monomial, BigInt]`, where a monomial is `Map[Atom, Int]`. Atoms are
  neutrals compared by identity, as in `Level`'s `Map[VarId, Int]`.
- `sub`, `ble` and `beq` first cancel the common part (the coefficientwise
  minimum) of their arguments `P` and `Q`, leaving `P'` and `Q'`:
  - `sub(P, Q)` is `P'` if `Q'` is zero, `0` if `P'` is zero, and otherwise
    the atom `sub(P', Q')`. `pred(P)` is `sub(P, 1)`, and subtracting from a
    `sub` atom folds into its subtrahend: `sub(sub(P, Q), R) = sub(P, Q + R)`.
  - `ble(P, Q)` is `true` if `P'` is zero, and `false` if `Q'` is zero and the
    constant of `P'` is at least 1. Otherwise it is stuck.
  - `beq(P, Q)` is `true` if both are zero, and `false` if one is zero and the
    other's constant is at least 1. Otherwise it is stuck.
- Matching sees `zero` only for the zero polynomial, and `succ` with
  predecessor `P − 1` when the constant is at least 1. Otherwise it is blocked
  on the atoms.
- The context value `[k, j]·e` is the polynomial `sub(e, k) + j`. Known
  successors are the constant term.

### Why it is faster

- Operation contexts compose exactly. Contexts become affine maps
  `R ↦ M·R + C` over polynomials, whose compositions and powers are polynomial
  arithmetic. Contexts may mention parameters that are passed unchanged.
  - Acceleration (§2) then covers `mul`, whose layer is `R + a` with power
    `R + t·a`, and `pow`, whose layer is `R·a` with power `R·aᵗ`.
  - Tail calls modulo a context (§3) cover `add(x, □)` and `mul(x, □)`
    builders, and so folds such as `sum`.
  - Layers that mix pops with affine contexts are not summarized.
- Arithmetic over several neutrals gets compact canonical values.
- The `mul` and `pow` residuals and the one-layer `NativeEquation` inspection go
  away, and with them the `mul(succ(x), 1)` gap.

### Costs and decisions

- Every operation with symbolic arguments does normalization work.
- A product of sums can grow exponentially. Decision (2026-10-05): expand
  fully, with a deterministic abort limit on monomial count and degree. The
  limit fails loudly and never changes an answer. There are no
  random-evaluation fingerprints.
- Unification stops being unitary for `+`: `add(?a, ?b) ≡ add(x, y)` has
  several solutions. Solve only `?m + P ≡ Q` with `P ≤ Q` coefficientwise, by
  `?m := Q − P`, and postpone everything else. Measure elaboration regressions
  on the corpus before adopting it.
- The polynomial code joins the trusted kernel.

### Obligations

1. Every identification is true in ℕ.
2. Every source equation of the Prelude operations holds after normalization,
   on symbolic arguments too, checked with the §2 probe. For example, naive
   cancellation turns `sub(x+5, y+3)` into `sub(x+2, y)`, while the source
   gives `pred³(sub(x+5, y))`. Folding pops into the subtrahend makes both
   `sub(x+2, y)`.
3. Normalizing and substituting commute, and every decision survives
   substitution. Coefficientwise dominance and "constant at least 1" do.
4. `P + 1 ≡ Q + 1` implies `P ≡ Q`, and `P + 1` is never `0`.
5. Structural termination takes strict subterms only by peeling the constant:
   `x` is not smaller than `x + y`.
6. Atom identity agrees with conversion. Compound stuck atoms carry node
   identity in their keys, so canonicalize them or compare leftover atoms by
   conversion.

### Constraint on this proposal

Implement §1 so that a context value can later become a polynomial without
touching its consumers. Consumers use only the smart constructor, the
constructor view and known successors, never a node's fields.

## Not in scope

- Polynomial normal forms; they are planned in §6 with their own spec.
- Inverting pops in unification, or solving unknown Nats by inverting any
  arithmetic operation.
- Changing residual semantics for unsummarized natives, including the
  `mul(succ(x), 1)` gap.
- The packed `CharList` and `String` path.

## Required validation

1. **Differential.** Take every summarized Prelude function and every argument
   tuple drawn from `{0, 1, 2, 7, x, y, [0, 3]·x, [2, 0]·x, [2, 5]·x}`. The
   value with acceleration and the value with acceleration disabled (ordinary
   layers only) must have equal keys. Add a switch that disables acceleration,
   next to `Packed.withOpsDisabled`.
2. **Shape.** Each of `add(x, 10^30)`, `sub(x, 10^30)`, `sub(add(x, 5), 3)`,
   `sub(add(x, 3), 5) = [2, 0]·x`, `add(sub(x, 3), 5)` and
   `ble(10^30, 10^30 + 1)` builds one node or literal. Tests inspect the shape,
   including counts beyond `Long`.
3. **Regression.** `match Nat.sub(Nat.succ(Nat.succ(x)), 1)` takes the `succ`
   branch, with predecessor `x`. First confirm that it is stuck before the
   change, as reading `compact` predicts.
4. **Summaries.** `add`, `sub`, `beq`, `ble` and a user `double` are summarized
   as in the table. `mul`, `pow`, `sum`, `half` and a tree-recursive function
   are not summarized, and still evaluate correctly. `double(10^30)` costs O(1).
5. **Unification.** Pops over metas postpone. `[0, j]·?m ≡ n` still solves.
   Unequal ground values stay apart.
6. **Small and large.** Ground matching, context values, zero against
   successor, predecessor binding, materialization, and constructor and
   refinement proofs agree across small counts, large counts, and counts beyond
   machine integers.
7. **Termination.** Structural recursion accepts genuine prefix descent and
   rejects unrelated bases.
8. **Conversion.** Native constructor equations and explicit source selectors
   compare wherever existing Nat induction proofs need them. Unknown arithmetic
   stays stuck. No impossible equality is accepted.
9. **Tail calls modulo a context.** `List.length`, `List.map`, `List.append`
   and a user recursion shaped like `Nat.sub` run over 250,000 elements with a
   bounded frame depth, measured by instrumentation. Their values with the
   optimization on and off have equal keys. A constructor whose recursive call
   is not its last argument, `List.filter` as written, and a user function
   named like a constructor are evaluated normally.
10. **Existing suites.** `sbt validate` passes in this repository. The `.rac`
   files, the library experiment and the GPU checks below live in their own
   repositories since 2026-10-05; run them there against the changed compiler.
   - `NatBoundConversion.rac` and `RingStorageBound.rac` check unchanged at 256,
     257, 9216 and larger.
   - `NatBltSuccessor.rac`, `gpu/proofs/SharedMemory.rac` and
     `gpu/proofs/WellFormed.rac` check again, as they do at HEAD.
   - `Arithmetic.rac`, `RingStorageProofs.rac`, `RingLibraryProofs.rac`,
     the library experiment and the GPU client checks pass.
     Do not overlap sbt builds and CLI JVMs.
   - CUDA outputs stay byte-identical.
   - These pass without proof detours. An independent source-authoring error is
     reported as such, separately from a compiler barrier.
   - The compiler change never edits the GPU proof or specification files to
     make a check pass.
   - Any newly exposed friction is recorded and escalated.
11. **Cost.** Compare the CPU time of the library experiment and the GPU checks
   before and after, under the same load. Do not use the old interpreter
   benchmark suite.

## Open questions

- Should the `BigInt` closed jets for `add`, `sub`, `beq` and `ble` be deleted
  once acceleration covers them? Deleting them shrinks the set of validated host
  equations. The answer depends on measurement.
- Is it acceptable to make `Nat.pred` a declaration the kernel recognizes? That
  adds one function to the validated Prelude surface.
- Should the Prelude's `List.filter` be rewritten so that its recursive call is
  in a context position? That means matching on `p(head)`, with
  `cons(head, filter(…))` in one branch and `filter(…)` in the other.
- Should §6 follow §1–§3 directly, or wait until measurement shows a need?
