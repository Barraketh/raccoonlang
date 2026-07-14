# Mathlib Export Port Plan

Status: **planning**. Companion to `kernel-theory.md` (the theory constraints every workstream must
respect) and `proof-collapse.md`. Records the decisions from the 2026-07 decidability analysis;
the workstream sections are the units of implementation, the milestones (§7) are the acceptance
ladder.

## 1. Goal and strategy

Typecheck a post-elaboration export of Mathlib (lean4export ndjson: kernel-level declarations and
terms) by mechanically translating it to CoreAst. Consuming the *export* rather than Lean source
means no elaborator, tactic framework, or `simp` engine is needed — the problem is kernel feature
parity plus a translation pipeline.

The governing decision: **Raccoon stays in the decidable fragment.** Lean's type checking is
undecidable through exactly two rules, both instances of "an irrelevant term drives reduction":

1. Proof irrelevance feeding `Acc.rec` ι-reduction (Carneiro, *The Type Theory of Lean*, §3.1 —
   defeq encodes halting under a single accessibility hypothesis; the kernel algorithm is
   non-transitive and can diverge).
2. Werner's rule — K-like reduction of `Eq.rec`-style casts on neutral proofs — which with
   impredicative Prop and propext yields a closed term with no whnf (Abel–Coquand,
   arXiv:1911.08174).

Both channels are already closed here: there is no recursion through proofs (collapsed proofs have
no subterms; `Acc` will be sealed, §4.K2), and collapse erases proof-level reduction entirely, so
the Abel–Coquand term collapses to a `VProof` before it can step (its every subterm is
impredicatively in Prop). The export's references to the poison rules get **primitivized or
patched, never implemented**. Mathlib fits in the complement empirically: since Lean 4.9
(leanprover/lean4#4061) well-founded definitions are irreducible by default and Mathlib proves
through equation lemmas, and kernel arithmetic runs on native literals, not `Nat.rec` unfolding.

Invariants the whole plan must preserve (kernel-theory §5–§6):

- Collapsed proofs never drive unfolding; no fixpoint ever recurses through a proof.
- `VProof` witnesses never flow into evaluation or conversion (quoting/diagnostics only).
- Reduction gates are type-level only (the diagonal rule); never gate on proof structure.

## 2. Input format

One declaration per line: universe levels (`0`, `succ`, `max`, **`imax`**, params), expressions
(bvar, sort, const-with-levels, app, lam, forallE, let, **proj**, **Nat/String literals**),
declarations (def/theorem/axiom/opaque with reducibility hints, inductive families — possibly
**mutual or nested** — constructors, recursors with their ι-rules, `#QUOT`). Terms are closed and
fully explicit; universe params become Raccoon's Level-implicit zone, and the translator supplies
explicit arguments per Raccoon's all-or-none implicit rule.

## 3. Workstream index

| # | Workstream | Depends on | Gate |
|---|---|---|---|
| K1 | Higher-order subterm rule | — | **done** (commit 3355563) |
| K2 | Sealed `Acc`/`WellFounded` primitives | — | spec review |
| K3 | Native Nat/String literals | — | — |
| K4 | Primitive projections + structure eta | — | — |
| K5 | `imax` levels | M0 stats | decision gate |
| K6 | Mutual / nested inductives | M0 stats | decision gate |
| K7 | Axioms: propext, choice | evidence-grades refactor | — |
| T1 | Export reader + prelude alignment | — | — |
| T2 | Recursor synthesis | K1 | — |
| T3 | `Acc`/WF cluster mapping | K2 | — |
| T4 | Typecheck-and-patch loop | T1–T3 | — |
| P1 | Eager-normalization scaling | M1 measurements | decision gate |

## 4. Kernel workstreams

**K1. Higher-order subterm rule — done.** Applications of function-typed constructor fields count
as strict subterms (`TerminationChecker.applicationOfSubterm`; kernel-theory §5 row, §6 checklist
item). This makes translator-synthesized recursors definable for infinitary inductives (`WType`,
`PGame`).

**K2. Sealed `Acc`/`WellFounded` cluster.** Needs its own spec (`wf-recursion.md`), but the shape
is forced: collapse erases `Acc.intro` heads, so ctor-gated unfolding (Coq/Lean style) is
inexpressible, and the diagonal subsingleton rule must never apply to a recursive singleton (for
`Acc` it would fire unconditionally — its only field is a proof and its index forces nothing).
Design: a primitive constant with the Sort-motive `Acc.rec` type that **never unfolds
definitionally**, plus its unfolding equation as a primitive *propositional* lemma (model-justified
by well-founded induction; same trust genre as `Quot.sound`). Prop-motive `Acc.rec` is ordinary
small elimination via match — already supported. Ledger obligations: an axiom-table row (§4) for
the primitive equation; the §1 invariant "no definitional recursion through collapsed proofs"
stated as case law. Cost accepted: WF-defined functions do not compute by defeq — identical to
post-4.9 Lean practice (equation lemmas; native ops cover `Nat.div`-class literals).

**K3. Native literals.** `NatLit` value form; ctor↔literal transparency (`Nat.rec`/match on a
literal must fire; `succ`-of-literal folds back); the ~15 kernel-accelerated ops Lean has
(add/sub/mul/div/mod/pow/gcd, beq/ble/blt, land/lor/lxor/shifts) as builtin defeq steps, each
justified against the structural Prelude definitions (they are derived rules, not new axioms —
decidability-benign). `StrLit` unfolds to `List Char` constructor form on demand; no accelerated
string ops needed. Without K3, literal-arithmetic proofs are not slow but *infeasible* (unary
numerals).

**K4. Primitive projections + structure eta.** The export uses `proj` nodes, not recursor
applications; extend the existing projection support to translate them, and add definitional eta
for single-constructor non-Prop structures (`s ≡ ⟨s.1, …, s.n⟩`). Required for Mathlib's
instance-diamond defeq. Standard and decidability-benign; interaction to check: eta vs. proof
collapse for structures with proof fields (the proof components compare by `VProof` equality).

**K5. `imax`.** Raccoon's canonical `max(vᵢ+kᵢ, c)` form cannot express `Sort (imax u v)`, and
translating `imax` as `max` silently reclassifies Prop-instantiations into `Sort u` — proofs stop
collapsing, a semantic divergence. Options: (a) extend the level algebra with imax normal forms
(case-split on `v = 0`; Lean's own level defeq is a sound-incomplete syntactic normalizer, so
parity does not require completeness); (b) recompute binder sorts semantically during translation
and fail loudly on declarations where genuine imax-polymorphism survives. Decision gate: M0 counts.

**K6. Mutual and nested inductives.** The Lean kernel accepts both natively; Raccoon has neither.
Mutual: generalize positivity, the termination order (component-wise subterm across the block), and
recursor synthesis. Nested: prefer kernel support over an encoding pass (encodings change
no-confusion/injectivity behavior downstream). Decision gate: M0 counts over the mathematical
closure — if nested occurrences are rare, they may be deferred past M3.

**K7. Axioms.** `propext` and `Classical.choice` (with `Nonempty`); `funext` arrives as a theorem
via `Quot.sound`. `propext` is safe under collapse (the Abel–Coquand trigger is erased — pin with
the Ω must-terminate probe before landing), but it is *gated on the evidence-grades refactor*
(kernel-theory §5 design debt / `TODO(propext)` on `definitionallyInjectiveHead`). `choice`
coarsens per the §4 axiom ledger (Cantor kills large-parameter former injectivity) — the ledger
says current rules already exclude this; re-walk §6 when landing.

## 5. Translator workstreams

**T1. Export reader + prelude alignment.** Parse the ndjson stream; intern names/levels/exprs;
topological declaration order. Map Lean's `Eq`, `Nat`, `Quot`, `Bool`, … onto the Raccoon Prelude
(or import a fresh translated core and keep Raccoon's Prelude only for bootstrapping); mangle
names into namespaces; insert explicit level arguments; translate `let` to `Body.lets`.
`theorem`s publish as collapsed proofs — checked once, erased — so proof bodies are never retained
(the memory-scaling win of collapse).

**T2. Recursor synthesis.** Per inductive, emit `Foo.rec` as an ordinary definition: match +
`decreases structural(major)`, IHs as lambdas applying selector fields (the K1 shape, pinned by
"synthesized recursor shape" in TerminationTests). Prop-motive recursors likewise (Prop-match).
Derived constants (`casesOn`, `brecOn`, `below`, `noConfusion`, …) are ordinary definitions in the
export and translate as-is once `rec` exists. The export's ι-rules serve as the spec: match
evaluation + fix unfolding must reproduce them definitionally on constructor-headed majors.

**T3. `Acc`/WF cluster mapping.** A fixed table: Sort-motive `Acc.rec` occurrences and
`WellFounded.fixF`/`fix` map to the K2 primitives; their Lean equation-lemma *proofs* are replaced
by the primitive lemma (untranslatable in principle — they typecheck only via `Acc.rec` ι on the
minor premise's literal `Acc.intro`, which collapse erases). Everything downstream that merely
*uses* `fix_eq` translates unchanged.

**T4. Typecheck-and-patch loop.** The safety net for defeq divergence (prior art: Lean4Less, which
re-typechecks and inserts casts to eliminate definitional irrelevance/K from real libraries).
Attempt each declaration; on a defeq failure that Lean accepted, try known patches — chiefly
explicit `fix_eq` rewrites where a proof relied on kernel WF-unfolding (rare post-4.9; kernel-level
irreducibility landed later, RFC #5192, so exports can still contain them) — and report
irreducible failures with declaration provenance. The failure report *is* the parity worklist for
K-tail corner cases.

## 6. Performance (P1)

Raccoon eagerly normalizes values at construction in a Scala tree-walker; Lean is lazy
whnf-on-demand in C++ precisely because fully normalizing Mathlib's instance forest explodes.
Collapse removes proof bodies from the equation, so the risk concentrates in Type-level definition
bodies (instances). Plan: measure at M1/M3 (wall-clock, peak values allocated, per-declaration
histograms — extend `benchmarks/`); mitigations in escalation order: opaque-by-default for
translated definitions Lean marked irreducible, hash-consing via existing `ValueKey`s, and only if
forced, laziness for definition bodies (an architectural change requiring its own
kernel-theory review — thunks must not weaken the §5 evidence rules).

## 7. Milestones

- **M0 — stats.** A reader-only pass over a real export (root: core `Init`, then a Mathlib slice)
  counting: `Sort (imax …)` in declared types, mutual blocks, nested inductives, Sort-motive
  `Acc.rec` uses outside the fix cluster, `proj` nodes, literal ops used, declarations flagged
  irreducible. Resolves the K5/K6 gates. Also: land the Abel–Coquand Ω must-terminate probe.
- **M1 — core prelude.** The `Init` closure typechecks end-to-end (exercises T1/T2, K3, K4, K2 for
  `Nat.div`-class definitions). Acceptance: zero unpatched failures; perf baseline recorded.
- **M2 — `Mathlib.Logic`.** K7 axioms live (post evidence-grades refactor); classical reasoning,
  `Decidable` machinery, `decide`-style proofs.
- **M3 — `Mathlib.Order` + `Algebra` roots.** Instance diamonds at scale — the K4 and P1 stress
  test. Acceptance: diamond-heavy files check with defeq parity and acceptable wall-clock.
- **M4 — `Data.Nat`/`Data.List`/`Data.Fin`.** Literal-heavy and subsingleton-heavy content;
  `norm_num`-produced proof terms.
- **M5 — broad closure.** Grow toward the full mathematical closure; track the patch-rate and
  failure taxonomy as the health metric rather than a single pass/fail.

## 8. Open decision gates

1. K5 route (extend level algebra vs. semantic recomputation) — decide on M0 numbers.
2. K6 nested-inductive route (kernel support vs. defer) — M0 numbers.
3. Prop-level `Quot.lift` stuckness (proof-collapse §10): completeness question — does Mathlib's
   `Quotient` usage ever eliminate a Prop-level quotient into data? Check at M2.
4. Native-op trust: builtin defeq steps trusted outright (Lean's stance) vs. certified against the
   structural definitions on first use. Default: trusted, documented in the §4 axiom ledger.
5. P1 laziness — only if M3 measurements force it.

## 9. Non-goals

Surface-source porting, tactics, `simp`, elaborator compatibility; a live-development Mathlib
(the translated artifact is a frozen library — new development happens in Raccoon proper);
kernel-level `Acc` ι-reduction and K-on-structured-proofs (excluded *by design* — they are the
undecidability); univalence (kernel-theory §4: not planned).
