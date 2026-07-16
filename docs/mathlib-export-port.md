# Mathlib Export Port Plan

Status: **implementation** (**M0 done**). Companion to `kernel-theory.md` (the theory constraints every workstream must
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

Both channels are already closed here: proof-valued metrics are forbidden (`Acc` will be sealed,
§4.K2), and proof structure is reconstructed only from declaration-certified exact-type recipes.
The evaluator never runs unification or a K-like diagonal rule. For the Abel–Coquand term, every
checked proof of a Pi canonicalizes to a type-directed eta-lambda whose application reconstructs
only the instantiated result proposition; the original proof body never executes. The export's references to the
poison rules get **primitivized or patched, never implemented**. Mathlib fits in the complement empirically: since Lean 4.9
(leanprover/lean4#4061) well-founded definitions are irreducible by default and Mathlib proves
through equation lemmas, and kernel arithmetic runs on native literals, not `Nat.rec` unfolding.

Invariants the whole plan must preserve (kernel-theory §5–§6):

- No fixpoint ever recurses through a proof-valued metric.
- `VProof` contains only its proposition and quotes canonically as `proof(A)`; no erased witness
  exists to flow into evaluation, conversion, or diagnostics.
- Proof constructor reconstruction is certified at inductive checking time; the exact proposition
  supplies every retained field, and the interpreter never invokes unification.

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
| K3 | Native Nat/String literals | — | **Nat base done**; M0 requires every staged Nat op; String staged |
| K4 | Primitive projections + structure eta | — | **done** |
| K5 | `imax` levels | M0 stats | **done** |
| K6 | Mutual / nested inductives | M0 stats | M0 decision: native kernel support |
| K7 | Axioms: propext, choice | evidence-grades refactor | — |
| T1 | Export reader + prelude alignment | — | M0 reader/stats done; translation pending |
| T2 | Recursor synthesis | K1 | — |
| T3 | `Acc`/WF cluster mapping | K2 | — |
| T4 | Typecheck-and-patch loop | T1–T3 | — |
| P1 | Eager-normalization scaling | M1 measurements | decision gate |

## 4. Kernel workstreams

**K1. Higher-order subterm rule — done.** Applications of function-typed constructor fields count
as strict subterms (`TerminationChecker.applicationOfSubterm`; kernel-theory §5 row, §6 checklist
item). This makes translator-synthesized recursors definable for infinitary inductives (`WType`,
`PGame`).

**K2. Sealed `Acc`/`WellFounded` cluster.** Needs its own spec (`wf-recursion.md`). The
declaration-time singleton policy may retain an actual `Acc.intro`, so a literal value can take one
ordinary match step. That does not define `Acc.rec`: accessibility hypotheses are erased neutral
proofs, and proof-valued metrics are rejected, so no fixpoint can recurse through the child proof.
Design: a primitive constant with the Sort-motive `Acc.rec` type that **never unfolds
definitionally**, plus its unfolding equation as a primitive *propositional* lemma (model-justified
by well-founded induction; same trust genre as `Quot.sound`). Prop-motive `Acc.rec` is ordinary
small elimination via match — already supported. Ledger obligations: an axiom-table row (§4) for
the primitive equation; the §1 invariant "no definitional recursion through proof metrics"
stated as case law. Cost accepted: WF-defined functions do not compute by defeq — identical to
post-4.9 Lean practice (equation lemmas; native ops cover `Nat.div`-class literals).

**K3. Native literals — Nat done.** Spec: `native-literals.md` (the `VPacked` design — a packed
value form with a closed, kernel-curated codec set; representation-not-rules, dual of K4).
`NatLit`, constructor↔literal transparency, packed structural decrease, and the seven operations
whose structural definitions exist today (`add/sub/mul/pow`, `beq/ble/blt`) are implemented and
certified against the structural path. Native Nat names are reserved to the bundled Prelude.
M0 found all staged Nat operations already in the `Init` export, so `div/mod/gcd` and the complete
bitwise set are required for M1 (still K2/T1-gated); `StrLit` remains staged until the Prelude
has `String`/`Char`. Container codecs (List-as-array, Vec-as-array+Nat) remain out of scope and
deferred with the P1 caching decision (spec §1).

**K4. Primitive projections + structure eta — done** (StructEta; kernel-theory §2 "structure
eta"). Implemented as representation, not conversion rules: every value of an eta-eligible structure-like inductive
type (one ctor, no indices, non-recursive, non-Prop instance) is constructor-headed. Binders
freshen expanded; neutrals — opaque constants, axioms, blocked applications/matches, stuck
`Quot.lift/ind` — wrap into the constructor of their stuck projections (`StructField`-headed
applications, defEq by head name + base). Eta is then fieldwise congruence, matches on struct
scrutinees always fire, and the flagged interaction resolved itself: proof fields follow the proof
representation policy at projection formation, and proof irrelevance equates reconstructed and erased
forms in `⟨s.val, s.property⟩ ≡ s`. Prop *instantiations* of sort-polymorphic structs never
eta-expand; every inhabitant follows the shared field-recovery plan, and layouts with unforced
fields such as `PairU` cannot reconstruct a constructor (though independently recoverable fields
may still project). Notable
consequences: opaque-by-default (P1) stays eta-compatible — an opaque instance constant gets eta
without unfolding its body — and projections of opaque constants are transparent to positivity
(previously rejected conservatively). Translator note for T1: exported `proj i` nodes map directly
to `CoreAst.Term.Proj(family, i, base)`; named selector spellings are irrelevant. The block checker
must recompute block recursion and validate any exported `isRec` claim rather than trusting it.
Residual gaps for the T4 taxonomy: values created before their
type is a *known* structure-like instance stay bare (rigid binders at then-blocked types; neutrals whose
types reveal only under a later store — expansion is canonical-at-birth by design, see
kernel-theory §2), and expansion cost on deep bundled-class hierarchies is a P1 measurement item.

**K5. `imax` — done.** Raccoon's canonical level form is generalized from
`max(vᵢ+kᵢ, c)` to `max(aᵢ+kᵢ, c)`, where an atom is a variable or an unresolved normalized
`imax`. The smart constructor implements Lean's zero/definitely-positive reductions and retains
the conditional form otherwise; substitution recursively re-normalizes it. Pi classifiers now
right-fold `imax` over the domains and codomain, matching Lean's telescope rule, so an open
polymorphic Pi retains the conditional universe and a later Prop instantiation reduces to `Prop`
and triggers the proof representation policy. Keys, quotation,
Prelude builtins, conservative universe bounds, unification, and forced-implicit projection all
handle the extended form; only an exact variable-plus-offset remains invertible. M0 found genuine
`imax` in declared types already in `Init` (`pi_congr`, `implies_congr`, and generated
constructor-elimination types). Tests pin normalization, substitution, bounds, quote round-trips,
polymorphic Pi formation, and Prop-instantiated proof-lambda canonicalization. Counts:
`m0-export-stats.md`.

**K6. Mutual and nested inductives.** Draft design: `k6-mutual-nested-inductives.md`. The Lean
kernel accepts both natively; Raccoon has neither as a complete declaration/recursor pipeline.
Mutual: generalize positivity, the termination order (component-wise subterm across the block), and
recursor synthesis. Nested: prefer kernel support over an encoding pass (encodings change
no-confusion/injectivity behavior downstream). Public nested values stay direct, but recursor
validation must build Lean's logical extended block so specialized container motives and minors
appear in the telescope; nested containers must share the block universe. M0 found mutual and
nested blocks in the first raw Mathlib slice, including blocks in the imported Lean/Std closure.
Since T1 consumes that raw export rather than a separately validated dependency-pruned artifact,
the decision is native kernel support, not an encoding or deferral. Counts: `m0-export-stats.md`.
K6 also generalizes the existing per-family proof-recovery plan to block checking; neither
mutual membership nor recursiveness introduces a runtime proof-unification rule.

**K7. Axioms.** `propext` and `Classical.choice` (with `Nonempty`); `funext` arrives as a theorem
via `Quot.sound`. `propext` is safe under the proof representation policy: after checking, every
proof-valued lambda becomes the type-directed proof eta-lambda, so the Abel–Coquand trigger never
executes its discarded source body. Pin this with the Ω must-terminate probe before landing. The
axiom is still *gated on the evidence-grades refactor*
(kernel-theory §5 design debt / `TODO(propext)` on `definitionallyInjectiveHead`). `choice`
coarsens per the §4 axiom ledger (Cantor kills large-parameter former injectivity) — the ledger
says current rules already exclude this; re-walk §6 when landing.

## 5. Translator workstreams

**T1. Export reader + prelude alignment.** The M0 reader-only portion is done
(`LeanExportM0` / `MathlibExportStats`): it validates format 3.1.0 and intern-table order while
retaining only packed transitive summaries, and was exercised on real `Init` and
`Mathlib.Logic.Basic` exports. See `m0-export-stats.md`. Remaining work: translate the stream and
retain topological declaration order. Map Lean's `Eq`, `Nat`, `Quot`, `Bool`, … onto the Raccoon Prelude
(or import a fresh translated core and keep Raccoon's Prelude only for bootstrapping); mangle
names into namespaces; insert explicit level arguments; translate `let` to `Body.lets`.
`theorem`s are checked once and passed through the proof representation policy. Every proof of a
Pi proposition publishes as the same type-directed eta-lambda, regardless of transparency; its
checked source body is discarded. Other proofs publish as a constructor reconstructed from their
exact proposition when the family recipe succeeds, and as `VProof` otherwise. This removes
operational theorem bodies while preserving all constructor computation forced by the type.

**T2. Recursor synthesis.** For logical blocks that are not definitely Prop, emit ordinary match
definitions; recursive SCCs use `decreases structural(major)`, with IHs as lambdas applying
selector fields (the K1 shape, pinned by "synthesized recursor shape" in TerminationTests).
Permitted non-recursive Prop eliminators are ordinary matches without a metric. Nested telescopes
are derived from K6's complete logical extended block—one motive per declared or specialized
family and one minor per corresponding constructor—with a fresh motive-result universe for
ordinary non-Prop recursors (non-recursive Prop uses the recomputed large-elimination result).
Every recursor in a recursive definitely-Prop logical block, including a
nested-container auxiliary, has a proof-valued major and cannot use it as a structural metric:
K6 derives the Prop induction-principle types in the kernel, validates the exported types, and
publishes bodiless principles in canonical eta-lambda form. Ordinary large elimination instead
requires every constructor field to be recoverable at the actual Prop instance. Exact propositions
whose recovered constructor also passes the result check match normally; other proofs stay stuck
for data motives. Instance-sensitive proof classification preserves generic `Sort u` terms that
land at `u = 0` without permitting an unvalidated branch reduction. Derived constants (`casesOn`, `brecOn`, `below`, `noConfusion`, …) are
ordinary definitions in the export and translate as-is once `rec` exists. For ordinary match
recursors, the export's ι-rules are the spec at non-collapsed instances: match evaluation + fix
unfolding must reproduce them definitionally on constructor-headed majors. For bodiless Prop
principles the ι-rules are proof-irrelevant; the generated type is the load-bearing validation.

**T3. `Acc`/WF cluster mapping.** A fixed table: Sort-motive `Acc.rec` occurrences and
`WellFounded.fixF`/`fix` map to the K2 primitives; their Lean equation-lemma *proofs* are replaced
by the primitive lemma. Retaining a literal `Acc.intro` does not install recursive ι-reduction,
because the recursive child is proof-valued and cannot be a metric. Everything downstream that
merely *uses* `fix_eq` translates unchanged.

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
Proof erasure removes most proof bodies from the equation, so the risk concentrates in Type-level definition
bodies (instances). Plan: measure at M1/M3 (wall-clock, peak values allocated, per-declaration
histograms — extend `benchmarks/`); mitigations in escalation order: opaque-by-default for
translated definitions Lean marked irreducible, hash-consing via existing `ValueKey`s, and only if
forced, laziness for definition bodies (an architectural change requiring its own
kernel-theory review — thunks must not weaken the §5 evidence rules).

## 7. Milestones

- **M0 — stats — done.** A reader-only pass over real `Init` and `Mathlib.Logic.Basic` exports
  counting: `Sort (imax …)` in declared types, mutual blocks, nested inductives, Sort-motive
  `Acc.rec` uses outside the fix cluster, `proj` nodes, literal ops used, declarations flagged
  irreducible. Results and resolved gates: `m0-export-stats.md`. The Abel–Coquand Ω
  must-terminate probe is pinned in `ConsistencyTests`.
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

## 8. Decision gates

1. **Resolved at M0:** K5 extends the level algebra; genuine `imax` occurs in `Init` declaration types.
2. **Resolved at M0:** K6 gets native mutual/nested support; both occur in the first raw Mathlib slice.
3. **Open:** Prop-level `Quot.lift` stuckness (proof-collapse §7): completeness question — does Mathlib's
   `Quotient` usage ever eliminate a Prop-level quotient into data? Check at M2.
4. **Open:** Native-op trust: builtin defeq steps trusted outright (Lean's stance) vs. certified against the
   structural definitions on first use. Default: trusted, documented in the §4 axiom ledger.
5. **Open:** P1 laziness — only if M3 measurements force it.

## 9. Non-goals

Surface-source porting, tactics, `simp`, elaborator compatibility; a live-development Mathlib
(the translated artifact is a frozen library — new development happens in Raccoon proper);
kernel-level recursive `Acc` ι-reduction and K-like reduction on neutral proofs (excluded *by
design* — they are the undecidability channels); univalence (kernel-theory §4: not planned).
