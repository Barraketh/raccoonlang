# Mathlib Export Port Plan

Status: **implementation** (**M0 done**). Companion to `kernel-theory.md` (the theory constraints every workstream must
respect) and `proof-collapse.md`. Records the decisions from the 2026-07 decidability analysis;
the workstream sections are the units of implementation, the milestones (§7) are the acceptance
ladder.

The M0/M1 parity target is lean4export 3.1.0 tag `v4.30.0` against Lean 4.30.0 at commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`. The 2026-07-20 producer refresh reopened the shape
assumptions recorded by T1, K2, K3, and K6: full `Init` has been rescanned, while a matching
Mathlib slice still needs regeneration before M1.

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
| K2 | Sealed `Acc`/`WellFounded` primitives | — | **kernel complete; kernel §13 pins green**; T3 mapping/tests pending |
| K3 | Native Nat/String literals | — | **kernel implementation complete**; translated-`Init` activation/manifest is T1-gated |
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
Design: a primitive constant with the full universe-polymorphic `Acc.rec` type that **never unfolds
definitionally**, plus its unfolding equation as a primitive *propositional* lemma (model-justified
by well-founded induction; same trust genre as `Quot.sound`). This seal is uniform: T3 eta-expands each exported partial
application into a saturated Core call; at a Prop motive the resulting wrapper is a proof of a Pi proposition and
existing proof canonicalization erases the distinction. A separate Prop-recursion
implementation would add trust without observable behavior. The
non-recursive `Acc.casesOn` is the explicit exception: T3 synthesizes it as a direct ordinary match so its safe iota
behavior is retained; `Acc.recOn`, `ndrec`, and `ndrecOn` remain sealed wrappers. Ledger obligations: rows for the
sealed recursor and generic recursor equation only; `fixF_eq` / `fix_eq` are synthesized checked applications before
wrapper opacity takes effect. The equation builder additionally requires a structurally validated Lean `Eq` block—an
exported name and a proposition-valued application do not authenticate equality. The §1 invariant "no definitional
recursion through proof metrics" is stated as case law. Cost accepted: WF-defined functions do not compute by defeq —
identical to post-4.9 Lean practice (equation lemmas; native ops cover `Nat.div`-class literals).

**K3. Native literals — kernel implementation complete.** Spec: `native-literals.md` (the `VPacked` design — a packed
value form with a closed, kernel-curated codec set; representation-not-rules, dual of K4).
`NatLit`, constructor↔literal transparency, packed structural decrease, and the seven operations
whose structural definitions exist today (`add/sub/mul/pow`, `beq/ble/blt`) are implemented and
certified against the structural path. Native Nat names are reserved to kernel-owned bootstrap
installers: the bundled Prelude and T1's pinned translated-`Init` mode. Following Lean's kernel
trust model, an exact native-operation identity installed by either trusted bootstrap receives its
kernel defeq rule outright; the definition is typechecked, but T1 does not attempt to prove or
fingerprint its agreement with the host arithmetic implementation. Ordinary imports can never
install those identities.
M0 found all staged Nat operations already in the `Init` export. K3 implements the native rows for
`div/mod/gcd` and the complete bitwise set; their checked structural definitions and production
activation remain K2/T1-gated for M1. The final fifteen-entry table is Lean's
fourteen pinned binary native identities plus `Nat.blt`, retained as an explicitly ledgered
Raccoon extension using the same trusted-bootstrap isolation. Nonzero `shiftLeft` has the same
`2²⁴` evaluator limit as `pow`; zero left-shift and sufficiently large right-shift return zero
without allocation. `StrLit` and the original `String.mk (List Char)` validated layout are
implemented and exercised through the synthetic full-K3 bootstrap. That layout is no longer the
production Lean layout: Lean 4.30 defines `String` with constructor `String.ofByteArray`, storing a
`ByteArray` plus a UTF-8 validity proof, and kernel literals reduce through `String.ofList`.
T1.5/K3 must add and validate this producer shape before translated-`Init` String activation; the
importer must not issue the old CharList capability for a 4.30 export. The bundled source Prelude
may retain its existing layout.

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

**T1. Export reader + prelude alignment.** Implementation spec: `t1-lean-export-importer.md`.
The M0 reader-only portion is done
(`LeanExportM0` / `MathlibExportStats`): it validates format 3.1.0 and intern-table order while
retaining only packed transitive summaries, and was exercised on real `Init` and
`Mathlib.Logic.Basic` exports. See `m0-export-stats.md`. Remaining work: translate the stream and
retain topological declaration order. The benchmark starts from a minimal kernel-owned `Sort`/`Level` bootstrap and
imports a fresh translated Lean `Init`; it does not load Raccoon's source Prelude. Preserve ordinary safe Lean names
and use an injective encoding only for numerical/exotic names. Retain each primitive's validated implicit/explicit
calling convention while supplying and validating every exported level and term argument; translate `let` to
`Body.lets`. For equality specifically, retain Lean metadata's two-parameter,
one-index split while lowering the checked Raccoon family to `{u}`, `A` parameters and `x`, `y` indices. Any equality
selected for primitive use must pass the shared structural `ValidatedEquality` check before K2 or another
primitive-proposition builder may use it.
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
land at `u = 0` without permitting an unvalidated branch reduction. Derived constants (`casesOn`, `brecOn`, `below`,
`noConfusion`, …) are ordinary definitions in the export and translate as-is once `rec` exists, except for K2's
explicitly synthesized non-recursive `Acc.casesOn`. For ordinary match
recursors, the export's ι-rules are the spec at non-collapsed instances: match evaluation + fix
unfolding must reproduce them definitionally on constructor-headed majors. For bodiless Prop
principles the ι-rules are proof-irrelevant; the generated type is the load-bearing validation.

**T3. `Acc`/WF cluster mapping.** Follow the fixed table in `wf-recursion.md`: every `Acc.rec`
occurrence maps to the uniformly sealed primitive; `Acc.casesOn` is separately validated and synthesized as a direct
non-recursive match; `Acc.recOn`, `ndrec`, and `ndrecOn` remain wrappers over the sealed head. Translate and typecheck
`WellFounded.recursion`, `fixF`, and `fix` in an atomic staging transaction before applying exported opacity. Synthesize
`fixF_eq` and `fix_eq` as checked applications of the generic primitive equation, extracting their minor and
accessibility arguments from the checked wrapper-body patterns rather than resolving helper names. Require the proofs
to check against the exported theorem types, then publish them through ordinary proof canonicalization. Retaining a
literal `Acc.intro` does not install recursive ι-reduction, because the recursive child is proof-valued and cannot be a
metric. Everything downstream that merely uses the equation lemmas translates unchanged.

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
- **M1 — core prelude.** The `Init` closure typechecks end-to-end (exercises T1/T2/T3, K2, K3, K4,
  K6, and the K7 capability required by exported `propext`/choice assumptions). Acceptance: zero
  unpatched failures; perf baseline recorded.
- **M2 — `Mathlib.Logic`.** K7 axioms are exercised at Mathlib scale; classical reasoning,
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
4. **Resolved:** Native-op defeq steps are trusted outright, following Lean's kernel stance. The
   trust applies only to exact reserved identities installed by the bundled Prelude or T1's
   explicit pinned translated-`Init` bootstrap mode; ordinary export streams receive no such
   authority. Structural differential/equation tests remain engineering backstops, not admission
   checks or proofs.
5. **Open:** P1 laziness — only if M3 measurements force it.

## 9. Non-goals

Surface-source porting, tactics, `simp`, elaborator compatibility; a live-development Mathlib
(the translated artifact is a frozen library — new development happens in Raccoon proper);
kernel-level recursive `Acc` ι-reduction and K-like reduction on neutral proofs (excluded *by
design* — they are the undecidability channels); univalence (kernel-theory §4: not planned).
