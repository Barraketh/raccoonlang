# Reflected typing and library safety

Status: **candidate implementation plan** (2026-10-02). Proposed direction for problem 1 of
[Safety problems](SAFETY_PROBLEMS.md). No part of this feature is implemented by this document.

The subsequent [state-machine experiment](../../experiments/state-machines/README.md) tests a smaller proof
interface before committing to this architecture. Its protocol histories, backlinks and invariant proofs check
in the existing core without full typing reflection. It also exposes the separate obligations for live authority,
captured scope dependencies and emission correspondence. This plan remains a candidate for broader theorems
about arbitrary checked client code; it is not the selected implementation direction.

The [compositional follow-up](../../experiments/compositional-machines/README.md) now checks opaque callbacks,
scoped loans, actor footprints, runtime loop invariants with changing payloads, and proof-producing AST lowering
in ordinary Raccoon. That supplies ingredients for elaborating machine contracts before adding a native judgement for this
fragment. It also records an indexed-elimination limitation and the remaining gap to CUDA semantic refinement.

The [extensible experiment](../../experiments/extensible-machines/README.md) adds generic machine families,
fresh allocation identities, generation-indexed loop progress, and equality with an actual Core-generated body.
Its [source-interface proposal](../../experiments/extensible-machines/SURFACE.md) recommends elaboration to
ordinary core terms for this fragment. A small exclusion-checking improvement now permits the earlier footprint
derivation. Broader typing reflection remains an option for arbitrary existing clients and effects outside the
certified command interface; hardware refinement and asynchronous completion remain separate obligations.

The [TinyGEMM comparison](../../experiments/machine-core/README.md) now ports a real client to an independent
library, with a complete kernel equality and local/composite protocol theorems. It also records Core's full
guarantee set and the missing features for A3b attention and persistent pair GEMM. Those ports and a broader
semantic argument are still required before claiming the command interface replaces Core or simplifies all
its proofs.

The aim is to make Raccoon's typing relation available inside Raccoon, connect proofs to actual checked
definitions through reflection, and prove a composition theorem for libraries that assign resource meanings to
their abstract types. The GPU library is the first intended application. Its existing token encoding should be the
starting point for verification, with correctness proofs alongside the implementation.

The user's preference is for a simple language and implementation, with changes where they substantially simplify
the argument. Preserving the current feature set is not a requirement. In particular, quoting and moving implicit
inference into elaboration are options to evaluate. The plan separates those choices so that a useful kernel
simplification does not require a broader change to the surface language.

## Intended result

A library proves that its operations respect a chosen interpretation of its types. A general theorem then says
that every well-typed client composes those operations safely. Reflection supplies the typing evidence for a
particular client, so its proof is an application of that theorem.

The eventual GPU theorem should have this shape. Names and notation throughout this document are schematic;
they are not proposed surface syntax.

```text
LibraryCorrect(environment, interface, interpretation)
ArtifactTyping(clientArtifact, Program)
EvaluatesTo(clientArtifact, generatedKernel)
-----------------------------------------------------
SafeKernel(generatedKernel)
```

The artifact identifies the actual checked code and its environment. `EvaluatesTo` connects that generator to the
CUDA AST it produces. `SafeKernel` refers to a semantics of that AST under stated hardware assumptions. Checking
Raccoon code and checking CUDA structure are separate premises in this argument.

For the initial GPU result, keep the safety claim of `gpu/OBLIGATIONS.md` §1, which excludes liveness. Named runtime
values and deadlock freedom remain separate projects. This work may provide a foundation for them, but does not
establish them automatically.

## Proposed proof architecture

Use unrestricted data for syntax, contexts, certificates, and modeled evaluation states. A description of a linear
value is ordinary data; it cannot be applied, redeemed, or decoded into that value. Keep live linear values out of
types and proofs.

Define the typing relation as an ordinary inductive proposition, with one rule per inference rule:

```text
Typing(environment, origin, unrestrictedContext, linearContext,
       openScopes, expression, typeCode) : Prop
```

Types are expressions in the reflected calculus. Kinds, lifetimes, and levels have explicit codes and normalization
rules. A linear context records variable identifiers and type descriptions, not tokens. Whether a variable is
tracked is fixed at its binder, as in the current checker; later refinement does not change that decision.

Use a separate certificate datatype in `Type` when validation needs to inspect derivation data. A validator checks
the certificate against a specified judgement, and its soundness theorem produces `Typing`. This avoids asking
proof-irrelevant evidence to retain computational information.

```text
validate(environment, judgement, certificate) = true
--------------------------------------------------
Typing(judgement)
```

Certificate search can run in Scala. Its output gains authority only through validation against the reflected
rules and ordinary proof checking. Start with a structurally recursive validator for finite certificates; a total,
complete implementation of dependent type inference inside Raccoon is not the first requirement.

The full relation includes declaration formation, environment validity, conversion, termination obligations, and
the relation between checked code and executable code. Merely certifying the linear ledger does not justify the
whole typing judgement. Each incomplete milestone must state its supported fragment explicitly.

The main derived interfaces are:

- **Authorized representation access:** constructor and eliminator code for a sealed family originates in its
  defining module, including authorized compiler-generated uses.
- **Resource accounting:** evaluation preserves the assignment of linear resources through arguments, closures,
  constructor fields, and results.
- **Scope confinement:** surviving executable values cannot provide access to a closed scope.
- **Library composition:** well-typed clients preserve a library-supplied interpretation of its abstract types,
  provided the library's accessible operations satisfy their contracts.

The first three can be exposed as convenient propositional interfaces. Their meanings differ: sealing governs
representation access by implementation code, while scopes govern the availability of values. A client may call
a public allocation function whose implementation uses a sealed constructor.

## Design audit before implementation

Run a small comparison before committing to the reflected core. The question is which representation gives the
fewest semantic rules and the clearest proof of composition while retaining useful source behavior.

### Implicits and explicit core applications

Compare three designs:

| Design | Kernel application | Main proof obligation |
|---|---|---|
| Current readout | Stores explicit arguments; reconstructs implicits by compiled projections during evaluation | Projection stability under substitution, admissible read positions, and scope accounting for reconstructed arguments |
| Forced inference in elaboration | Retains the surface requirement that implicits are recoverable; inserts all inferred arguments into core code | Correct insertion, ordinary application typing, and any subsequent erasure |
| General inference in elaboration | Uses metavariables and constraints; inserts all solved arguments into core code | Ordinary application typing; inference heuristics need not become kernel typing rules |

**Recommended candidate to test first:** retain forced surface inference and use explicit core applications. This
isolates the likely simplification: the evaluator and object typing relation no longer reconstruct omitted data
arguments. It does not require adopting general inference or expected-type-directed checking.

The current readout design remains a serious candidate. `Projection.scala` shares one implementation between
checking and evaluation, and application checking revalidates the projected arguments. Formalize a representative
projection rule before deciding that its proof burden is excessive. Pay particular attention to substitution,
function closure scopes, sealed-field projection, and the prohibition on reading blocked application arguments.

In both candidates, distinguish data implicits from evidence. Erased evidence still needs justification, and
canonical proof reconstruction still needs a semantics. Inserting all arguments does not make those obligations
disappear.

Choose explicit insertion only if it removes substantially more machinery than typed readback and the elaboration
boundary introduce. Count the semantic cases and substitution lemmas, and measure checking and evaluation cost.
Retain readout if its stability proof is small and the alternative mostly relocates complexity. Moving argument
inference also does not require changing the current rule that a term's type is synthesized independently of the
expected type.

### Quoting values and reflecting code

These are separate facilities:

- **Code reflection** captures a declaration's code, signature, origin, and dependencies before evaluation erases
  information. Every design needs this, even if value quoting remains absent.
- **Value quoting** converts a typed semantic value back into a core expression. It may simplify materializing
  inferred arguments and type annotations for an explicit core.

Prototype typed readback only if explicit insertion needs it. Its contract must state that the result is well
typed, denotes the original value, and preserves relevant scope and declaration identities. Cover open neutrals,
exact binder groups, native literals, canonical proofs, closure annotations, and static scope atoms. Quoting a
semantic value is not a replacement for capturing the original code's module origin.

A returned expression containing a linear variable must be checked by the ordinary ledger in its enclosing code;
readback must not create an unrestricted executable copy of a linear closure. Reflection of syntax can be
unrestricted because it remains descriptive data.

### Other language choices

Record the proof cases introduced by dependent match refinement, nominal family principles, proof reconstruction,
large elimination, and declaration-level universe polymorphism. Consider changes when a concrete example shows
that they remove substantial machinery. Choose a universe and trust boundary for the semantic theorem rather than
promising a proof of Raccoon's entire logical consistency inside itself.

Keep local synthesis, exact function groups, sealing, scopes, and proof irrelevance as the initial semantics to
model. Revisit any of them through the same comparison if the formalization exposes a significant simplification.

**Audit deliverable:** one decision note with two worked applications, a scoped callback, and a dependent match;
the rules required by each candidate; the observed changes to accepted programs and generated CUDA; and a chosen
core. Temporary prototypes are experiments, not permanent parallel implementations.

## Checked declarations and reflection

The current `TypeChecker.CheckedTerm` contains an evaluated value and a residual term. `Interpreter.evalDecl`
publishes the value in `Env`; globals do not retain a complete checked declaration artifact. Checked applications
drop implicit arguments and supplied evidence, while lambdas retain derived captures and recursion metadata.

Add a compiler-owned declaration record at successful publication. It should retain:

- resolved input code and checked signature;
- checked code and, if different, the residual executed by the evaluator;
- sufficient evidence for elaboration, inferred arguments, discharged evidence, and erasure;
- declaration identity, module origin, binder identities, and scope-node identities;
- the dependency environment and selected prelude's trusted-surface manifest;
- the certificate and the supported calculus version.

Publish records atomically with declarations, including mutual groups. Failed or skipped declarations publish no
record. Prelude declarations participate too, with native and axiomatized entries distinguished from checked
bodies. Generated selectors and synthetic proof code need explicit origin rules.

If checked and executable code differ, certify the transformation:

```text
Typing(environment, checkedCode, typeCode)
ErasesTo(environment, checkedCode, executableCode)
```

For the readout candidate, this must account for projection-based reconstruction at execution. For an explicit
core, it covers proof erasure and any argument erasure. Do not typecheck a convenient reconstruction and silently
treat it as the code that ran.

Initially export records through a developer-facing command and load them as Raccoon data. Once the format and
validation are stable, add a declaration reflection form that resolves an already-published declaration and exposes
its authenticated record and typing proof. Reflect closed declarations first; support open syntax only after its
context and binder mapping are specified.

Users may construct arbitrary syntax and prove hypothetical judgements about it. Only the compiler's capture
boundary connects a record to an actual declaration. A source-supplied module name or hash must not authenticate
that connection. Content hashes may index caches; structural identity and the captured dependency environment
determine correctness. Reflection of the same artifact must be deterministic.

The initial public reflection interface has no operation that decodes arbitrary reflected syntax into an actual
Raccoon value. A modeled evaluator may return modeled values. Any later syntax-splicing feature must check inserted
code at the caller's origin; copied origin labels must not authorize sealed constructors. This distinction prevents
reflected representations from becoming a way to mint real capabilities.

## Trust boundary

The host proof checker remains trusted. Internal certificates make the object rules explicit and permit stronger
proofs about them; they do not independently verify the checker that accepts those proofs.

Bootstrap the syntax, relation, and validator as ordinary checked modules. Their initial validity rests on the
current kernel. Later reflection may describe them, but certificate validation must not assume the very certificate
it is validating. Recursive declarations use a checked group rule, not a cycle of assumed declaration-validity
proofs.

| Boundary | Required statement |
|---|---|
| Object rules | Match the chosen language semantics, including declaration validity and conversion |
| Certificate generation | May propose data; acceptance comes from the validator's soundness theorem |
| Reflection capture | The artifact is the actual published declaration, with the actual environment and origin |
| Executable code | Checking and erasure preserve the behavior modeled by the semantics |
| Bootstrap | The selected prelude satisfies explicit consistency, sealing, linearity, lifetime, and native-equation obligations |
| Library | Accessible operations preserve their advertised semantic contracts |
| Hardware | The CUDA transition rules describe the stated platform assumptions |

Use relative theorems with named assumptions where the enclosing logic cannot establish its own complete
metatheory. The implementation must report these dependencies. A theorem for a bounded fragment must not be
presented as a theorem for all Raccoon programs.

Proof canonicalization must not manufacture missing certificate validity. In particular, raw certificate fields
belong in unrestricted data, while a proof of their validity is produced only after the corresponding proposition
has been checked.

## Implementation stages

### Phase 0 Choose the reflected calculus

Inventory the rules in `docs/kernel.md` against the checker, evaluator, and bootstrap. Write down the judgement
signatures and their dependencies. Perform the design audit above, with the current readout path and explicit core
applications as the first comparison.

**Complete when:** the chosen core, supported initial fragment, reflection boundary, and relative assumptions are
specified, and every current language feature has either a planned rule or an explicit coverage gap.

### Phase 1 Implement syntax and a small typing relation

Proposed destination: ordinary Raccoon modules under `meta/`, with separate modules for syntax, contexts, annotation
algebra, typing, certificates, and certificate validity. Names can change before implementation.

Start with variables, declared constants, sorts, explicit dependent function groups, lambdas, applications, lets,
simple inductives and matches, and scopes. Include linear closure capture and module-origin checks from the start.
Use explicit binder contexts; the syntax must not accidentally capture host-language variables.

Define conversion relationally and check finite witnesses for the supported reduction and equality rules. Do not
accept a host Boolean saying two values were equal as a conversion proof. More sophisticated conversion rules can
be added with their justifications in phase 4.

Prove certificate-validator soundness for this fragment. Prove the small context and substitution lemmas needed
by the next phase rather than building a general tactics framework first.

**Complete when:** positive examples have checked typing proofs, malformed certificates fail, and unsupported
forms are identified explicitly. A proof cannot retain a live token or execute a modeled constructor.

### Phase 2 Capture and certify actual declarations

Implement declaration-record retention and certificate production at the current checking boundaries. Keep one
authoritative host implementation of each rule. Existing rule functions may return the information needed for a
certificate; avoid a second Scala checker that independently rediscovers their decisions.

The exporter must preserve syntactic origins and identities. Where an inferred type exists only as a `Value`, use
the chosen typed readback or a specified symbolic reconstruction; do not invent an unchecked alias. Record erased
evidence and the justification for generated operations.

Use small closed declarations for the first reflection tests. Then cover cross-module calls and dependencies.
Introduce the user-facing declaration reflection form after export and validation agree.

**Complete when:** a certificate for an actual declaration validates in Raccoon, changing its code or dependencies
invalidates the certificate, and changing a module label cannot authorize a previously forbidden access.

### Phase 3 Prove the structural resource guarantees

Define an operational semantics for the supported checked code, including evaluation of dependent annotations
where it can affect behavior. Use explicit environments and closures. Model resource identity with ghost labels,
not equality of token representations: two fieldless tokens may have identical representations.

Prove resource accounting and confinement for finite evaluation prefixes, together with the required substitution
and closure lemmas. Resource accounting includes transfer into results and closures. It does not say every input
token is immediately destroyed, nor does it assert termination.

The scope model must respect today's static identity: one scope node denotes the same atom on repeated evaluation,
including recursion. Track activation and accessibility without silently changing to fresh runtime lifetimes.
State confinement as absence of executable access after closing; the current semantics permits inert descriptions
of atoms in proofs and blocked computations.

Prove representation-access authorization with correct treatment of public calls, generated selectors, evidence
discharge, implicit projection where retained, structure eta, and proof reconstruction.

**First useful demonstration:** certify the actual definitions in `examples/leases/Lease.rac`, then prove that
well-typed clients of their interface account for issued tokens and cannot use leased access after its scope.
If those definitions need features beyond phase 1, add those rules before claiming this demonstration is complete.
The example's copyable lease permits repeated token issuance; do not claim that it represents one exclusive
physical allocation.

**Complete when:** this demonstration uses reflected definitions and generic lemmas, and its reuse, drop, escape,
and unauthorized-constructor variants fail at the expected premise.

### Phase 4 Cover the full chosen kernel

Extend the relation, certificates, validator, and proofs together. Cover:

- kind, scope, and level polymorphism, including declaration-level large types;
- implicit reconstruction if retained, or explicit insertion and typed readback if selected;
- evidence discharge, canonical proof reconstruction, proof irrelevance, and allowed elimination;
- indexed and mutual inductives, positivity, universe bounds, and family kind and scope containment;
- dependent match refinement, checked constructor exclusion, and nominal family principles;
- structure eta, destructuring, generated selectors, and native literals;
- structural, measure, and mutual recursion, including termination evidence;
- trusted prelude axioms, quotients, native operations, and custom prelude manifests.

Reuse ordinary checked exclusion proofs where possible. Keep the trusted nominal premises and any new assumptions
visible. Certifying branch exclusion alone does not certify refinement links or substitutions.

Maintain a coverage table for term and declaration forms, conversion rules, and bootstrap cases. Unsupported forms
have no fallback that grants a typing proposition from host acceptance alone.

**Complete when:** every feature of the chosen kernel has a rule and its required justification; reflected proofs
cover the repository's relevant examples and GPU dependencies; and the structural theorems state their exact
bootstrap assumptions. Update language and kernel references only for changes actually implemented.

### Phase 5 Prove composition for interpreted library types

Build a small resource algebra and program logic inside Raccoon. Semantic assertions describe ownership in a
modeled world; ordinary proof duplication does not duplicate the resources described by an assertion. Define
separating composition, validity, and frame-preserving transitions explicitly.

Give abstract types interpretations over modeled values, resources, and accessible scopes. Linear values may
describe exclusive obligations. Copyable scoped values may describe shared access whose validity ends with the
scope. Copyable values and proofs require meanings compatible with their permitted copying and erasure.

Define `LibraryCorrect` for the actual reachable interface. Include unrestricted handles and capability keys, such
as `Core.Key`, rather than assuming all public helper names are client-callable or ignoring indirect ways to reach
them. Verified internal bodies may use representations; clients receive only the operations justified by the
interface theorem.

Prove the fundamental composition theorem by induction over typing evidence. Its conclusion is semantic typing:
the program preserves the chosen interpretation. Add adequacy lemmas connecting that property to a concrete safety
claim. Use a small resource library as the first application before bringing in CUDA.

**Complete when:** a verified implementation with a sealed interface supports arbitrary well-typed client
composition through the theorem, and a well-typed implementation that violates its contract cannot obtain
`LibraryCorrect` merely from its typing certificate.

### Phase 6 Verify the conditional callback pilot

Define a relational semantics for the minimal CUDA AST fragment needed by `Core.onLeader`: expressions, rank tests,
blocks, register declaration and assignment, and an abstract completion operation with per-CTA obligations.
Connect it to the existing typed AST in `gpu/Cuda.rac`. An executable evaluator can implement those same transitions
and prove its step function sound against the relation, following `gpu/EVALUATOR.md`.

The generator proof must describe both the code accumulated in `Ctx` and what that code means when GPU threads
execute it. Emitting a callback once is distinct from its emitted body executing in each CTA.

Prove the contract of the actual reflected `Core.onLeader`, with verified contracts for its transitive helpers.
Cover all three relevant restrictions: the callback cannot capture outer linear obligations; explicit `sides` have
the meaning justified by `LeaderOnly`; and the arm cannot export leader-only register state or scoped access.

Retain the historical buggy callback type as a negative verification example. Its typing proof should succeed.
Construct a concrete modeled client in which the peer CTA skips its required completion operation, and prove that
the advertised contract fails. A missing proof attempt alone is not a counterexample.

**Complete when:** the current implementation satisfies the specified contract, the buggy implementation has a
checked counterexample, and the result refers to the captured code and emitted AST rather than a handwritten
replacement for either. State the pilot's abstraction of completion operations; it is not yet the complete
hardware safety proof.

### Phase 7 Extend to the GPU safety claim

Expand the semantics using `gpu/MODELS.md`, the resource meanings in `gpu/SEPARATION_PILOT.md`, and the operation
obligations in `gpu/OBLIGATIONS.md`. Verify one protocol family at a time: allocation and lending, synchronous
memory operations, stage rings, asynchronous completion, accumulators, output stores, then register protocols.

Carry runtime protocol state in the interpretation of modeled token representations and associated registers.
Do not require adding proof fields to every live token merely to expose those meanings.

Integrate the existing structural checker proofs from `gpu/Spec.rac` and `gpu/proofs/`. They remain useful premises.
Connect the emitted AST to printed CUDA through the relevant printer correctness lemmas and explicit remaining
lowering assumptions. A theorem about the AST alone does not establish that every printed instruction has its
modeled behavior.

Apply composition to a small existing kernel first, then the other examples. Where a real invariant is missing
from an API, repair the encoding for that reason and record the counterexample. The goal of preserving the encoding
does not require proving a false claim about it.

**Complete when:** the stated GPU safety claim follows from verified operation contracts, reflected client typing,
generation and printing correspondence, and an enumerated set of hardware and bootstrap assumptions. Deadlock
freedom requires an additional theorem and fairness model.

## Validation and implementation locations

Likely Scala integration points are `CoreAst.scala`, `TypeChecker.scala`, `Interpreter.evalDecl`, `Env.scala`, and
`ExecutionPhase.scala`. The implicit-design comparison also touches `telescope/Projection.scala`, binder checking,
and `Interpreter.residualArguments`. Sealing, annotation containment, and ledger decisions remain owned by their
current rule implementations until a chosen redesign replaces them.

Add focused tests for certificate tampering, origin forgery, stale dependencies, failed-declaration publication,
scope identity under recursion, closure captures, erased evidence, and custom preludes. For each semantic
guarantee, include an accepted example and a minimal rejected or semantically refuted variant.

Run `sbt validate` for implementation changes, plus `gpu/check.sh` whenever kernel behavior or GPU proofs change.
For a redesign that intends to preserve source behavior, compare diagnostics and generated CUDA against the
baseline. Classify every difference; deliberate language changes need new documented expectations rather than an
unconditional compatibility promise. Measure certificate size, retained-code memory, validation time, and repeated
reflection cost on the lease example and a representative GPU generator.

## Order and decision points

The dependency order is phase 0, then phases 1 and 2, then the structural demonstration in phase 3. Full kernel
coverage in phase 4 is needed before certifying an unchanged GPU implementation. The semantic framework in phase 5
can grow from the smaller proven fragment while coverage expands. Phases 6 and 7 apply it to generated code.

The first implementation commitment should end at the lease demonstration, not at a complete GPU semantics. It
answers whether the typing proposition is usable in Raccoon, whether reflection binds it to actual code, and
whether the implicit/readback choices produce a tractable proof. The next commitment should end at the
`onLeader` contract and checked counterexample. Broad GPU verification follows once both demonstrations work.

Do not assign calendar estimates until phase 0 and the first certificate prototype establish the cost of the
chosen core. The largest uncertainties are dependent conversion and refinement certification, the treatment of
the surrounding logic, and the bridge between generation-time resource flow and runtime thread behavior.

## Precedents and reading

[RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf) supplies the closest model for assigning ownership and
lifetime meanings to types, verifying library boundaries, and deriving safety for well-typed clients.
[A Logical Approach to Type Soundness](https://cs.au.dk/~timany/publications/files/2024-jacm-accepted-logical-type-soundness.pdf)
explains the semantic soundness and abstraction argument in a pedagogical form.

[Coq Coq Correct](https://www.ps.uni-saarland.de/Publications/documents/SozeauEtAl_2020_CoqCoqCorrect.pdf) supplies a
precedent for representing syntax and typing inside the host language and verifying a checker relative to explicit
metatheoretic assumptions. Its derivations carry data in `Type`; this plan separates such certificate data from a
public proposition.

[Foundational proof carrying code](https://www.cs.princeton.edu/~appel/fpcc.html) supplies the precedent for connecting
typing evidence to a reusable semantic safety theorem. Combining these ideas for Raccoon's generator and GPU
library is the proposed design, not a claim that those projects already prove this encoding correct.
