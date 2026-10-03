# Compositional state-machine experiment

Status: **checked language-design experiment**, 2026-10-02.

For the fragment tested here, ordinary Raccoon types and propositions support the proposed machine contracts:
opaque callbacks, independent resource instances, scoped loans, actor footprints, runtime branches, and nested
runtime loops with changing payloads. A proof-producing lowerer connects the same structured program to its
CUDA AST. The initial experiment required no checker changes, new axioms, or changes to eager evaluation.
The [extensible follow-up](../extensible-machines/README.md) adds a small exclusion-checking improvement and
removes the redundant stored footprint certificate from this experiment.

This supports a machine-oriented source interface elaborating to ordinary core terms. It does **not** establish
that all GPU protocols can use this representation, or that native machine judgements would have no benefits.
One attempted derivation initially exposed an indexed-elimination limitation; the follow-up now resolves it
and derives the footprint from the meaning certificate. The target connection is a checked correspondence to
emission templates, not a soundness theorem for CUDA or PTX.

## The discriminating example

The first [experiment](../state-machines/README.md) checked finite histories and generic history composition.
This experiment asks whether the approach still works when a client cannot inspect its callbacks, and when
execution depends on runtime values that the eager generator does not know.

The kernel has two buffers of exactly the same shape, owned by different warpgroups. Each starts with 128 values
of 1. It accepts a runtime count `n` and a runtime Boolean `flag`. Each outer iteration:

1. Splits the 512-thread CTA's register allocation into 192/192/72/56 registers per thread.
2. Runs two abstract role callbacks, one per buffer/owner. Each borrows its buffer and generates an inner loop
   of `n` iterations. A role reads once per iteration, except that `flag = true` causes two reads on iteration 0.
3. Closes the loans, joins the roles, restores the register allocation, and executes the restoration barrier.
4. Rewrites both buffers to 2 and publishes them with a barrier.

The outer loop's invariant says the CTA is uniform and both buffers are ready. Each inner loop preserves an
active loan. Neither invariant fixes the accumulated payload. With `n = 3`, each active thread accumulates 20
when `flag` is true and 15 when it is false. The generated program contains three runtime loops, regardless of
the eventual count, and writes the accumulators to `out`.

The interface actually checked by `Client.construct` is:

```raccoon
(left: (l: Lifetime) -> Gpu.Buffer(l, 0, 0)
  -> Gpu.Local(l, 0, 0, BufferModel.at(BufferModel.Phase.ready), BufferModel.at(BufferModel.Phase.reading)))
(right: (l: Lifetime) -> Gpu.Buffer(l, 1, 1)
  -> Gpu.Local(l, 1, 1, BufferModel.at(BufferModel.Phase.ready), BufferModel.at(BufferModel.Phase.reading)))
```

The client receives neutral function parameters. Its checked definition calls each through that interface,
composes the split with publication, and builds the outer loop. Proving safety does not inspect the callbacks.
Lowering later traverses their returned program descriptions.

`Roles.worker` provides a concrete implementation. Its callback constructs a loan-scoped command description
once, during eager generation. The generated loop executes that description at runtime. `Examples.everyRuntime`
proves the outer invariant for every modeled runtime input; the evaluations for 0 and 3 are additional probes,
not the basis of the loop proof.

## What a machine judgement elaborates to

The proposed source judgement is a Hoare contract with resource, actor, and lexical-scope indices:

```text
command at scope l, touching buffer id for actor a : P -> Q
```

`Gpu.Local(l, id, a, P, Q)` carries three pieces of checked information:

- A structured program tree: sequence, branch, first-iteration branch, loop, and primitive operations.
- A semantic function `Runtime -> State -> Outcome(State)` and a `Meaning` proposition connecting it to that tree.
- A universal safety proof: `forall runtime state, P(state) -> Post(Q, run(runtime, state))`.

`Footprints.fromMeaning` derives an `Owns(id, a, tree)` proposition giving the actor/resource footprint of every
primitive, including inside loops. It is exposed through `Gpu.localFootprint`, without an additional stored proof.

`Post` is false for a fault, so safety also excludes modeled protocol faults. `Gpu.Whole` carries analogous
information for the uniform CTA and its two resource slices. The scoped constructors are sealed. `Gpu.Program`
is an unscoped final description containing `Meaning` and a ready-to-ready safety theorem.

| Source rule | Ordinary-core representation | What is checked |
|---|---|---|
| Primitive transition | Semantic function, transition proof, syntax/semantics witness | Its stated precondition excludes a modeled fault and establishes the postcondition |
| Sequence | Common intermediate predicate and `sequenceSafe` | The second command receives the first command's established state |
| Runtime branch | Two commands with the same contract and `branchSafe` | Both runtime choices establish the result; their payloads may differ |
| Runtime loop | A body with contract `I -> I` and `repeatSafe` | All counts, all iteration indices, and all states satisfying `I` |
| Abstract callback | A function returning a certified command | The caller needs the returned contract, not the implementation |
| Actor restriction | Resource/actor indices and an inductive footprint certificate | No primitive in the returned tree is assigned to a peer resource or actor |
| Independent resources | Product-state semantics and `parallelSafe` | Each callback receives only its own state slice |
| Frame | `Invariants.frame` | An arbitrary safe computation on one slice leaves an arbitrary peer slice exactly unchanged |
| Loan | Fresh lexical scope and a scoped lease/command family | A loan command or a closure capturing the lease cannot escape its lifetime |
| Closing a borrow | Trusted composition of begin/body/close | Only the complete ready-to-reading description loses the loan scope |
| Register split | Existing `Registers.fits` evidence plus both role contracts | Counts fit the pool, and both role endpoints permit join/restoration |
| Emission | `Emission.Whole(tree, binding, start, block, next)` | The target AST follows the templates for this very tree, with correctly bound loop indices |

The generic composition, loop, and frame proofs are checked with unknown semantic functions and predicates.
They are not enumeration procedures over the example's histories. `Separation.independentOrder` also proves
that combining the two independent outcomes in either order gives the same result. It does not prove a theorem
about every instruction-level GPU interleaving.

The command descriptions are ordinary immutable values and can be copied. Sequencing their transitions must
still meet the intermediate-state contract: a second ready-to-reading command cannot follow the first without
republication. This experiment represents ownership through program contracts; it does not add a linearity
annotation to these descriptors or replace the existing language's rules for effectful values.

## Where the propositions come from

The buffer protocol is:

```text
ready --beginRead--> borrowing --read--> borrowing --close--> reading
writable --write(value)--> ready
```

The root split accepts two ready-to-reading roles. Its semantics combines their independent results, joins and
restores the CTA, and grants writable endpoints. This rule requires both local safety proofs and the budget
proof in its `Meaning.split` introduction. The target template contains the join barrier, register restoration,
and final restoration barrier. Granting writable endpoints is justified by that modeled primitive contract;
it is not derived here from a general CUDA operational semantics.

This gives the useful “could only have arrived through these operations” interface through an explicit
inductive program/transition relation. A client can use safety, footprint, and framing propositions directly.
There is no need to reflect the *entire Raccoon typing relation* to obtain them in this fragment. Reflection
could still help connect existing effectful library implementations to comparable contracts.

Scope still contributes a separate fact: the eager builder cannot retain a lease in a command or closure past
the lexical loan. The modeled phase expresses the runtime protocol; the lexical lifetime expresses capture
and escape restrictions. The experiment uses both. It does not show that a phase machine alone replaces scopes.
Pure AST data and certificates can be read out through the interface; escaping a description is different from
escaping an active lease. A complete runtime program still needs a checked protocol history.

Sealing limits introduction and lifetime elimination for the convenient source interface. The final `Program`
constructor is public: an expert can supply a raw tree, but must also supply its matching semantics and universal
safety proof. Thus the certification route can admit programs built through explicit proofs as well as through
the sealed combinators.

## The connection to emitted code

`Emission.local` and `Emission.whole` are total, structurally recursive lowerers. Each returns a target block
together with a proof of its emission relation. Sequence and branch rules thread a fresh-symbol counter.
A loop allocates its own symbol and passes that binding to its body, so an inner read or first-iteration branch
cannot be certified using the outer loop's index.

`Artifact.compile` binds the certificate to the actual `Cuda.Kernel`, including declarations, initialization,
and output. `Artifact.render` supplies launch bounds of 512 threads with residency 1 to the existing `Cuda`
renderer. The retained [generated.cu](generated.cu) is the result, not a separate manually maintained program.

The trusted target assumptions are the authoritative templates in `Emission.rac`, the shell in `Artifact.rac`,
and the existing CUDA renderer. The proof establishes template correspondence; it does not independently prove
the machine meaning of `setmaxnreg`, barriers, or loads. Host C++ syntax checking rewrites inline assembly to
operand-checking stubs. Neither CUDA/PTX compilation nor hardware execution is part of this experiment.

This explores remedies 4 and 5 in `gpu/encoding/REGISTERS.md` §9: checking the emitted AST and placing rendering
after construction of a certified program. The machine model, source interface, and lowering do not need an
import cycle. It does not implement shared sealing or solve the original mutual-minting pattern. Arbitrary
`Cuda.Kernel` values can still be rendered by the existing general renderer; this experiment's safety claim
applies to the certified entry point, not every CUDA string someone can construct.

## What resisted the encoding

The successful encoding was not completely automatic:

- Predicate arguments to generic command constructors need explicit annotations in some places. The checker
  cannot infer arbitrary predicates from a reduced `Safe` proposition. This is annotation/elaboration work.
- A proof lambda capturing a scoped command inherits its lifetime even when it only reads the command's pure
  fields. Calling the generic, unscoped composition theorem with those fields avoids this capture.
- Matching a neutral function application does not automatically rewrite other occurrences of that application.
  The generic proofs eliminate a named `Outcome` or use explicit helper theorems.
- The footprint derivation initially failed because an unsupported function-index quotation prevented the
  checker from using a contradictory syntax index. The follow-up lets checked refutations use a quotable subset
  of the index equations. `Footprints.fromMeaning` now checks by structural induction, and
  `checks/derived_footprint.rac` accepts a generic use of it. The interface no longer stores `Owns` alongside
  `Meaning`. The first experiment's separate direct backlink limitation remains.

This is a proof-usability improvement in ordinary indexed elimination. It does not introduce a machine semantic
judgement or reflection of the full typing relation.

## Checks and remaining questions

Run from the repository root:

```sh
python3 experiments/compositional-machines/run.py
```

Set `RACCOON` to the CLI command, or prepare the JVM classpath with `sbt graalvmNativeImageClasspath`.
The runner checks every module, verifies expected diagnostics at the intended fixture definition, regenerates
CUDA, and syntax-checks it with the GPU stub headers when `clang++` is available.

There are 13 accepted modules, one accepted generic footprint derivation, and 20 expected rejections:
wrong instance/lease, swapped roles, a peer effect, wrong actor, escaping loan command or closure, wrong kernel
lifetime, non-invariant loop, incompatible branch, first-iteration-only validity, premature write, read before
republication, register over-allocation, forged command introduction, fake semantics, wrong emitted buffer,
wrong emitted index, unrolled loop replacement, omitted restoration barrier, and an unrelated kernel shell.

Validation also passed the first experiment's 69 checks and `sbt -batch validate` (930 tests, including the follow-up
refinement checks). The generated kernel passed the host C++ syntax check; no hardware result is claimed.

Important bounds on the result:

- Resource identity is tested with two distinct builder-issued slots of identical shape and separate lexical
  kernel lifetimes. Runtime allocation, arbitrary fresh instances, aliasing views, and dynamic footprints are
  not modeled.
- Actors are four fixed warpgroups in one CTA, with buffer work confined to groups 0 and 1. Hierarchical actor
  restrictions, CTA-pair leaders, cross-CTA memory, and arbitrary synchronization protocols remain untested.
- The buffer contents are uniform values; loads are in bounds by `% 128`, and the modeled accumulator wraps
  modulo `2^32`. This is not a general memory model. The shell's initial state and primitive hardware meanings
  are assumptions of the target correspondence, rather than independently verified refinements.
- The proof covers modeled protocol safety and payload-dependent control. It does not establish liveness,
  deadlock freedom, race freedom against a hardware semantics, register/spill behavior, or numerical GPU output.
- The DSL is a closed subset. It has no machine-declaration parser, source elaborator, native machine judgement,
  automatic invariant discovery, extension mechanism for arbitrary machine families, or migration of the
  existing GPU library. The AST is retained on commands; reflection on every Raccoon value is not implemented.

The next language-design commitment supported by this result is a source interface that elaborates contracts,
footprints, structured code, and their certificates. Keep eager generation, require contracts on abstract
callbacks, and let runtime loops preserve a predicate rather than a representative payload. This experiment
avoids the representative-state generation interface; it does not justify removing `Fixed` from existing
combinators that still use that interface. Quoting and the interpretation of implicits need no change for this
construction.

The [extensible follow-up](../extensible-machines/README.md) now checks generic machine definitions, fresh
allocation identities, changing generation indices, and a production Core AST bridge. Dynamic ownership and
cross-CTA synchronization remain discriminating tests before committing to new core machine semantics.
Full CUDA refinement remains its own proof project.
