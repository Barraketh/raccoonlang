# Compact Nat values and uniform native reduction

## Purpose

Keep eager evaluation, ordinary `Nat.zero` / `Nat.succ` elimination and
structural induction. Use the same representation and reduction policy for
small and large natural numbers. Resume the GPU-library storage proof without
an unfolding lemma or changing its obligations.

The immediate regression is
`experiments/library-correctness/probes/NatBoundConversion.rac`: its dependent
Boolean elimination checks with 256 and fails with 257. A native call made
before refinement enters the source body; the identical call made after
refinement becomes opaque under `Packed.MaxUnfoldedLiteral`. The actual ring
bound fails at 9216. The previous positivity improvement is independent and
must remain in place.

## Representation

Ground Nats remain arbitrary-precision packed integers at the validated Nat
type. A symbolic Nat may additionally have a **positive packed successor
prefix**, representing `succ^offset(base)` with a `BigInt` offset. Bare neutral
values remain bare at offset zero. This does not require wrapping every Var
or rewriting the representation of other inductive families.

One smart constructor is authoritative:

- zero offset returns its base;
- a packed ground base adds the offset to its payload;
- a prefixed base combines the offsets;
- otherwise a positive offset builds one compact value.

Nested prefixes and prefixes over ground integers do not survive construction.
Counts never pass through `Int` or `Long` truncation. The value carries its exact
Nat type, dependencies and base; construction must retain existing layout
admission and constructor checks. It cannot grant native behavior to an
untrusted lookalike declaration.

## Matching and structural descent

One constructor view serves evaluation, checking, projection and termination:

- packed zero exposes `Nat.zero`;
- positive packed ground exposes `Nat.succ` with a packed predecessor;
- a positive symbolic prefix exposes `Nat.succ` with its prefix decremented
  through the smart constructor;
- an unprefixed neutral blocks ordinary matching.

No consumer allocates a successor chain to inspect a prefix. Constructing
`Nat.succ` uses the same smart constructor. A custom recursive function still
performs the iterations its source asks for; compact storage alone does not
accelerate arbitrary user recursion.

Structural termination must recognize prefix predecessors and its underlying
base as actual strict constructor subterms. Distinct bases cannot become
ordered merely by comparing their offsets. Preserve the existing treatment
of function applications of subterms and of ordinary inductives.

Implicit readout must see the same successor fields. Represent a repeated
predecessor path by one `BigInt` count; compiling or following that path must
not enumerate a large prefix. Admission retains the checked constructor and
seal requirements of ordinary field readout. This compresses an existing
structural projection and grants no inverse rule for arbitrary arithmetic.

## Native arithmetic

Remove `MaxUnfoldedLiteral` as a semantic rule. The magnitude of a literal
must not select source unfolding versus an opaque native call.

Ground operands retain the existing validated host equations and their
explicit resource limits for exponentiation and shifts. Mixed/symbolic
operands use uniform compact constructor rules and otherwise remain residual
applications of the exact native lambda. Residuals retain all blockers needed
to rerun after refinement; they use the same reducer on rerun.

Required compact reductions include:

- `add(a, literal(k)) = succ^k(a)` without k source iterations;
- `add(a, succ^k(b)) = add(succ^k(a), b)`;
- `ble(0, b) = true`;
- comparison of zero against a known positive prefix;
- cancellation of common known successor prefixes in `ble` and `beq`, in one
  numeric step, followed by the residual comparison of the remaining values;
- `blt(a, b)` agrees with `ble(succ(a), b)`;
- zero and constructor equations used by existing generic Nat proofs.

Do not introduce unrestricted commutative-polynomial normalization or solve
unknown Nat variables by guessing arithmetic inverses. Nat operations are not
generally injective. Extra compact rewrites must follow the actual trusted
operation equations, not merely resemble them.

## Conversion and source constructor equations

Uniform residual native applications must remain convertible to their
declared constructor equations where existing induction proofs require them.
For example `mul(a, succ(b))` must compare with `add(a, mul(a, b))`; an
explicit match implementing `ble(succ(a), b)` must compare with that native
call. Native residuals must not silently lose those proofs.

When a direct compact rule is insufficient, conversion may inspect one layer
of the exact checked source body. Recursive peers in that inspection must
refer to the published native residual heads, so inspecting one layer does
not eagerly run a million recursive iterations. This is demand during
conversion of a blocked computation; ordinary evaluation stays eager.
Keep the equation's source identity and typed environment rather than
recognizing arbitrary syntax by printed names. Compare under a
non-invertible frame, discard partial choices if comparison fails, and report
failure as stuck. Prevent repeating the same residual comparison indefinitely.
Do not restore a numeric cutoff under a different name.

If preserving these constructor equations requires a larger language change,
report the concrete failing proof before adding further machinery or
rewriting the proof around it.

## Integration invariants

The new value form participates in dependencies, occurrence/positivity
summaries, materialization, equality keys, structural comparison, printing,
constructor reconstruction and matching. Substitution rebuilds through the
smart constructor: substituting a literal for the base becomes ground;
substituting another prefix combines counts. Keys must agree for canonical
equivalent prefixes and obey the existing key-coherence checks. Mixed old
constructor representations must either canonicalize at their construction
boundary or compare correctly. Existing conservative positivity treatment
and scope/linearity checks are unchanged.

One implementation supplies these rules to all consumers. The Core evaluator's
scalar path and general application path must agree. Do not keep the old
size-dependent path as a compatibility mode. The test-only source evaluator
may remain to check the trusted host equations; it is not the normal reduction
policy.

Preserve the existing unboxed `Long` scalar fast path and its overflow
fallback to arbitrary precision. Uniform symbolic reduction does not require
allocating `BigInt` operands or packed values for ground operations already
handled by that path.

## Required validation

1. The minimal Nat bound and `RingStorageBound` reproducers check unchanged,
   including 256, 257, 9216 and larger literals with the same behavior.
2. Ground matching, symbolic prefixes, zero versus successor, predecessor
   binding, materialization and constructor/refinement proofs agree across
   small and large counts. Include a count beyond machine integer ranges.
3. Matching a huge prefix and adding a huge literal to a neutral remain
   compact; tests inspect shape as well as results. Generic structural
   recursion accepts genuine prefix descent and rejects unrelated bases.
4. Native constructor equations and explicit source selectors compare where
   existing Nat induction proofs need them. Unequal ground Nats stay apart;
   unknown arithmetic failures stay stuck. No impossible equality is accepted.
5. `Arithmetic.rac`, `RingStorageProofs.rac`, `RingLibraryProofs.rac` and the
   existing compiler soundness suites pass without proof detours. If an
   independent source-authoring error is exposed, distinguish it from a
   compiler barrier.
6. Run `sbt validate`; then the library experiment and GPU client checks,
   without overlapping sbt builds and CLI JVMs. Existing CUDA outputs stay
   byte-identical. Record any newly exposed friction and escalate it.

Root owns this design and the GPU obligations. Luna max implements compiler,
tests and the corresponding language documentation. Compiler implementation
must not modify the GPU proof/specification files to make a check pass.

## Integration barrier: occurrence information for native residuals

The unchanged Nat-bound reproducer checks with the implementation. The storage
reproducer instead fails in its unchanged `Regions` dependency: the result
index `Nat.add(base, bytes)` of `Regions.Layout.reserve` is rejected by
positivity checking. Uniform mixed reduction leaves this addition as a native
application. Existing occurrence analysis treats every native lambda as capable
of mentioning any global family, whereas the formerly evaluated source match
had precise occurrence information.

The initial proposal to reuse a native function's checked-source occurrence
summary was withdrawn. It preserved the wrong abstraction: ordinary Nat values
must not acquire positivity facts from their computation or source bodies.
The intermediate Pi and inductive-head occurrence design
was also withdrawn before implementation. The current approved replacement is
[declaration-time positivity](../implemented/DECLARATION_TIME_POSITIVITY.md): target-specific
walks memoized for each declaration, with native closure freshness checked
through its type, captures and environment. The full validation suite and
unchanged storage proofs must still be checked before calling the compact Nat
integration complete. The separate `Nat.blt(0, Nat.succ(m))` proof barrier is
recorded in that replacement spec and remains outside its scope.
