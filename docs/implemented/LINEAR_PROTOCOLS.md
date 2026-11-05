# Linear protocols

Status: **implemented** (2026-10-29). The rules are stated in the kernel
reference, which is authoritative: [Linear types](../kernel.md#linear-types),
[Resource protocols](../kernel.md#resource-protocols),
[Primitives](../kernel.md#primitives),
[The protocol library](../kernel.md#the-protocol-library),
[Axioms](../kernel.md#axioms) and
[Recursion on proofs](../kernel.md#recursion-on-proofs). This document records
what was built and why. It implements the protocol design of
`lemur-raccoon/resource_core.md`, which the decisions of §3 refine. The open
questions (§6) have fixed numbers, which other documents and code comments
cite as "open question N".

## 1. Goal

Give Raccoon linear types and the generic resource-protocol primitives of
`resource_core.md`: a linear `Supply`, `new`, `step` and `observe` over
first-class protocol instances. Holding tokens of an instance then yields
ordinary propositions about the reachable states of its protocol. A Lean model
of the language (§5) is to show it conservative over Lean: a proof obtained
with tokens could have been obtained without them.

## 2. Design

**Linear types.** A universe `Univ(k, u)` has a kind `k`, and `Sort(u)` and
`Lin(u)` name its constant kinds, `copy` and `lin`; universes are not
cumulative, so a type is used at exactly its universe. A type is linear when
its kind is not provably `copy`; types, proofs and function values never are.
Linear and kind-polymorphic families are ordinary nominal families whose
fields may be linear, unrestricted or proofs, and the kernel's `List` is one
([KINDS.md](../proposals/KINDS.md)). A ledger requires each tracked local to be used at
most once on every path, and never runs for unrestricted binders. Types and
proofs are read extents (S1): they may read linear values, consuming nothing,
provided each call in them takes separate linear inputs that were live
together (§3.9). No global is linear (S2), and axioms that mention linear
types are linted (S3).

**Protocols.** Beneath every prelude, the kernel declares the protocol
mathematics (`List.Perm`, `Protocol.Proto`, `Protocol.Reach`,
`Protocol.Valid`) as ordinary checked inductives, and the instance and token
types: the opaque `Supply`, `Inst` and `Tok`, and the linear families `Toks`
(packets), `Observed` and `Fresh`. The kernel owns them because the
primitives' types name them and a `--prelude` replaces the prelude. `Tok` and
`Supply` are opaque because an inductive without constructors has an empty
match, which would prove anything. Theorems recurse on `Reach` and `Valid`
directly, decreasing a proof compared by structural key rather than by
conversion, which proof irrelevance would make accept any proof.

**Primitives.** `new`, `step` and `observe` are natives with the
reductions R1–R3. Checking evaluates, and `Interpreter.run` returns the
checker's value of the program body, so the primitives compute in the one
evaluator and a program's result is computed through them. Tokens carry no
data; canonical packets are built from ghosts, which no source term names and
quotation refuses. `observe` reflects one fact, jointness: a packet observed
together is part of a reachable configuration. Use is affine (§3.8), so a
program drops a supply or a token it no longer needs.

## 3. Decisions

### 3.1 Families and primitives take a `Proto`

Every protocol family, opaque type and primitive takes a protocol `P: Proto`
and an initial inventory: `Inst(P, init)`, `Tok(P, init, s, a)`,
`Toks(P, init, s)` indexed by `C`, `Observed(P, init, s, C)`, `Fresh(P, init)`,
`Reach(P, init, C)`, `Valid(P, init, C)`, `new(P, init, sup)`, and so on. A
concrete protocol is `Proto.mk(Atom, Step)`.

The first design took the atom type and the step relation as two parameters,
for three reasons, each since removed:

- a field type that projects a parameter, such as `List(P.Atom)`, contains a
  stuck computation, and strict positivity rejected any one in a field type;
  the declaration-time rule (KERNEL_FOLLOWUPS 2.2) accepts one that does not
  mention the family;
- without structure eta, a family taking a `Proto` would tell a variable `P`
  apart from `Proto.mk(P.Atom, P.Step)`; with eta (2.1) they convert;
- the size rule charged a `Proto` argument its whole `Sort(1)`, which would
  have put `Toks` in `Lin(1)`; see §3.2.

The library's bundled wrappers, such as `Protocol.Proto.Reach(P, init, C)`,
became the kernel names (2.3).

### 3.2 The families are in `Lin(0)`

`Toks`, `Observed` and `Fresh` are in `Lin(Level.zero)`, with `Tok` and
`Supply`. Linear families obey the
[family argument size check](../kernel.md#family-argument-size), which charges
a record with structure eta by its fields: a `Proto` holds a `Type` and a
relation into `Prop`, which cost level 0, so a `Proto` costs 0 and every field
fits `Lin(0)`. A `Lin(0)` family can then hold a packet with its identity, and
a function type over the packets of a given protocol stays in `Type`. The
refinement is sound by the formalization's elementwise rank lemma: every
`Proto` value lies in the level-0 labels (`raccoon-formalization/DESIGN.md`
§10). A record holding a large field, such as a `Type -> Type`, still costs
its level, and so does a family with more than one constructor.

### 3.3 The entry is a `Supply -> R` body, and checking never allocates

A program has at most one body, in its entry module, checked once. A body of
type `(sup: Protocol.Supply) -> R` is an entry: it checks as any body does,
and `Interpreter.run` then applies its value to the root supply `supply#(0)`.
A global function of that type named as the body is an entry too, so no
separate entry declaration is needed. `R` must be unrestricted
(`LinearGlobal`), since nothing consumes a program's result.

Applying the checked value keeps checking free of allocation. The root supply
exists only once `run` applies the checked entry, and only R1 makes another,
so during checking every supply is a variable or stuck and R1 never fires.
Every identity is then a field variable of a `Fresh.mk` match or a stuck term
over its supply, which conversion relates only by congruence. An entry whose
result depends on its initial packet is stuck while it checks and computed by
`run`. Only the entry module has a body, no global is linear, and protocol
programs run with `--no-user-axioms`, so a run has exactly one root supply.

### 3.4 R1 and R2 reduce on known lists

R1 fires on a canonical supply and a known `init`, and R2 on a known output
list `B`: `nil`, or a chain of conses ending in `nil`, whatever its elements.
Otherwise the application is stuck on the supply's and the list's blockers and
resumes when one is solved, as a stuck `List.append` does. R3 always fires.

A canonical packet has one cons per atom, so it is a constructor value exactly
when its list's shape is known. A stuck ghost `canon` for an unknown tail
would be a new value form; staying stuck reuses the resumption natives already
have. Known lists also keep reduction consistent with refinement: R2 fires
during checking, and a match on a constructor value checks only that
constructor's branch, so a packet must not exclude a branch that its index
keeps. A known `B` already excludes every branch its canonical packet
excludes. The cost is that a theorem applied to a concrete run evaluates the
run while it checks (KERNEL_FOLLOWUPS 4).

### 3.5 `Inst` is opaque

`Inst(P, init)` is an opaque symbol in `Type`. It converts with
another only when their arguments convert, and unification derives neither
injectivity nor apartness from it: `Inst(P, x) = Inst(P, y)` refines neither
`x` nor `y`. So tokens of distinct identities have distinct
types. Identities are otherwise ordinary data: stored in lists and
unrestricted families, returned, and packaged with a packet of their own.

Plain data would be sound too, since soundness rests on tokens, not on
unforgeable identities. An axiom or an absurd branch can produce an identity
that `new` never returned, but its tokens come only from steps without inputs,
so its packets are reachable from `[]`, and framing gives their validity.
Opacity commits the kernel to less: no program builds, inspects or compares an
identity beyond conversion, which identifies no more identity types than the
model's names do, and the representation of names stays free to change, as
supply splitting would change it (open question 6).

### 3.6 Axioms and builtins

Protocol theorems are trustworthy only without user axioms: an axiom can prove
`False`, and in an inconsistent context a token can be built by eliminating
`False` into a `Lin` motive. Protocol soundness therefore rests on
`--no-user-axioms`, under which a theorem depends on the kernel and the
prelude alone; the prelude's axioms are the trusted bootstrap. By default any
module may still declare axioms, which the CLI reports, so existing programs
are unaffected. `main-new`'s policy, axioms only in a trusted prelude, would
give every program the guarantee at the price of rejecting existing ones.

S3 is a lint, not part of the guarantee. It checks the bootstrap obligation
that no prelude axiom yields or consumes tokens or supplies, by rejecting an
axiom whose evaluated type mentions a linear type anywhere. It cannot be
complete: a stuck computed type, a type variable instantiated at a minting
type, and the fields of a family named without linear arguments hide a linear
type from any check of the axiom's own type.

A builtin body, `:= builtin`, is unchecked like an axiom, so builtins are
accepted only in kernel and prelude sources. A program cannot introduce an
unchecked native outside the axiom policy, and `--no-user-axioms` covers
everything a program can assume.

### 3.7 No exit accounting

There is no scoped session and no accounting of what remains at exit.
Allocation is a first-order `new` on a linear supply, and instances are
first-class: identities leave any scope. Completeness facts, that nothing of
some kind is still pending, come from protocol state through jointness: an
authority atom that counts what is outstanding, or a held packet whose
coverage excludes the rest. Such a fact holds whenever its tokens are held
together, not only at an exit.

Exit accounting gives completeness for free, but only at exit, only for
second-class instances, and only with no dropping and totality. An exact
ledger also says what remains, not what happened, so "every issued copy was
written" needs a history invariant either way. The GPU port (§4) validates the
choice: both of its completeness facts follow from protocol state, at the
price of pair invariants and their frame lemmas.

### 3.8 Use is affine

A tracked local is used at most once on every path, and may be dropped
anywhere; a second use is `LinearReused`. Soundness needs only
no-duplication: forgetting tokens preserves the model's invariant
(`Inv.forget`), and a dropped token only enlarges the remainder in `Valid`.
So `discard` is gone, an entry need not use its last supply, a selector of a
linear record drops the other fields, and a protocol needs no rules without
outputs for programs to finish.

The first design used each tracked local exactly once, with `LinearUnused`
for a drop, so that the checker forced cleanup and a scoped exactness
primitive, certifying that a packet is an instance's whole ledger, stayed
possible; under affine use a dropped token still belongs to the ledger, and
no packet can be certified whole. It cost a `discard` primitive, rules
without outputs, and special cases for `_` fields and for paths an empty
match ends, and bought nothing soundness needs. Scoped exactness is no longer
planned ([KINDS.md](../proposals/KINDS.md) §6). A lint for dropped linear
values is deferred (KERNEL_FOLLOWUPS 3.7).

### 3.9 Types and proofs read linear values

A type or proof is a read extent: it may mention live linear locals, compute
over them, observe packets, and run closed resource computations, such as an
observation of `Toks.nil`, and it consumes nothing. Its reads do not count
toward the enclosing ledger. Two rules hold at every call inside it, an
application or a constructor application: its linear inputs have pairwise
disjoint provenance, the parts of tracked locals they are built from
(`LinearReusedInType`), and those locals were live together at one point on
the path (`LinearNotJointlyLive`). So `Eq(Nat, count(xs), count(xs))` and a
proof that returns what `observe(t)` gives are types and proofs, while
`observe(join(t, t))` and a packet combined with its successor are refused.
Codomains may read linear binders, and a proposition may have linear domains
(F2, F3). A read extent hands no linear value to a term (R8), since its value
is a type or a proof.

**Provenance is by region.** A provenance is a set of regions: a root, a
tracked binder with no defining value (a parameter, or a Π or constructor
binder), with a path of field indices into it. Regions overlap when one path
is a prefix of the other. Three choices close the ways a value could be
renamed out of its source:
- **Lets alias** their value's provenance and are never roots. As fresh roots,
  `let a := t; let b := t` made `join(a, b)` look separate, which an
  adversarial review turned into an axiom-free `False` from one token.
- **Fields are paths.** A match field `i` of a scrutinee that is exactly one
  region is that region extended by `i`, so sibling fields are separate and
  the same field taken by two matches overlaps. A field of any other
  scrutinee, such as a constructor application, gets the scrutinee's whole
  provenance: extending each of its regions would let a field that *is* one
  input pass as a part of it.
- **A match is no call.** In the model a match inside a read only inspects its
  scrutinee, so it adds no check; testing a scrutinee against its fields would
  also refuse `match xs with | cons h t => t`.

Joint liveness is decided on roots: each root records the roots consumed on
the path before it was bound, and a value built from roots since is
recomputed from that point.

**Kept conservative**, each for a significant simplification
(`docs/kernel.md` S1 lists them): a binder inside a data computation nested
in a read is used at most once; a match's result unions all its branches; a
call's result and a field of a non-exact scrutinee get whole provenances, so
two halves of one call result cannot be combined inside one read; and
quotation still refuses linear values, so an inferred motive that would need
one is `MissingReturningClause`.

The reason is the model's (`raccoon-formalization/DESIGN.md` §6). A read
extent formed where linear locals are live is a hypothetical run from the
current ledger. It needs only the joint admissibility of each run's inputs,
which follows from the live context because the frame absorbs the rest, and
which is a proposition, so it persists after the locals are consumed.
Observation is not what fails; duplication is: `count(join(xs, xs))` needs the
footprint of `xs` twice, which a protocol that excludes duplication never
reaches. Separation is decided at each call from the callee's type, never its
body, as Rust refuses `f(&mut x, &mut x)`: a function with two linear
parameters may join and observe them. Banning reads would reject sound
programs without simplifying the checker, and the language rejects a sound
program only when that significantly simplifies the implementation or
improves performance.

### 3.10 No linear captures

A lambda references no linear local bound outside it, in its body or its
type, read or not (F5), so every function value is unrestricted and a
function type carries no closure flag: F1 classifies it by levels alone. A
copyable closure holding a token would duplicate it, and a read inside it
would run when the function is applied, where nothing ties the captured
local's liveness to the arguments'. A callback that should own tokens takes
them as arguments. Closures that own their captures are open question 11.

## 4. The library and the GPU validation

`lib/Protocol`, loaded with `--root lib`, is untrusted library code over the
kernel declarations ([The protocol library](../kernel.md#the-protocol-library)).
`Laws` has `Derives`, `Reach.iff_derives`, `Reach.frame` and the `Valid` laws
over a `Proto`, as the kernel families take one; `Morphism` has
`transport`, `pullback` and `comp`; `Packets` has `append`, `split`,
`exchange`, `swap`, a framed `step` and the token-first `inspect`; `Exclusive`
and `Shares` are building blocks; `Lists` and `Logic` hold supporting
lemmas, beyond the prelude's membership, permutation, `flatMap` and order
laws. Packets travel in the kernel's kind-polymorphic `List` and the
prelude's `Prod`, with `Fact` for a proof beside them, and `Eq.subst` moves a
packet along an equation of its index.

The design was validated by porting the cooperative GPU fragment of
`gpu-schema-compiler` onto the library, in
`lemur-raccoon/experiments/protocols-clean` (see its README). The protocol is
in `resource_core.md` §6's authority style, without receipts. Both
completeness facts follow from protocol state: from counts (`GpuCompleteness`:
with the issuer and the engine held after `wait_write(0)`, every issued copy
has been written and no copy or write of the block is pending) and from
coverage (`GpuDrain`, through a footprint morphism into `Exclusive`). The
proofs build `Reach` derivations and take jointness as a `Valid` hypothesis,
the type `observe` returns; the fragment does not hold tokens yet. Its
verifier checks the library and the GPU modules under `--no-user-axioms`, with
no axioms or builtins in either, and requires every negative and friction
control to fail. The port also showed that
`resource_core.md` §6's invariant I is false as written, and that V, K and D
are consumed by no proof.

## 5. The formalization

**Its role.** The formalization follows the language, never the other way
round. Where the kernel admits something the model cannot yet interpret, that
is a gap for the model to close; the kernel changes only for an actual
unsoundness, not to make the model easier.

**What is mechanized.** `raccoon-formalization` is a Lean mixed embedding: the
unrestricted world is Lean, linear terms are a deep embedding with exact
contexts, and a ghost-ledger interpretation of well-typed terms makes that
calculus conservative over Lean. It models the supply and `new`, first-class
identities, jointness, the equations of R1–R3 (and of `discard`, since
removed), linear families with recursion
over linear values, and copyable functions; its `Protocol.lean` and
`Morphism.lean` hold the library's laws. Three kernel rules are gaps in it:
nested, non-uniform and under-binder recursion in linear families (L9), large
indices (L2), and function types over `Lin(v)` in `Sort(v)` (F1). Conversion
is not mechanized: the soundness of the Nat normal forms, and of the expansion
behind the prelude's `Nat.expand_eq`, is owed by the design's conversion
catalogue ([Nat normal forms](../nat-normal-forms.md#trust-and-the-formalization)).

**The design.** `raccoon-formalization/DESIGN.md`, under review and not yet
implemented, replaces the deep embedding with a semantic model over an
abstract base theory, of which Lean is one instance. A type is a carrier in
the base, its erasure, with an ownership predicate relating carrier values to
ghost-ledger footprints in `Prop`. A program is a carrier function with a
proof that it simulates a ledger transformation under every frame; function
carriers take an admissibility proof, which absurd branches, transports and
facts eliminated into data need. Linear families are indexed containers,
W-types of shapes with index guards in `Prop`, which covers the three gaps.
Each kernel conversion rule becomes an equality in the base, and R1–R3 hold
by `rfl` for every input, which validates the kernel's reductions on open
terms. Adequacy of an entry run from the root supply gives
conservativity as the case with no tokens. Phase 1 (one lemma per kernel rule,
and adequacy) and Phase 2 (generic families, nominal labels) are planned;
Phase 3, soundness of every well-typed term of a syntax, is deferred while the
language moves.

**Risks** (DESIGN.md §11): generic ownership for nested and indexed W-types,
which needs every admitted family to be container-generated; cumulativity
coherence, since Lean's lifts commute with type formers only up to
isomorphism, which the kernel's removal of cumulativity retires; the size of the conversion catalogue, chiefly soundness of the
`Nat` normalizer; recursion forms, since `lexicographic` and `measure`
recursion do not compute by `rfl` and the kernel's semantic termination check
might accept a call that does not decrease on the W encoding; the plumbing of
guards and relativization; nominal labels, which track the size rule closely;
universe-polymorphic protocols (open question 12); and final ledgers no longer
computed by `rfl`.

**Separation follows the model.** S1 (§3.9) is the relaxation that DESIGN.md
§6 validates, its R1–R5: reads and observations of live linear locals in types
and proofs, codomains over linear binders, propositions over linear domains,
and closed resource computations. It refuses what the model cannot interpret:
a read that duplicates a local (R6) or combines a consumed local with its
successor (R7). Phase 1 of the model must therefore interpret read extents as
hypothetical runs, not only a strictly separated fragment.

## 6. Open questions

Resolved items keep their numbers. Where
[KERNEL_FOLLOWUPS](../proposals/KERNEL_FOLLOWUPS.md) tracks an item, its
section is named.

1. (resolved: the entry is a program body of type `Supply -> R`, and a global
   function of that type named as the body serves as a named entry; §3.3.)
2. (resolved: a proposition may have linear domains, and its applications
   read their linear arguments (F2, §3.9).)
3. (resolved: a lambda with a linear parameter may appear in a type or proof,
   and F5 still forbids it to capture a linear local, read or not (§3.10);
   lambdas in types at all are tracked in KERNEL_FOLLOWUPS 2.8.)
4. (resolved: R1 and R2 fire on known lists, `nil` or a cons chain ending in
   `nil`, and are otherwise stuck and resumed; §3.4.)
5. (resolved: `Inst` is opaque, with no injectivity or apartness, so tokens of
   distinct identities have distinct types; §3.5.)
6. **Supply splitting**, so that independent code can allocate without
   threading one supply: `split : Supply -> Prod(Supply, Supply)`, drawing
   names from disjoint parts of the name space, such as paths in a binary
   tree. Tracked in KERNEL_FOLLOWUPS 3.3.
7. (resolved: use is affine, so scoped exactness, a primitive certifying that
   a packet is an instance's whole ledger, is no longer planned; §3.8.)
8. (resolved: a proof-variable scrutinee is always linked to its constructor,
   in every branch whose refinement succeeds; see
   [Recursion on proofs](../kernel.md#recursion-on-proofs).)
9. (resolved: user axioms are reported and rejected by `--no-user-axioms`, and
   builtins are accepted only in kernel and prelude sources; §3.6.)
10. (resolved: kinds, [KINDS.md](../proposals/KINDS.md). A universe is
    `Univ(k, u)`, the kernel's `List` and the prelude's containers are
    kind-polymorphic, and `LList` and `Tensor` are gone; KERNEL_FOLLOWUPS 3.1.)
11. **Linear closures**: a capture flag on Π, or a second function type, for
    closures that own the tokens they capture (§3.9). Tracked in
    KERNEL_FOLLOWUPS 3.2.
12. **Universe-polymorphic protocols.** With `Atom : Type`, `Proto` is in
    `Sort(1)` and the families are in `Lin(0)`. `Atom : Sort($u)` would admit
    large atoms and put the families in `Lin(u)`, and the model's ledger would
    range over protocols at every level (DESIGN.md §7). Tracked in
    KERNEL_FOLLOWUPS 3.4.
13. (resolved: protocol equality is conversion of the atom type and step
    relation, so separately declared but equal protocols give distinct token
    types (N2), while `P` and `Proto.mk(P.Atom, P.Step)` give the same ones.)
14. (resolved: the kernel accepts any step relation, which is sound; only
    generated matching, part of elaboration, would need an inductive.)
15. (resolved: `Lin`, `List.Perm` and the `Protocol` kernel declarations
    cannot be redeclared (`AlreadyDefined`), while the library may add members
    to the `Protocol` namespace.)
16. (resolved: the unification linking a variable scrutinee to its constructor
    also refines the variables of the scrutinee's type, so at a variable index
    `decreases structural(v)` sees the fields as smaller, and packet functions
    such as `Toks.append` recurse on the packet; KERNEL_FOLLOWUPS 2.4.)
17. (resolved: universes are not cumulative, so `A := Nat` is refused where
    `A : Lin(0)`, and `Eq.refl(A)` at a linear `A` has its declared type;
    KERNEL_FOLLOWUPS 1.2.)
18. (resolved: a stuck computation is positive when it does not mention the
    family, by main-new's declaration-time rule; KERNEL_FOLLOWUPS 2.2.)
19. (resolved: `Tensor` is gone, and `Prod`, with two kind and two level
    captures, refines its fields at copyable, mixed and linear instances;
    KERNEL_FOLLOWUPS 1.1.)

## 7. Out of scope

- Elaboration: `schema` syntax producing the atom and step inductives and the
  `Proto`; named rules as sugar for `step`; implicit supply threading;
  generated joint matching over `Reach`; threading of authority atoms and of
  knowledge atoms; `terminal` drop rules.
- Token-threading clients, starting with the GPU fragment.
- Emission protocols and refinement, giving theorems about generated code. The
  primitives compute, so a builder returns what it built, and no separate run
  mode is needed.
- Per-declaration axiom reports, which need each global to record the axioms
  its residual reaches.
- Porting the `main-new` GPU library.
- Borrowing, binder multiplicities, sealing, host reflection, per-schema
  primitives, quotients, partial functions and abort, and concurrency.
