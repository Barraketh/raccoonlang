# Safety problems for the language

> **Historical problem statement.** This document predates removal of
> Raccoon's `Lifetime` and sort-scope feature. Its lifetime/scope examples and
> safety gaps are historical; they do not state current language behavior.
> See the [language reference](../language.md) and
> [kernel reference](../kernel.md). The pre-removal source is retained at
> revision `4af124c4`; view it with
> `git show 4af124c4:docs/proposals/SAFETY_PROBLEMS.md`.

Status: **problem statement** (2026-10-01). Three problems that the GPU library has run into, where a language feature
may be the right answer. Each needs design work. This document says what goes wrong today, what we would like to be
able to say or check, and what makes it hard. It proposes no solutions, though it notes approaches that are known not
to work.

Related problems that are written up elsewhere:
- Sharing a sealed capability between two trusted modules: `gpu/encoding/REGISTERS.md` §9.
- Checking generated code by running it: `gpu/EVALUATOR.md`.

Implementation direction for problem 1: [Reflected typing and library safety](REFLECTED_TYPING.md), a staged plan for
internal typing propositions, declaration reflection, and semantic library composition.
The [compositional machine experiment](https://github.com/Barraketh/lemur-raccoon/blob/main/experiments/compositional-machines/README.md) tests a narrower
alternative: explicit contracts and structured emission certificates in the existing core.
The [extensible follow-up](https://github.com/Barraketh/lemur-raccoon/blob/main/experiments/extensible-machines/README.md) tests fresh identity, indexed loop
progress and an actual Core AST connection; its [source interface](https://github.com/Barraketh/lemur-raccoon/blob/main/experiments/extensible-machines/SURFACE.md)
sets out the proposed language functionality and remaining proof obligations.
The [TinyGEMM comparison](https://github.com/Barraketh/lemur-raccoon/blob/main/experiments/machine-core/README.md) and
[A3b/pair client ports](https://github.com/Barraketh/lemur-raccoon/blob/main/experiments/machine-core/full/RESULTS.md) test an alternative interface and exact
Core lowering equivalence. They do not prove the library-wide safety claim.
The [kernel-independent proof experiment](https://github.com/Barraketh/lemur-raccoon/blob/main/experiments/library-correctness/README.md) checks universal
retirement/coverage and peer-frame theorems, compares the evidence needed by the three language routes, and
records the remaining obligations. It does not establish a complete replacement for Core.
Its [primitive copy-ring continuation](https://github.com/Barraketh/lemur-raccoon/blob/main/experiments/library-correctness/RING_DESIGN.md) now emits CUDA and
proves arbitrary-client primitive protocols, exact kernel assembly and phase parity for a single-stage slice.
The [friction log](https://github.com/Barraketh/lemur-raccoon/blob/main/experiments/library-correctness/RING_DESIGN_FRICTION.md) records actual proof costs and tooling issues.

## 0. Background for a new reader

**Raccoon** (`docs/language.md`, `docs/kernel.md`) is a dependently typed language with the following features.
- **Sorts.** A sort `Sort { level, kind, scope }` gives a type's universe level, its kind (`unr` or `lin`, where linear
  values are used exactly once) and its scope.
- **Scopes.** `scope l => e` opens a fresh lifetime `l`. A value that belongs to `l` cannot be held, made or used once
  `l` closes (`docs/implemented/SCOPE_CONTAINMENT.md`). A function belongs to every scope its code captures.
- **Sealed families.** A family declared `sealed` can be constructed and taken apart only in its own file. Other files
  get its values only from that file's functions.
- **Forced implicits.** An implicit argument must be recoverable from the types of later explicit arguments.
- **Local typing.** A type may be derived from a term, never from the expected type. Checking is synthesis plus
  equality, and conversion is unification. There is no readback ("quoting") of values into terms. Every definition is
  transparent: there is no `opaque`. A `let` binds transparently too: the bound name unfolds to its value.
- **Linear values stay out of types.** A type or a proof may not contain a value of linear type (`LinearInType`).
- **Propositions.** Proofs are irrelevant and canonical. Evidence arguments `[h: P]` are discharged by evaluation.

**The GPU library** (`gpu/encoding/Core.rac` and the documents beside it) is a Raccoon program that generates CUDA.
- **Staging.** A client's Raccoon code runs at generation time and emits code through a linear context `Ctx(l, g)`,
  where `g` is the group of threads running it. The printed CUDA is what runs on the GPU.
- **Tokens.** Authority over on-chip resources is a sealed linear token: a ring stage that may be filled, an
  accumulator that may be read, a warpgroup's registers, the right to store rows of the output. Each token stands for a
  piece of a resource (`gpu/SEPARATION_PILOT.md`). Each operation consumes some pieces and produces others.
- **Protocols.** Protocols between roles are typestate on tokens: a producer side and a consumer side, each moving
  through its states.
- **Facts about run-time data.** A fact about run-time data is a sealed value minted where the fact was checked. For
  example, `Claimed` is minted in the branch where an atomic claim succeeded (`gpu/encoding/P2.md`), and `Leader` in
  the branch where the CTA's rank is 0 (`gpu/encoding/TWO_CTA.md`).
- **The claim.** The library's claim (`gpu/OBLIGATIONS.md` §1) is that any program that type-checks against the
  library prints a kernel with no data race, collectives run by exactly the threads they require, asynchronous
  protocols used as specified, and so on. Liveness is explicitly not claimed.
- **What is trusted.** `Core.rac` is trusted: it mints every token, and its code is checked only by review. The
  argument that its types imply the claim is on paper, as the M-rules in `OBLIGATIONS.md` §5.

**The user's direction.**
- Find the cleanest safe encoding of the GPU algebra in Raccoon, which leans on linearity and scopes.
- Then establish what it takes to prove that encoding correct without changing it.
- Language changes are acceptable where they pay for themselves.

## 1. The library's meaning lives on paper

**The situation.** Client code is checked by Raccoon's type system. The library's safety then follows from three facts,
none of which Raccoon states:
- **What tokens mean.** Each sealed linear token stands for a piece of a resource: shared memory, tensor memory,
  registers, barrier phases, rows of the output (`gpu/SEPARATION_PILOT.md` §1–§5).
- **What operations do.** Each operation of `Core.rac` turns the pieces it consumes into the pieces it produces, and
  the code it emits respects that: it touches only what its pieces cover, and it waits where it must.
- **What the language guarantees.** A well-typed client uses each linear token exactly once, never after its scope
  closes. A callback that captures a linear value runs as often as the token's meaning requires.

The first two are prose in `OBLIGATIONS.md` (M1–M24) and `MODELS.md`. The third is a meta-theorem of the language
(`docs/kernel.md`), available to us as reasoning but not as a premise inside a Raccoon proof.

**What went wrong.** Each bug below broke a rule stated only in prose, in trusted code.
- **`onLeader`** (`OBLIGATIONS.md` M23). The combinator emits `if (rank == 0) { … }`, but its callback's type allowed
  it to capture linear values. A client could put the peer CTA's store wait inside it. The type checker saw the token
  used once; at run time the peer never waited.
- **A3b's register restore** (`gpu/encoding/NOTES.md`, "Hardware session"). A warpgroup restored its registers before
  another warpgroup's first increase had run. It deadlocked on hardware.
- **A3a's store rows.** The authority to store a tile's rows did not determine the rows the store computed. A
  warpgroup placed on other warps wrote another CTA's rows.
- **P2's append.** The core's column arithmetic wrote outside the claimed (page, head) region.

Hostile reviews and a hardware session found these. None was a gap in the client-facing types; each was a gap between
what a token means and what the trusted code does.

**What we would like to be able to say, inside Raccoon:**
1. **A token family's meaning:** the piece of a resource a token stands for, as a function of its indices.
2. **Each operation's contract:** its consumed pieces and produced pieces, and that its emitted code stays within them.
   This is in the style of a separation-logic triple, over a semantics of the generated code.
3. **Each combinator's obligation.** For example, a callback run under a run-time condition captures no linear value
   whose meaning needs all threads. This should be a statement whose proof fails for the `onLeader` that was written.
4. **The composition principle** as a premise: a well-typed client's tokens are used exactly once, within their
   scopes. From that and 1–3, the library's claim follows: the adequacy argument.

**What makes it hard:**
- **Linearity and scope are typing judgments, not propositions.** No proposition can say "this token is consumed
  exactly once".
- **Types and proofs may not contain linear values** (`LinearInType`). A statement about a particular token cannot
  mention the token. It can mention only its unrestricted indices.
- **Proofs are irrelevant and canonical.** Whatever form these statements take must not let a proof stand in for a
  resource.
- **The meaning connects generation time to run time.** Tokens exist while the generator runs, while their meaning is
  about what the emitted code does when it runs. That needs a semantics of the generated code:
  - `gpu/Spec.rac` today states only structural invariants;
  - `gpu/EVALUATOR.md` proposes an executable semantics;
  - `gpu/MODELS.md` describes the hardware's transition systems on paper.
- **The encoding should stay as it is.** The goal is to prove the library correct without reshaping it to suit a proof.

**Questions for the design:**
- How can a proposition speak about a linear token without containing it? Through its indices, a ghost description,
  or something else?
- Should the composition principle be an axiom of the trusted prelude, a reflected typing judgment, a modality, or
  something else?
- What is the smallest statement that would have refused the `onLeader` that was written? That is a useful first
  target.
- How much of the semantics of generated code has to live in Raccoon for statements 2 and 3 to be provable, rather
  than assumed?

## 2. Facts about one run-time value

**The situation.**
- **Values.** A run-time value in the library is a `Val(l, grain, type)`: an expression of the generated code, with
  the scope `l` it belongs to and whether it is the same in every thread (`grain`).
- **Facts.** Facts about run-time data are sealed values. `Claimed` means "this warp holds the claim on the page it
  read". `Leader` means "this CTA's rank is 0".
- **The gap.** A fact cannot say which value it is about. Every value bound in a scope has that scope's lifetime, so two
  different values have the same type.

**What went wrong:**
- **P2's append.** Lane 0 read the page table, claimed the page, and broadcast whether the claim held. The other 31
  lanes computed their rows from their own reads of the table. If another kernel changed the table between the reads, those lanes
  wrote a page nobody had claimed. The fix broadcasts lane 0's row. But nothing would refuse the old code: the
  recomputed page and the claimed page had the same type.
- **A3a's store rows.** The store computed its row from the warp number, a different formula from the one the
  authority token was about.

A cut-down example:

```raccoon
let (e, page) := gload(e, table, b, j)           // page : Val(l, Grain.thread, DType.u32)
withClaim(e, owners, page, fun (m: Lifetime)(e: Ctx(m, warp))(c: Claimed(m)) => {
  let (e, page2) := gload(e, table, b, j)        // page2 : the same type
  writeRow(e, c, page2, knew)                    // accepted, though the claim was about `page`
})
```

**What we would like.** A way to make names that are known to be globally unique, and to put them in types:
- `page : Val(p, …)` and `c : Claimed(m, p)` for a name `p`. A value with any other name is refused where the claim
  is used.
- Trusted operations that know two values are equal, such as a broadcast, may carry a fact from one name to another.
  Nothing else can.
- Functions must be able to return values with fresh names, as `gload` does above.
- This is meant as a feature of its own, not as part of scopes.

**What makes it hard:**
- **Equality.** Generating a fresh name is impure, and definitional equality assumes purity:
  - **Congruence.** Two occurrences of `fresh()` are the same term, so the checker would treat them as equal.
  - **Transparent `let`.** `let p := fresh()` and `let q := fresh()` both unfold to `fresh()`, so `p` and `q` are
    equal to the checker.
  - **β-reduction.** It duplicates arguments: `(fun x => (x, x))(fresh())` versus `(fresh(), fresh())`.
  - **Checking evaluates terms.** It does so under binders too, to compare them. If evaluating `fresh()` made a new
    name, comparisons would be nondeterministic and memoized results wrong.
  - **Conversion is unification.** It could solve a fresh name equal to something else.
- **Linear values stay out of types.** The only thing that differs at every call site today is the linear context
  `e`, and `LinearInType` keeps it out of types.
- **The known workaround does not scale.** `scope p => …` is generative, so a fresh lifetime per value can be had today
  by putting the rest of the code in a callback. A kernel binds hundreds of values, so that nesting is unusable.

**Requirements a design should meet:**
- Names from different generations are never definitionally equal.
- It is usable in straight-line code, with no callback per value.
- A function can return a value with a fresh name.
- It is sound with proof irrelevance, canonical proofs, normalization by evaluation, unification and forced implicits.
- The static guarantee does not depend on the names' run-time values, which could all be the same.

**Questions for the design:**
- **Distinctness in proofs.** May proofs use the distinctness of two names, say "different names, so the pieces they
  cover are disjoint"? Or do names only prevent confusion? The uses so far need only the latter. The former is a new
  logical principle.
- **Names and sealing.** How do names interact with sealing? Can a sealed family's constructor require a fresh name?
- **Names in implicits.** Can implicits be forced from a name in a type? How do names appear in error messages?

## 3. Progress: deadlocks

**The situation.**
- **What the types rule out.** Protocols are typestate on linear tokens. The types rule out a role touching a buffer
  out of turn, but not a set of roles waiting on each other in a cycle.
- **What the claim excludes.** `OBLIGATIONS.md` §1 excludes liveness, and M11 states "deadlock is not a race". So far
  that has been the accepted trade-off.
- **Why it matters anyway.** A deadlocked kernel hangs the GPU until it is killed. On rented hardware, a hang is found
  late and costs money.

**What went wrong.** Deadlocks found in the last day:
- **A3b's register restore.** It deadlocked on hardware and was found with `cuda-gdb`. A warpgroup that finished early
  increased its registers back to 128, taking registers another warpgroup's first increase still needed. The register
  file was exactly full, so that increase never completed.
- **Two register splits in a row**, found in review: one warpgroup's next split could take registers before the others
  had restored theirs.
- **A leader-only tile loop**, found in review. A value written only in the leader CTA steered a loop that ran in the
  leader only. The peer waited for stages that never came.
- **Roles that disagree on a trip count**, the standing case M11 describes. For example, a loader that loads one block
  more than the MMA consumes.

**What we would like.** That a kernel built by well-typed client code cannot deadlock, under a stated fairness
assumption about the hardware: every blocking operation eventually returns. A weaker version would also help: the
library's protocols are deadlock-free for every client that keeps the stated agreements (trip counts, one split at a
time).

**What makes it hard.** The blocking operations are of several kinds:
- **mbarrier waits on a phase:** completed by arrivals from other threads, transaction bytes from TMA, or commits from
  the tensor cores;
- **barriers that need every participant:** CTA barriers, named barriers and cluster barriers;
- **increases that draw on a shared pool:** `setmaxnreg` increases, and tensor-memory allocation, which for a CTA pair
  is collective across two CTAs;
- **completion waits for asynchronous work:** bulk store groups, tensor-memory loads.

Other difficulties:
- **Concurrent roles.** The roles run at once, in one CTA, across a pair of CTAs, and with asynchronous units. A
  deadlock is a cycle of waits across these. Linear typing is compositional, and a cycle is a global property.
- **Trip-count agreement.** Agreement between roles is a property of run-time values: every role computes the same
  number from the same inputs. It overlaps with problem 2: "the same count" is "the same value".
- **Shared pools.** Registers and tensor memory are acquired and released incrementally. Whether an increase can
  complete depends on the order of other warpgroups' changes.

Approaches the literature offers, none evaluated:
- multiparty session types: a global protocol projected onto roles;
- priority or level annotations on blocking operations, with typing that makes waits increase along every path
  (Kobayashi's deadlock-free π-calculus);
- encodings of either in the library, with indexed tokens and evidence, which might need nothing from the language.

**Questions for the design:**
- **The claim.** Should liveness become part of the library's claim, or stay outside it with deadlock-freedom checked
  some other way? The evaluator of `gpu/EVALUATOR.md` would search schedules for deadlocks dynamically.
- **The fairness model.** What fairness model of the hardware does a progress claim need? Warp scheduling, barrier and
  pool behaviour are only partly documented.
- **Trip counts.** Can trip-count agreement be typed? For example, every role's loop is driven by one shared, named
  count, as in problem 2.
- **Language or library.** Does the language need anything, or can the library encode progress with what it has?
