# Machine source interface

Status: **language-design proposal**, 2026-10-02. The examples below are proposed syntax, not accepted Raccoon.
The [checked experiment](README.md) supplies ordinary-core representations for the main rules. There is no new
parser, elaborator or machine judgement in this change.

## The proposed language commitment

Give libraries a way to declare indexed protocols and give clients a way to compose commands with contracts.
Initially elaborate these declarations to ordinary inductives, predicates and proof terms. Keep eager construction
of a retained command tree. Runtime branches and loops are nodes in that tree; the generator builds their bodies
once, and their proofs quantify over runtime states and inputs.

There are three different objects:

- A resource reference names an allocation and belongs to its lexical lifetime.
- Live authority permits an operation in the current state. Linear authority cannot be copied.
- A command description contains syntax and a proof of what executing that syntax would do. It can be copied;
  each execution must still obtain authority satisfying its input contract.

The third object is what the generic machine encoding implements. The allocator also uses a linear cursor.
A general execution interface connecting command descriptions to live resource authority remains to be designed.
Thus a transition proof is not itself a new way to mint or redeem a resource token.

## A library declares the protocol

The following declaration sketches a buffer with a generation and a set of active readers:

```text
machine Buffer(id, width) {
  state Empty(g: Nat)
  state Writing(g: Nat)
  state Published(g: Nat, readers: Set(ReaderId))

  transition store(value): Empty(g) -> Writing(g)
  transition publish: Writing(g) -> Published(g, {})
  transition open(reader): Published(g, rs) -> Published(g, rs + reader)
  transition read(reader) requires reader in rs:
      Published(g, rs) -> Published(g, rs)
  transition close(reader) requires reader in rs:
      Published(g, rs) -> Published(g, rs - reader)
  transition recycle: Published(g, {}) -> Empty(g + 1)
}
```

Here `publish` and `recycle` include their synchronization obligations. The generation identifies which
publication a reader may use. A pure equality of storage addresses cannot justify reading a later publication
with an earlier loan. The checked model specializes the reader set to two Boolean permissions, and includes
payload and stored value in the state. Arbitrary reader sets are a proposed extension.

A declaration should produce a transition proposition with one introduction per permitted edge, a semantic
interpreter, primitive contracts, and named elimination theorems. For example:

```text
Step(before, op, after) : Prop
Entered(Published(g, rs), edge) : Prop

originPublished:
  Step(s, op, Published(g, rs)) ->
  StoreWasPublished(s, op, g, rs) or ReaderSetChanged(s, op, g, rs)

recycleRequiresNoReaders:
  Step(s, recycle, Empty(g + 1)) -> s = Published(g, {})
```

Backlinks describe an edge, or a checked history reaching a state from an authorized initial state. They should
not be timeless claims extracted from a state tag alone. A caller can construct the pure data `Published(g, rs)`;
that does not establish that a physical buffer has reached it.

The declaration's author supplies the meaning of operations and the proofs of primitive contracts. Deriving
the useful eliminators from the transition inductive should be automated. Hardware primitives additionally
need a contract connecting emitted operations to the target semantics; declaring a machine cannot supply that
contract by itself.

## Clients write indexed commands

```text
def consume(buffer: Ref(id), reader: Loan(id, g, r))
    : Command touches {id} [Published(g, rs) -> Published(g, rs)] {
  let value = buffer.read(reader)
  accumulate(value)
}

def cycle(buffer: Ref(id))
    : forall g, Command touches {id} [Empty(g) -> Empty(g + 1)] {
  buffer.store(iteration + 1)
  buffer.publish()
  buffer.reads(g) { r0, r1 =>
    consume(buffer, r0)
    consume(buffer, r1)
  }
  buffer.recycle()
}
```

Elaboration threads the intermediate predicates, establishes guards, retains syntax, and composes checked
primitive theorems. Expert code can instead provide a command tree with explicit meaning and contract proofs.
The public certification route must verify the same obligations as the convenient combinators.

The `reads` callback receives fresh lexical authority. Its complete description can leave the callback only
after the enclosing operation records opening and closing the loan. A closure retaining the loan remains
scoped. Pure syntax and proofs may leave through explicit readouts without bringing live authority along.

Machine states express runtime validity; scopes express which values and closures may be captured or retained
during eager generation. Keep both until a proposed replacement can prove these capture restrictions, including
indirect captures through closures. A state named `Open` does not provide that proof.

## Allocation supplies identity

```text
kernel {
  let a = allocate Buffer(width = 64)
  let b = allocate Buffer(width = 64)
  have a.id != b.id
  ...
}
```

Each allocation introduces a fresh lexical identity as well as a storage identifier. Shape is not identity.
The checked allocator consumes a linear cursor and issues a reference with a fresh scope; a theorem establishes
that successive storage identifiers differ for every cursor index. It is a generation-time allocator. It does
not allocate CUDA memory dynamically or prove reuse of freed storage safe.

References can support views, but a future view design must expose shared ownership and overlap explicitly.
Giving every view a fresh name would incorrectly justify disjointness for overlapping storage.

## Loops state their proof obligation

```text
for i in runtime(0 .. K)
    invariant Empty(g0 + i) {
  cycle(buffer)
}
// result: Empty(g0 + K)
```

The body has one retained AST and a theorem for every generation. The generic induction uses that theorem
at each runtime iteration. No representative generation determines the generated code. A branch must establish
the common result contract in both arms; a branch that leaves a different generation needs an existential or
otherwise explicit result predicate.

`Progress.Advances` and `Progress.repeat` check this rule today. The earlier fixed-invariant rule remains the
special case for predicates that do not track changing generations. Automatic invariant discovery is optional;
the source language should accept a written invariant and expose the exact unsolved obligation.

## Abstract workers carry contracts

```text
worker:
  forall allocation id,
  Ref(allocation, id, 64) ->
  (forall g, Command touches {id} [Empty(g) -> Empty(g + 1)])
```

A kernel can call an unknown worker and prove progress from this interface. Its proof cannot assume a particular
read count or implementation. A footprint/frame theorem says updating `id` leaves any disjoint peer unchanged.
The worker's returned tree can be lowered later without inspecting its body during the kernel's safety proof.

The checked `CustomWorker` demonstrates an implementation with an extra read. The client and generic machine
rules do not change. In a larger language, a worker with several resources would declare a footprint and its
state interpretation explicitly. Dynamic and overlapping footprints remain a separate design problem.

## What replaces existing features

| Existing mechanism | Proposed role |
|---|---|
| Sealing | Restricts issuance of references and live authority, and controls convenient source introductions; explicit proof certification can admit additional descriptions |
| Scopes | Enforce allocation/loan identity and closure capture restrictions during eager generation |
| Linearity | Controls live authority and allocator cursor advancement; command proofs and syntax remain unrestricted |
| Typestate indices | Describe runtime protocol states through a common contract interface |
| `Fixed` in current GPU loops | Reassess for each migrated combinator once its body is retained once and certified universally; this experiment does not remove it from current APIs |
| Implicit readout | Continue using existing inference; improved annotation and proof elaboration can hide boilerplate |
| Full typing reflection | Still useful for a theorem about arbitrary existing clients and effects outside the command interface; unnecessary for the checked command fragment |
| Quoting | Optional elaboration convenience; this encoding stores syntax directly and requires no evaluation or implicit redesign |

The immediate implementation target is library declarations plus elaboration into this representation.
A native machine judgement would become justified if it removes a demonstrated expressiveness limitation,
substantially reduces certificates, or provides a simpler trustworthy check than the ordinary core. The experiments
have not yet demonstrated such a need.

## Connecting the existing GPU library

The first migration boundary can be a checked program artifact. Build through the existing Core API, expose its
read-only kernel syntax, and prove it equals the lowering of a certified command. Rendering continues to require
the existing structural well-formedness proof.

This arrangement breaks the proof dependency into an acyclic sequence: machine definitions and contracts,
source commands, lowering certificates, then program inspection and rendering. It develops the AST-checking
and certified-program options in `REGISTERS.md` §9. It does not solve mutual minting between two sealed modules;
that sharing pattern needs its own solution if the API still requires it.

The checked pilot follows this arrangement for a synchronous buffer cycle. To establish the wider library
claim, operation contracts must connect the modeled machine to GPU execution, and library combinators must
cover every accepted client effect. AST equality alone does not establish either premise.

The next discriminating protocol is asynchronous or cross-CTA completion: independent roles open and finish
loans, and recycling needs all relevant completions. Require both a checked safe implementation and a checked
counterexample when one role's completion is omitted. That test will exercise the ownership and concurrency
requirements the current sequential pilot leaves open.
