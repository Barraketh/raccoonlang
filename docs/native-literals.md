# K3: Native Literals — Packed Values (`VPacked`)

Status: **Nat implemented; source-layout String implemented; Lean 4.30 String adapter pending**
(2026-07-20). The bundled source Prelude activates its seven available operations; the full
fifteen-op and old `String.mk (List Char)` path is exercised through the kernel-owned synthetic
bootstrap. Production activation from translated `Init` now requires the 4.30
`String.ofByteArray`/`String.ofList` adapter described in §7. Companion to
`mathlib-export-port.md` (workstream K3) and
`kernel-theory.md` (every judgment below must trace to a ledger entry; the §6 checklist walk is
in §8 of this document). Records the 2026-07-14 base design and the 2026-07-17 full-K3 decisions.
Implementation record: `plans/k3-implementation.md` (code-level decisions, historical first-slice
notes, completed continuation, and remaining T1 integration tests).

## 1. Problem and scope

A ground `Nat` in constructor form is a `succ`-spine proportional to its *magnitude*: the literal
`1000000` is a million-deep `VApp` chain, and literal arithmetic through structural unfolding is
exponentially slower than its notation. Without K3, literal-arithmetic proofs are not slow but
infeasible (plan §4.K3). Deliverables:

1. A packed value form for ground `Nat` (payload: arbitrary-precision integer).
2. Constructor↔literal transparency: match/`Nat.rec` on a packed value fires; `succ`/`zero` of
   packed values fold back to packed form.
3. Fifteen kernel-accelerated ops as builtin defeq steps: the fourteen binary operations in
   Lean's pinned kernel table plus `Nat.blt`, a deliberate Raccoon extension justified against
   its checked structural definition.
4. `StrLit`, unfolding to the selected bootstrap's validated String representation on demand; no
   accelerated string ops. The existing CharList implementation covers the source/synthetic
   layout, not Lean 4.30's translated `Init` layout.

**Scope decision (2026-07-14).** The machinery is shaped generically — a `VPacked` value form
plus a *codec* describing one type's packed representation — but the codec set is **closed and
kernel-curated**: `NatCodec` and the validated-layout-owned `CharListCodec` used by `StrLit`.
Explicitly out of scope:

- **No container codecs** (List-as-array, Vec-as-array+Nat). The wins concentrate in accelerated
  *ops*, not representation: an array-backed list without accelerated ops gains only locality,
  while kernel reduction's access pattern (peel one constructor, prepend one element) is O(n) per
  step on flat arrays. Chunked representations fix that but lose canonicity (§3.L5), which is the
  load-bearing soundness property. Compact storage for ground constructor data is also an
  *alternative* to hash-consing — deferred until the P1 caching strategy is decided.
- **No user-extensible codecs.** Each codec is trusted code inside defeq; an open set converts
  the kernel into a plugin host inside the TCB (Coq's retroknowledge precedent: built general,
  walked back to a fixed primitive set).
- **No alternate declarations under native Nat names.** `Nat`, its constructors, and the
  accelerated `Nat.*` definitions are reserved to kernel-owned bootstrap installers: the bundled
  default Prelude and T1's explicit pinned translated-`Init` mode. Ordinary imports,
  Prelude-less programs, and custom Preludes remain free to define the same datatype under another
  canonical name (for example `Peano`), but cannot acquire a reserved native identity.
- Nat is the principled special case: the unique type whose representation changes complexity
  class (unary→binary). String is its cousin (avoids materializing `List Char`). Everything else
  is constant-factor and belongs to a future compiler, not to defeq.

## 2. Design: the `VPacked` value form

```
VPacked(codec: PackedCodec, payload: PackedPayload, tpe: Value)
```

A `VPacked` is a **ground, closed data value**: the payload is one member of a sealed host-value
sum (`NatPayload(BigInt)` or `CharListPayload(Vector[Int])`) containing no `Value`s, no vars, no
proofs. Each `Int` in a CharList payload is a Unicode scalar value; construction rejects surrogate
code points and values above `0x10ffff`. `synDeps = tpe.synDeps`; it is never a
`Blocker`; its constructor requires `!isPropositionType(tpe)` (mirroring `VProof`'s require, from
the opposite side). Factories additionally require the represented type to have empty syntactic
dependencies, so every permitted packed value and its type are closed.

The sealed sum is preferred to Scala path-dependent payload types: it keeps exhaustive matches
compiler-checked and makes codec/payload mismatch impossible through private codec factories. The
payloads and `VPacked` itself expose no public raw constructor or `copy`; the only kernel-package
factories are `VPacked.nat`, `VPacked.charList`, `VPacked.charListTail`, and `VPacked.retype`.
`charList` validates the complete scalar vector once. `charListTail`, usable only by the codec's
one-layer decoder, takes a suffix of that already-validated persistent vector without rescanning;
successively peeling a length-*n* literal is therefore O(*n*) validation/peeling work rather than
O(*n*²). `retype` accepts only a type definitionally equal to the prior type and, for CharList,
definitionally equal to the descriptor's `listCharTpe`; it then returns the original packed value
without replacing the authenticated type. This preserves the actual `tpe.key` across ascription,
materialization, and quote/evaluate round trips even when defEq type representatives have different
keys.

Payload acceptance, semantic equality, and `ValueKey` mixing are codec-defined. CharList equality
and keys cover the remaining scalar sequence, so a tail of one literal compares identically to the
same suffix introduced as a separate literal; they never depend on `Vector` node identity.

The design is *representation, not conversion rules* — the dual of K4. StructEta keeps
eta-eligible structure-like values constructor-headed from creation; `VPacked` keeps codec-type values
packed from creation and derives constructor form **on demand, one layer at a time**
(`decodeHead`). Both make their equations hold by making the other representation (bare structs /
ground spines) unrepresentable rather than converted.

A codec provides:

| Member | Signature (informal) | Role |
|---|---|---|
| payload variant | sealed host payload | `NatPayload(BigInt)` or `CharListPayload(Vector[Int])` |
| constructor names | canonical name strings | where a peel needs a real head, it borrows the concrete side's (§6); match dispatch needs only names |
| payload acceptance | `PackedPayload → Boolean` | private factories reject codec/payload mismatches exhaustively |
| `decodeHead` | `PackedPayload → (ctor name, Vector[Value])` | expose one constructor layer; total on the codec's payload variant |
| optional `fold` | `(ConstructorHead, Vector[Value]) → Option[PackedPayload]` | canonical codecs may pack constructor forms; decode-only codecs advertise no fold |
| payload equality/key | codec-specific | semantic payload equality and deterministic mixing into `ValueKey` |
| `canonical` | `Boolean` | §3.L5: whether *every* ground value of the type is packed |
| `less` | `(PackedPayload, PackedPayload) → Boolean` | strict order realized by constructor-field steps (§3.L6) |
| clash realization | `Boolean` claim | §3.L9: whether unequal payloads are *refutably* distinct — gates payload apartness |
| ops | reserved-name accelerated operations (§5) | Nat only |

## 3. Codec laws

Every codec must satisfy these; each is load-bearing for a specific judgment in §6.

- **L1 (eligibility).** The type is a Type-valued inductive, all of whose constructors carry
  derivable no-confusion (`noConfusion = true`), and which is *not* eta-eligible.
  Type-valued + no-confusion is a precondition of the apartness shortcut (with L9, §6
  unification); non-eta-eligibility keeps `VPacked` off StructEta's expansion seams — packed values and
  canonical-at-birth structure expansion never compete for the same value (the "no mixed rule"
  invariant, kernel-theory §2).
- **L2 (groundness).** Payloads contain no `Value`s. Packed values therefore cannot capture vars,
  hide proofs, occur in positivity checks, or block; every invariant about proof flow and
  evidence (kernel-theory §5–6) is vacuously preserved *inside* the payload.
- **L3 (injectivity).** Payload equality ⇔ definitional equality of decodings. The ⇒ direction is
  what `ValueKey` trust rests on (key equality ⇒ defEq). The ⇐ direction gives only definitional
  inequality — which is **not** propositional apartness (kernel-theory §1 ordering; funext will
  equate definitionally-distinct functions). Apartness needs L9.
- **L4 (decode correctness and optional fold round trip).** `decodeHead` is total on the codec's
  payload variant and exposes exactly one constructor layer of the represented ground value.
  When a codec advertises folding, `fold(decodeHead(p)) = Some(p)` and, when
  `fold(c, args) = Some(p)`, `decodeHead(p) ≡ (c, args)` fieldwise. A decode-only codec has no
  fold obligation: its packed/constructor comparisons always use the mixed peel. Decoded fields
  are built **through the standard value seams** (`evalApply`/`evalRef`), never as raw `VApp`s —
  so proof-collapse and StructEta apply automatically (a decoded `Char`'s validity proof enters
  its exact type's canonical proof representation on its own). Nat is fold-capable and canonical;
  CharList is decode-only and non-canonical.
- **L5 (canonicity, per-codec).** *Canonical* means every ground value of the type is packed:
  all value-birth seams fold, so no ground constructor-headed value of the type exists. Canonical
  codecs get key-only defEq. Non-canonical codecs (CharList: structurally built ground char lists
  never pack) must set `needsStructuralDefEq = true` on their packed values and are compared by
  peeling (§6).
- **L6 (order realization).** `less(p, q)` holds exactly when `decode*(p)` is reachable from
  `decode*(q)` by ≥1 constructor-field steps, and `less` is well-founded. For Nat: `m < n`
  realizes exactly `n − m` `succ`-field steps. This makes the §6 termination rule an instance of
  the existing structural-decrease judgment, not a new order.
- **L7 (op correctness).** Each accelerated op in the closed table is a **sound bounded fast
  path**: ordinary dispatch mismatches may decline to the structural definition, but when an op
  fires it must terminate and produce exactly the structural definition's result on the decoded
  arguments. `pow` admits exponents through `2²⁴`, matching Lean's kernel reduction bound, and
  raises `NativeOperationLimitExceeded` above it. It must not decline an oversized closed `pow`:
  Raccoon's evaluator is eager, so doing so would immediately enter an impractically large unary
  structural recursion. `shiftLeft` uses the same `2²⁴` bound on a nonzero operand's shift
  count and raises the same error above it; `0.shiftLeft(n)` returns zero for every Nat `n` without
  allocation. `shiftRight` is unbounded: when the count is at least the operand's bit length it
  returns zero without converting the count to a host `Int`. These are explicit evaluator resource
  policies, not new equations. Ops are
  **derived rules**: on admitted inputs they decide equations the structural
  rules already decide (in astronomically more steps), so they add no equations and are
  decidability-benign. Each op gets a ledger row and a certification test (§10). For ops whose
  structural definitions are WF-recursive and K2-sealed (`Nat.div`-class), the justification
  target is the primitive equation lemma (`fix_eq` instances), and the native op is the *only*
  definitional computation path — parity with post-4.9 Lean.
- **L8 (closure, reserved identity, and layered validation).** The codec set is sealed in kernel
  code, with **no registration step and no kernel mutable state**. The canonical names that give
  native rules meaning are reserved: `Nat`, `Nat.zero`, `Nat.succ`, and every definition name in
  the accelerated-op table. Only a kernel-owned trusted bootstrap installer may declare them: the
  bundled default Prelude, the kernel-owned synthetic full-K3 test bootstrap, and T1's explicit
  pinned translated-`Init` mode once the importer consumes the already-defined authority.
  Ordinary program/import declarations, `Prelude.none`, the minimal test Prelude, and
  path/source-provided custom preludes fail with `ReservedKernelName`. Consequently, after a
  trusted bootstrap publishes its immutable environment, a `ValueId.Const("Nat.add")` is
  provenance enough: no later or ordinary declaration can attach that id to another body. This is
  Lean's trust model—the kernel and its `Init` definitions are one coordinated trusted
  bootstrap—not a claim that typechecking proves the arithmetic body extensionally correct.
  Validation is layered where each layer carries exactly the obligation it can discharge:
  (a) the deep family shape check — family Type-valued and `familyArity = 0`, constructor list
  exactly the codec's, zero nullary with type the family, succ unary with field *and* result the
  family, all heads no-confusion — runs once for each trusted bootstrap environment and fails
  loudly (`NatLiteralUnavailable`). Literal checking thereafter performs only a reserved-family
  lookup; absence still raises `NatLiteralUnavailable`.
  (b) fold seams **self-validate structurally** (exact stored arity, no-confusion,
  already-packed fields, non-propositional type), protecting the value invariant even during
  bootstrap construction and against malformed trusted values.
  (c) one immutable `NativeNatOpSpec` table owns each exact name, host implementation, typed
  Nat-result or Bool-result row, Lean-vs-Raccoon origin, and required bootstrap profiles; dispatch,
  reservation, type validation, extension labeling, and missing-operation checks derive from it.
  The private typed row subtype derives the read-only `returnsBool` classification that T1 uses for
  manifest entries. Ordinary checking first produces an immutable candidate environment; before
  that candidate is committed to the trusted bootstrap fold, the loader requires an applicable
  transparent `VLam` with `ValueId.Const(name)` and the exact expected type, including two explicit
  operand binders. This `VLam` check reflects the current interception seam and is not a body
  recognizer. A closed bootstrap profile selects the bundled source Prelude's seven definitions or
  all fifteen for T1 and the synthetic full-K3 fixture. The profile is checked only for bootstrap
  completeness and is never retained as runtime authority. Agreement between checked bodies and
  the host arithmetic table is trusted outright, as it is in Lean; no structural body recognizer,
  semantic capability, declaration fingerprint, or runtime enablement state is an admission
  requirement.
  (d) the transparency, differential, equation, and performance pins are desynchronization alarms.
  A bootstrap edit that changes Nat's shape fails validation; an edit that changes an operation's
  meaning is a TCB change that the engineering pins are expected to expose.
  Reservation is deliberately simpler than attaching codec/native-op state to `ConstructorHead`
  or maintaining a trusted mutable registry.

  In the implementation, `Prelude.Config` carries a single sealed `BootstrapAuthority`.
  `Interpreter.trustedBootstrap` derives a package-private context containing the native permit
  and optional completeness profile, so callers cannot independently combine those values. Its
  `add` and `finish` operations serve both the whole-program source loader and T1's streaming
  import path. The native authority constructors are kernel-owned; ordinary configurations use
  `Unprivileged`.
- **L9 (clash realization).** A codec may claim *payload refutability*: unequal payloads decode
  (by iterated `decodeHead`) to forms that differ at a **constructor clash between
  derivable-no-confusion heads** at finite depth. Only codecs claiming L9 participate in payload
  apartness (§6) — L3 alone gives definitional inequality, which the planned axiom ledger does
  not let stand in for propositional apartness (funext equates definitionally-distinct
  function-valued content; kernel-theory §4). First-order decodings (no function-typed fields
  reachable) are the easy sufficient condition. Nat claims it: unary numerals `m ≠ n` clash at
  depth `min(m, n)` with a `zero`/`succ` mismatch.

## 4. The Nat codec

Payload `BigInt ≥ 0`, `canonical = true`, `less` = numeric `<`, claims L9 (first-order
decodings; clash at depth `min(m, n)`).

- `decodeHead(0) = (Nat.zero, [])`; `decodeHead(n) = (Nat.succ, [VPacked(n−1)])`.
- `fold(Nat.zero, []) = Some(0)`; `fold(Nat.succ, [VPacked(n)]) = Some(n+1)`; `fold(Nat.succ,
  [neutral]) = None` — `succ` of a neutral stays an ordinary `VCtor` spine over a neutral base,
  exactly as today. Folding also declines on propositional result types (a Prop-declared
  lookalike must collapse, never pack) and on heads without no-confusion.
- **Why name-keying is sound without registration:** L8 reserves the family, constructor, and
  accelerated-op names to trusted bootstrap installers, so ordinary checked source and later
  imports cannot give those names different declarations or bodies. The fold's local guards
  remain load-bearing during bootstrap construction: a nullary zero round-trips to the same head,
  while a succ fold requires an already-packed, well-typed field. The selected bootstrap has
  already passed the full family check before any checked program can construct a literal.
- **Fold seams** (canonicity is an invariant, not a birth-only courtesy):
  - `Interpreter.evalRef` — nullary constructor references (`Nat.zero` folds here).
  - `Interpreter.evalApply`, `ConstructorHead` branch — constructor applications.
  - `ValueOps.materialize` — store-solution substitution rebuilds `VApp`s and can turn
    `succ ?x` with `?x := VPacked(4)` into a ground constructor form; the rebuild re-folds.
  - MatchChecker's reachable-constructor probe — its nullary `Nat.zero` candidate is ground and
    folds; `Nat.succ` of a fresh field remains structural.
  - All other `VCtor` factories produce non-ground fresh-var forms or struct expansions (disjoint
    by L1) and need no fold.
- **Literal syntax.** `CoreAst.Term.NatLit(value: BigInt)` and the matching `ElabAst` node;
  TypeChecker assigns the Prelude's `Nat`; evaluation produces `VPacked` directly. The export
  reader (T1) maps Lean `NatLit` nodes one-to-one. A surface numeral token is added so tests can
  be written in-language; it is sugar for the same node.
- `Int`, `Fin`, `UInt32`, … need nothing: they arrive from the export as ordinary inductives
  whose fields are Nat literals.

## 5. Accelerated ops (Nat only)

One immutable table maps each reserved canonical definition name to either a typed Nat-result row
or a typed Bool-result row containing its native implementation. Interception point:
`Interpreter.evalApply`, before `runLam`, keyed on
`ValueId.Const(name)` — L8's declaration reservation makes the name an authenticated identity
without per-lambda provenance state. The trusted loader additionally requires the published value
to be a transparent, applicable `VLam`, because that is the value form the current interception
seam receives; an opaque/symbolic declaration is rejected as an unavailable native operation. This
covers both `LamBody.Core` definitions and the raw-recursive native wrappers `TerminationChecker`
builds (skipping the runtime decrease check is sound exactly because no recursive call is made).
The op fires only when **all** arguments are packed; otherwise the structural body runs as today
(and on a neutral scrutinee sticks as usual). By L7 the bypass is observationally invisible.

| Op | Structural definition | Convention to pin |
|---|---|---|
| `add`, `sub`, `mul`, `beq`, `ble` | in Prelude today (structural recursion) | `sub` truncates at zero |
| `pow` | structural; added with K3 | `pow(a, 0) = 1`; exponent limit `2²⁴` |
| `blt` | structural; added with K3 | Raccoon extension to Lean's native table |
| `div`, `mod`, `gcd` | native rows implemented; checked WF-recursive definitions arrive through T1 and are K2-sealed | `a / 0 = 0`, `a % 0 = a`, `gcd(0, b) = b` |
| `land`, `lor`, `xor` | native rows implemented; checked binary-decomposition definitions arrive through T1 | non-negative bitwise operations |
| `shiftLeft`, `shiftRight` | native rows implemented; checked binary-decomposition definitions arrive through T1 | left limit above; arbitrarily large right shift returns zero |

`pred`/`isZero` are not ops: match on a packed value already computes them in O(1) via
`decodeHead`. `beq`/`ble`/`blt` return `Bool` constructor values resolved from the trusted
lambda's closed global environment and checked against the instantiated codomain. The final op
set is a decision for M0's "literal ops used" stat; the table makes extension a ledger decision,
not an architecture change (plan §8 gate 4). Adding an op also reserves its canonical name.
The selected bootstrap validates two explicit `Nat` binders and exact checked result types
`Nat → Nat → Nat` for the twelve Nat-result entries and `Nat → Nat → Bool` for `beq`, `ble`,
and `blt`. Validation runs after ordinary checking and before the candidate environment is
committed to the bootstrap fold. A second finalization check applies the table's closed bootstrap profile:
the source Prelude's seven rows or all fifteen for pinned translated `Init`. The table itself still
contains and reserves all fifteen in either environment; absence of the eight T1-gated definitions
does not make the source Prelude fail.

Two parity notes. (1) Ground reduction is confluent to the numeral, so acceleration is
independent of the structural definition's recursion pattern (Raccoon's `add` recurses
tail-style, Lean's rewraps `succ` — same normal form on ground args). (2) Defeq parity on *open*
args (`n + 1 ≡ succ n` and friends) is a property of the structural definitions and belongs to
T1's prelude-alignment work, not to K3.

Trust stance: per plan §8 gate 4, ops are trusted outright and recorded in the ledger (§9),
following Lean's kernel model. Lean hard-codes fourteen binary `Nat.*` constant identities and
assumes its bootstrapped `Init` definitions agree with the native equations. Raccoon uses the same
trust mechanism for those identities and for one deliberate extension, `Nat.blt`, in the bundled
Prelude and T1's explicit pinned translated-`Init` bootstrap mode. The imported definitions are
still ordinarily typechecked, but K3 neither recognizes their bodies nor issues a per-operation
semantic capability. The certification harness (§10) is the engineering backstop—differential/
equation tests, not admission checks or proofs.

Pinned Lean precedent: at `d024af099ca4bf2c86f649261ebf59565dc8c622`,
[`type_checker.cpp`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/type_checker.cpp#L619-L635)
dispatches the fourteen binary operations on fixed constant identities before ordinary definition
unfolding; it does not inspect or fingerprint their declaration bodies. Lean's private,
append-only kernel environment and preinstalled `Init` keep later user declarations from replacing
those names. T1's distinct trusted-bootstrap entry point plus the shared reserved-name registry
reproduce that boundary; merely presenting an export with the same names or version header does
not. `Nat.blt` is not in that Lean table and must remain labeled as the separately ledgered
Raccoon extension.

## 6. Kernel integration

- **Evaluation.** `evalMatch` gains a `VPacked` scrutinee case: `decodeHead`, then the existing
  branch dispatch by constructor name (this *is* "match on a literal fires"; T2-synthesized
  `Nat.rec` goes through the same path). Stuck/blocked handling untouched — packed values are
  never stuck.
- **defEq** (`ValueEquivalence.defEqStructural`), two arms:
  - `(VPacked, VPacked)` same codec → payload equality. Complete among packed values by L3.
  - `(VPacked, VCtor)` / symmetric → `decodeHead` one layer and recurse. Reachable only for
    non-canonical codecs (canonical types have no ground `VCtor`s) and for `VCtor`s over
    neutrals, where it correctly reduces to comparing a packed field against a neutral (false
    now, as today).
  - `needsStructuralDefEq(VPacked) = !codec.canonical` — packed Nats resolve entirely through
    the key fast path; packed char-lists always take the structural path against constructor
    forms.
- **Keys** (`ValueKey`). `Tag.Packed` is mixed with a stable codec id and the payload's canonical
  content, then always with the packed value's actual `p.tpe.key` (as for constructor-headed
  `VApp`s). CharList additionally mixes its descriptor's `listCharTpe.key` before the scalar count
  and unsigned 32-bit scalars; its factory fixes the actual type to that represented type and
  identity-preserving retyping never changes it. Key equality ⇒ defEq holds by L3⇒; distinct codec
  kinds mix distinct ids.
  No `AstNodeId`s, host strings, collection identities, layout object identities, or cached JVM
  hashes participate.
- **Unification** (`tryUnify`), mirroring defEq:
  - Peel arm: `(VPacked, VCtor)` decodes one layer and continues under the same `Ctx` — the
    decoded frame is a constructor frame, invertible as usual. This is required, not optional:
    MatchChecker refinement must solve `succ ?x ≡ 5` as `?x := 4` (literal indices — `Fin 5`,
    `Vec A 3` — are everywhere in the export). Links so produced record forced solutions of
    constructor equations; the store still never invents values.
  - Apartness: same codec **claiming L9**, with explicitly unequal payloads → `apart = true`.
    Equal payloads that reach unification because their annotated types did not compare equal
    continue with the ordinary type equation, never apart. Justification: L9
    guarantees the decodings differ at a constructor clash between no-confusion heads at finite
    depth — the shortcut is the transitive closure of derivable no-confusion steps, nothing more
    (kernel-theory §5 apartness row). It is gated on the L9 claim, never on canonicity or L3
    alone: definitional inequality is not propositional apartness under the planned axioms
    (funext), and enabling it for a codec failing L1/L9 is the `Quot.mk`-trap shape
    (kernel-theory §6). Same-codec packed pairs *without* L9 report stuck — conservative;
    peeling both sides would decide some of them, recorded as a gap (§11).
  - Everything else (packed vs neutral, packed vs blocked) is stuck, never apart — unchanged.
- **Termination** (`TerminationChecker.isStrictSubterm`): new case — candidate `VPacked(c, p)` is
  a strict subterm of root `VPacked(c, q)` iff `c.less(p, q)`, compared on payloads directly —
  never by decode-recursion (peeling a 10⁹ literal is a hang). Justified by L6 as a run of the
  existing constructor-field descent. Scope note: the decrease check runs only while the
  *declaring* body is checked (`rawRecursiveSelf` is the bound self during checking; at runtime
  `runLam` binds the finished lambda and recursion is unchecked), so this rule is check-time
  completeness for metrics that meet packed values, not a runtime-performance need. Mixed roots
  (`VCtor(succ, [VPacked n])` mid-decode) work through the existing field descent + defEq.
  Non-canonical-codec mixed forms are a completeness gap (§11).
- **Quoting** (`ValueQuote`): a Nat `VPacked` quotes to `NatLit`; a CharList `VPacked` quotes to
  `Proj("String", 0, StrLit(payload))`. The canonical outer `String.mk` form quotes directly to
  `StrLit`. None expands to a constructor spine (a 10⁶ literal must not quote to a 10⁶-deep term).
  Round trip: quote → eval → same semantic payload, type, and key.
- **Proof collapse:** no interaction by construction — `VPacked` requires a non-propositional
  type (L1/L2), `canonicalizeProof` passes it through, decoded proof fields canonicalize at their own
  seams (L4). Positivity: payloads contain no values (L2), so `mayOccurIn` is untouched.
- **Implicit projection** (`telescope/Projection.project`): the `CtorField` step reads stored
  fields of constructor values; against a packed value it reads the decoded field instead, so
  implicits forced through literal-valued indices (`f {n} (v: Vec(A, succ(n)))` applied at
  `Vec(A, 5)`) still reconstruct. `compile` needs nothing — its patterns are matched over fresh
  vars, and `succ`-of-var never folds.
- **MatchChecker** (static side): the ground-scrutinee arm — a constructor-headed scrutinee
  admits exactly its own constructor's case — gets a packed mirror via `decodeHead`. Everything
  else reasons over types and fresh constructor copies, with literal indices handled by the
  unification arms above.
- **PrettyPrinter:** Nat payloads print as numerals; the exact validated `String.mk` over a packed
  field prints as a quoted string; a standalone packed `List Char` prints as
  `proj[String,0]("...")`, matching its residual type rather than pretending the list is itself a
  String. These are diagnostics only.

## 7. String literals (source layout implemented; Lean 4.30 adapter pending)

The implementation below is the existing Raccoon source/synthetic layout. It cannot be activated
for the pinned 4.30 export: that producer defines `String` with constructor
`String.ofByteArray (toByteArray : ByteArray) (isValidUTF8 : ...)`, and defines
`String.ofList : List Char → String` by UTF-8 encoding into that constructor. The kernel expands a
String literal to `String.ofList` applied to the familiar `List.cons (Char.ofNat ...)` spine. A
production adapter must therefore validate the ByteArray representation and proof field, preserve
the observable `String.ofList` reduction, and select an appropriate packed payload. Treating the
4.30 block as `[String.mk]` is a typed compatibility failure, not a fallback.

Implemented and exercised against a kernel-owned synthetic bootstrap containing validated
`Char`/`String` declarations. The bundled source Prelude intentionally has no String layout;
production translated-`Init` activation is part of T1. Factoring chosen for K4-compatibility:
`String` (a one-field struct) is eta-eligible, and a whole-string packed form would be a second
representation competing with StructEta's canonical constructor form — exactly the mixed-rule
situation K4 forbids. So the packed value lives **at the field**:

- A trusted bootstrap constructs a private immutable `ValidatedStringLayout` only after an exact
  structural check. `Char`, `List Char`, and `String` are non-propositional Type-valued inductive
  instances. `String` has family arity zero, constructor list exactly `[String.mk]`, and installed
  projection metadata with `etaEligible = true` and exactly field zero. The exact no-confusion
  `String.mk` has no erased family arguments, one stored field whose instantiated type is
  definitionally equal to `List Char`, and result definitionally equal to `String`.
- For the same resolved `List Char` instance, the constructor list is exactly
  `[List.nil, List.cons]`. Instantiating each head's erased family binders with that instance's
  family arguments consumes exactly those family arguments. The exact no-confusion `List.nil` has
  no stored fields and result `List Char`; the exact no-confusion `List.cons` has stored fields
  `(Char, List Char)` and result `List Char`, all modulo definitional equality. The two-constructor
  instance is not eta-eligible.
- `Char.ofNat` has exactly checked callable type `Nat → Char`, using the already-validated Nat
  representation. Every retained type, constructor head, and callable value has empty syntactic
  dependencies and no private-stage local reference. A failed condition raises
  `StringLiteralUnavailable` and produces no partial layout. This is a representation-shape
  capability, not a semantic native-operation capability; only the bundled Prelude installer or
  T1's caller-authorized pinned translated-`Init` installer can issue it.
- As in Lean's own hardcoded String-literal expansion, the exact bootstrap `Char.ofNat` identity is
  trusted to map each valid scalar to the intended `Char` and to be injective on valid scalars.
  Its declaration and type are checked, but K3 does not recognize or fingerprint its body. This
  agreement is part of the bootstrap TCB: it is what justifies semantic CharList payload equality
  (L3). Unicode round-trip and unequal-scalar tests are desynchronization alarms, not admission
  proofs. An ordinary same-named declaration cannot issue a layout or acquire literal semantics.
- The layout owns a private `CharListCodec` instance and the closed checked values needed to apply
  `Char.ofNat`. This is necessary because `decodeHead` is used by defeq, unification, and
  termination paths that do not carry an `Env`. Holding closed bootstrap values in the immutable
  codec descriptor does not weaken L2: the **payload** still contains no `Value`s, and the
  descriptor's closure is checked before publication. Constructor dispatch remains name-based;
  the codec does not manufacture unchecked `ConstructorHead` objects.
- The issued layout is stored in an immutable `NativeLiteralState` field of `Env`. Environment
  extension and closure preserve it automatically; the trusted bootstrap installs it atomically
  after validation, and rollback cannot leak it. `StrLit` checking/evaluation reads this field;
  an already-created packed CharList carries its private codec descriptor and therefore needs no
  environment to peel. There is no process-global registry or mutable codec state.
- T1's export IR uses `StrVal(scalars: Vector[Int])`, and the three `StrLit` AST nodes carry the
  same scalar representation; none uses a host `String` as its semantic payload. T1 and
  double-quoted surface syntax decode text without Unicode normalization into that vector, which
  `VPacked.charList` validates once. Invalid UTF-8, unpaired
  UTF-16 surrogates from a host JSON/parser library or `\uXXXX` escape, and non-scalar code points
  are rejected before a literal node is built; a valid surrogate escape pair becomes one
  supplementary scalar. This matches Lean's UTF-8-to-code-point expansion while making host
  representation details unobservable.
- Surface parsing, scalar validation, and diagnostic rendering share `UnicodeScalarString`:
  `LanguageParser` converts its committed decode failures to parser diagnostics, while
  `PrettyPrinter` uses its deterministic scalar escaping. The semantic payload remains the scalar
  vector, never the rendered host `String`.
- `StrLit s` evaluates through the validated layout to
  `VCtor(String.mk, [VPacked.charList(layout.charListCodec, s)])` — the `String` layer stays
  constructor-headed (K4 canonical), while the char *list* is packed at the descriptor's validated
  `List Char` type.
- `decodeHead([]) = List.nil Char`; `decodeHead(c +: rest) =
  List.cons(evalApply(Char.ofNat, VPacked.nat(c, Nat)), VPacked.charListTail(current))`.
  `Char.ofNat(c)` is formed by ordinary `evalApply` to the layout's checked closed value with a
  packed Nat argument, so structure eta and proof collapse run through their existing seams. The
  tail factory reuses the validated suffix without another scalar scan. The codec is
  `canonical = false`, `refutesUnequalPayloads = false`, and decode-only: structurally built ground
  char lists never pack, and mixed defeq/unify comparisons peel the packed side. Its strict-subterm
  relation is proper scalar-sequence suffix. There is no CharList constructor fold and no
  accelerated string operation.
- `SurfaceAst.Term.StrLit`, `CoreAst.Term.StrLit`, and `ElabAst.Term.StrLit` carry the validated
  scalar sequence. Quotation of
  the exact validated `String.mk` head with exactly one field packed by that layout's CharList
  codec emits `StrLit` directly; every other constructor uses ordinary constructor quotation.
  Quotation of a standalone packed `List Char`—for example after projecting the String
  field—emits the checked residual
  `Proj("String", 0, StrLit(s))`; it must not mis-type the field as a String literal or expand an
  O(n) constructor spine. Re-evaluation of that projection recovers the same packed field and key.
  Pretty-printing escapes the scalar sequence deterministically and never uses host-string
  normalization: `\"`, `\\`, `\b`, `\f`, `\n`, `\r`, and `\t` use their standard
  JSON-style escapes; other C0 controls use four-hex-digit `\uXXXX`; all other Unicode
  scalars are emitted literally.

Pinned Lean precedent: at the selected commit,
[`inductive.cpp`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/inductive.cpp#L1200-L1212)
UTF-8-decodes a String literal and expands it to `String.ofList` over `List.cons` applications whose
heads are `Char.ofNat` code points, ending in `List.nil Char`. The source/synthetic implementation
preserves only the list-spine portion of that behavior; the outer 4.30 representation remains the
T1.5/K3 compatibility task above.

## 8. Interaction checklist walk (kernel-theory §6)

- **× proof irrelevance:** packed values are never proofs (constructor require); payloads hold no
  proofs (L2); decoded proof fields collapse through the standard seams (L4).
- **× quotients / canonicity-of-closed-values:** nothing new assumes closed values are
  constructor-headed — packed values are ground by construction; axiom-stuck closed Nats remain
  neutrals, remain stuck. Quotient types fail L1 and can never carry a codec.
- **× non-forced unification:** peel links are consequences under constructor frames; payload
  apartness is gated on L1+L9 (derivable no-confusion, clash realization) — the same
  discipline that keeps `Quot.mk` out of apartness.
- **× impredicativity / large elimination:** untouched; packed types are Type-valued (L1).
- **× planned axioms (§4):** propext/funext/choice speak about Prop, functions, and large
  parameters; payload apartness is ground-data constructor disjointness, which every ledger row
  preserves ("genuine constructor disjointness still prunes").
- **× cumulativity:** none involved.
- **× identity keys:** new key surface is payload-derived and deterministic (no node ids); key
  equality ⇒ defEq is L3⇒; residual risk unchanged (128-bit collision).
- **× native-op identity:** accelerated names are reserved to kernel-owned trusted bootstrap
  installers (L8), so name-keyed interception cannot attach a trusted equation to a user-defined
  body or ordinary imported declaration. Custom and prelude-less environments simply have no
  native Nat declarations. T1's pinned translated-`Init` path is deliberately part of the TCB,
  matching Lean's own bootstrap assumption.
- **× termination order:** the packed rule is the existing tree order via L6; payload order
  well-founded; no laziness, no self-capture (L2).
- **× structure eta:** codec types are never eta-eligible (L1); `StrLit` packs at the field
  precisely so expansion and packing never share a value space.

## 9. Landed ledger entries

- kernel-theory §2 includes a defeq component bullet: packed representation (canonical-at-birth for
  Nat), payload equality, the peel rule, and the key trust extension.
- kernel-theory §5 includes two rows: **payload apartness** (consumer: match pruning; justification
  L1+L9 as above) and **packed structural decrease** (consumer: termination guard;
  justification L6).
- The op table is documented as derived rules under the §4-adjacent trust note (plan §8 gate 4:
  trusted, ledgered) — one line per op, conventions included. The same ledger entry records the
  Lean-style bootstrap assumption and reserved-name isolation as the reason a table key can
  identify a trusted bootstrap definition rather than an arbitrary user body.
- The §4-adjacent String representation note records the structurally validated layout, the exact
  `Char.ofNat` scalar-mapping assumption, ordinary-import exclusion, and the projection quotation
  rule. CharList remains outside payload apartness because it does not claim L9.
- The landed K3 pins in §10 live in `NativeLiteralTests`; the translated-`Init` differential,
  manifest, and atomic-publication pins remain T1 acceptance work. Any future codec beyond
  CharList must re-walk §8 and add its own rows before landing.

## 10. Test plan

- **Certification harness** (`NativeLiteralTests`), tiered by what each tier can afford:
  (a) *structural differential* — the seven bundled operations against their structural
  definitions under an op-table
  kill-switch, on operand ranges sized to the structural path's cost (it is O(magnitude) and
  compounds: comparisons and `add`/`sub` afford dozens, `mul` single digits, `pow` operands ≤3),
  always including the boundary cases (0, 1, equal args, near-equal, `sub` underflow, and `pow`
  zero exponent); the eight T1-gated operations currently use equation examples and randomized
  host-oracle checks in the synthetic bootstrap, because their checked structural definitions are
  supplied only by translated `Init`;
  (b) *op-path randomized checks* — large random operands through the full
  parse→check→eval pipeline against host-`BigInt` oracle expectations; this guards wiring,
  conventions, and the pipeline, not the arithmetic itself (the op *is* host arithmetic);
  (c) *perf pins* as separate tests (§ below). For K2-sealed ops the structural oracle is
  replaced by the equation lemma applied at literal arguments.
- **Transparency pins:** match/`rec` on a literal fires (`pred(1000000) ≡ 999999`);
  `succ`-of-literal folds (`succ(41) ≡ 42` by key); quote round trip preserves payload and key;
  literal-index refinement (`succ ?x ≡ 5` solves `?x := 4`; matching on a `Fin 5`-typed value
  refines correctly).
- **Apartness pins:** `3 ≡ 4` apart; `0 ≡ succ x` apart; packed vs axiom-stuck neutral stuck,
  never apart.
- **Termination pins:** structural recursion driven by literal arguments passes the decrease
  check (`fib`, `ackermann` on small literals); the K1 synthesized-recursor shape works with a
  literal major.
- **Perf smoke** (extend `benchmarks/`): arithmetic on 2⁶⁴-magnitude literals completes
  instantly; the unary counterfactual is the point of the workstream.
- **Resource-limit pin:** `pow(1, 2²⁴)` is admitted, while `pow(1, 2²⁴ + 1)` raises
  `NativeOperationLimitExceeded` before either host allocation or structural fallback;
  `shiftLeft(1, 2²⁴)` is admitted, `shiftLeft(1, 2²⁴ + 1)` raises the same error,
  `shiftLeft(0, 2²⁴ + 1) = 0`, and `shiftRight(1, 2²⁴ + 1) = 0` without host-`Int` conversion.
- **String pins:** ASCII, BMP, and supplementary-plane literals quote/evaluate with identical
  scalar payloads and keys; `match` exposes `List.nil`/`List.cons` and a checked `Char.ofNat`
  result one layer at a time; projecting field zero and quote/re-evaluating uses the `Proj` residual
  rather than a constructor spine; a decoded tail and an independently introduced equal suffix
  have equal keys; distinct scalars remain distinct through `Char.ofNat`; malformed Unicode is
  rejected before `StrLit` construction; and a 20,000-scalar packed list peels without suffix
  rescans. Negative layout tests cover field type, arity, projection, no-confusion, closure,
  constructor membership, constructor results, and `Char.ofNat`'s result.
- **Consistency suite:** keep the existing proof-theoretic probes semantically unchanged. The
  probe-worthy payload-apartness surface is a law-violating codec, which L8's sealed set makes
  unconstructible (there is no public codec constructor).
- **Reservation/bootstrap pins:** defining `Nat`, its constructors, or an accelerated `Nat.*`
  name outside a kernel-owned trusted bootstrap raises `ReservedKernelName`; all fifteen operation
  names are tested directly. The bundled Prelude
  and the synthetic full-K3 bootstrap load through their distinct privileged paths. T1 must add
  the corresponding pinned translated-`Init` acceptance pin. A general export stream that merely
  claims the pinned version or uses the right names remains unprivileged. The same test shape applies to
  `ValidatedStringLayout`: a same-named ordinary `Char.ofNat` cannot issue it or enable `StrLit`.
  Native admission rejects implicit operands, wrong Nat- and Bool-result telescopes, an
  opaque/symbolic declaration, and a lambda without the exact reserved identity. The table's
  bundled profile selects its seven operations; the synthetic/T1 profiles select all fifteen and
  report the first missing row in stable table order. Direct context tests pin streamed
  declaration loading, final layout publication, and failed-finalization atomicity.

## 11. Residual gaps and non-goals

- **Mixed-form decrease on non-canonical codecs:** a recursion whose metric mixes packed and
  structurally built char lists may be rejected (conservative false in `isStrictSubterm`).
  Acceptable: kernel workloads do not recurse over string payloads; revisit only if T4's failure
  taxonomy says otherwise.
- **Same-codec packed pairs without L9 report stuck** in unification rather than peeling both
  sides to look for a clash — conservative, never apart. Revisit with the first non-L9 codec.
- **Translated-`Init` activation remains T1-owned.** K3 already defines the pinned bootstrap
  profile and authority, but only T1 can supply and atomically publish the checked production
  declarations, run the equation/differential alarms against those definitions, and emit the
  manifest entries.
- **No container codecs, no user codecs** (§1). Array-backed ground-data storage is revisited
  together with the P1 caching decision (hash-consing vs compact spines are alternatives).
- **No custom datatype under the reserved Nat identity.** Custom or prelude-less programs use a
  different canonical family name; supporting an alternate implementation with the native Nat
  names would require a provenance mechanism and is intentionally out of scope.
- **Open-arg unfolding parity** of Prelude definitions with Lean's (T1 concern, §5 note 2).
- **Op set growth** (`log2`, others): only via M0 stats + a new ledger row each.
- Negative literals, `Int`/`Float` primitives: not planned; the export encodes them over Nat.
