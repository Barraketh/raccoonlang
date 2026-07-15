# K3: Native Literals — Packed Values (`VPacked`)

Status: **Nat implemented** (2026-07-14); CharList/`StrLit` remains staged. Companion to
`mathlib-export-port.md` (workstream K3) and
`kernel-theory.md` (every judgment below must trace to a ledger entry; the §6 checklist walk is
in §8 of this document). Records the 2026-07-14 design discussion. Implementation handoff:
`plans/k3-implementation.md` (code-level plan — file-by-file changes, resolved decisions, test
plan).

## 1. Problem and scope

A ground `Nat` in constructor form is a `succ`-spine proportional to its *magnitude*: the literal
`1000000` is a million-deep `VApp` chain, and literal arithmetic through structural unfolding is
exponentially slower than its notation. Without K3, literal-arithmetic proofs are not slow but
infeasible (plan §4.K3). Deliverables:

1. A packed value form for ground `Nat` (payload: arbitrary-precision integer).
2. Constructor↔literal transparency: match/`Nat.rec` on a packed value fires; `succ`/`zero` of
   packed values fold back to packed form.
3. The ~15 kernel-accelerated ops as builtin defeq steps, justified against the structural
   Prelude definitions.
4. `StrLit`, unfolding to `List Char` constructor form on demand; no accelerated string ops.

**Scope decision (2026-07-14).** The machinery is shaped generically — a `VPacked` value form
plus a *codec* describing one type's packed representation — but the codec set is **closed and
kernel-curated**: `Nat` now, a char-list codec for `StrLit` when the Prelude grows `String`.
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
  accelerated `Nat.*` definitions are reserved to the bundled default Prelude. Prelude-less and
  custom-Prelude programs remain free to define the same datatype under another canonical name
  (for example `Peano`).
- Nat is the principled special case: the unique type whose representation changes complexity
  class (unary→binary). String is its cousin (avoids materializing `List Char`). Everything else
  is constant-factor and belongs to a future compiler, not to defeq.

## 2. Design: the `VPacked` value form

```
VPacked(codec: PackedCodec, payload: codec.P, tpe: Value)
```

A `VPacked` is a **ground, closed data value**: the payload is a host value (Scala `BigInt` /
`String`) containing no `Value`s, no vars, no proofs. `synDeps = tpe.synDeps`; it is never a
`Blocker`; its constructor requires `!isPropositionType(tpe)` (mirroring `VProof`'s require, from
the opposite side).

The design is *representation, not conversion rules* — the dual of K4. StructEta keeps
eta-eligible struct values constructor-headed from creation; `VPacked` keeps codec-type values
packed from creation and derives constructor form **on demand, one layer at a time**
(`decodeHead`). Both make their equations hold by making the other representation (bare structs /
ground spines) unrepresentable rather than converted.

A codec provides:

| Member | Signature (informal) | Role |
|---|---|---|
| `P` | host payload type | `BigInt` for Nat, `String` for CharList |
| constructor names | canonical name strings | codecs never hold `ConstructorHead` objects — where a peel needs a real head, it borrows the concrete side's (§6); match dispatch needs only names |
| `decodeHead` | `P → (ctor name, Vector[Value])` | expose one constructor layer; total |
| `fold` | `(ConstructorHead, Vector[Value]) → Option[P]` | pack a constructor-of-packed/ground-args form; `None` when args aren't packable |
| `canonical` | `Boolean` | §3.L5: whether *every* ground value of the type is packed |
| `less` | `(P, P) → Boolean` | strict order realized by constructor-field steps (§3.L6) |
| clash realization | `Boolean` claim | §3.L9: whether unequal payloads are *refutably* distinct — gates payload apartness |
| ops | reserved-name accelerated operations (§5) | Nat only |

## 3. Codec laws

Every codec must satisfy these; each is load-bearing for a specific judgment in §6.

- **L1 (eligibility).** The type is a Type-valued inductive, all of whose constructors carry
  derivable no-confusion (`noConfusion = true`), and which is *not* an eta-eligible struct.
  Type-valued + no-confusion is a precondition of the apartness shortcut (with L9, §6
  unification); non-struct keeps `VPacked` off StructEta's expansion seams — packed values and
  canonical-at-birth struct expansion never compete for the same value (the "no mixed rule"
  invariant, kernel-theory §2).
- **L2 (groundness).** Payloads contain no `Value`s. Packed values therefore cannot capture vars,
  hide proofs, occur in positivity checks, or block; every invariant about proof flow and
  evidence (kernel-theory §5–6) is vacuously preserved *inside* the payload.
- **L3 (injectivity).** Payload equality ⇔ definitional equality of decodings. The ⇒ direction is
  what `ValueKey` trust rests on (key equality ⇒ defEq). The ⇐ direction gives only definitional
  inequality — which is **not** propositional apartness (kernel-theory §1 ordering; funext will
  equate definitionally-distinct functions). Apartness needs L9.
- **L4 (round trip).** `fold(decodeHead(p)) = Some(p)`; when `fold(c, args) = Some(p)`,
  `decodeHead(p) ≡ (c, args)` fieldwise. `decodeHead` is total on payloads. Decoded fields are
  built **through the standard value seams** (`evalApply`/`evalRef`), never as raw `VApp`s — so
  proof-collapse and StructEta apply to decoded structure automatically (a decoded `Char`'s
  validity proof collapses to `VProof` on its own).
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
  structural recursion. This is an explicit evaluator resource limit, not a new equation. Ops are
  **derived rules**: on admitted inputs they decide equations the structural
  rules already decide (in astronomically more steps), so they add no equations and are
  decidability-benign. Each op gets a ledger row and a certification test (§10). For ops whose
  structural definitions are WF-recursive and K2-sealed (`Nat.div`-class), the justification
  target is the primitive equation lemma (`fix_eq` instances), and the native op is the *only*
  definitional computation path — parity with post-4.9 Lean.
- **L8 (closure, reserved identity, and layered validation).** The codec set is sealed in kernel
  code, with **no registration step and no kernel mutable state**. The canonical names that give
  native rules meaning are reserved: `Nat`, `Nat.zero`, `Nat.succ`, and every definition name in
  the accelerated-op table. Only the bundled default Prelude may declare them; ordinary program
  declarations, `Prelude.none`, the minimal test Prelude, and path/source-provided custom preludes
  fail with `ReservedKernelName`. Consequently a `ValueId.Const("Nat.add")` is provenance enough:
  checked source cannot attach that id to a different body. Validation is then layered where each
  layer carries exactly the obligation it can discharge:
  (a) the deep family shape check — family Type-valued and `familyArity = 0`, constructor list
  exactly the codec's, zero nullary with type the family, succ unary with field *and* result the
  family, all heads no-confusion — runs once when the reserved bundled Prelude environment is
  built and fails loudly (`NatLiteralUnavailable`). Literal checking thereafter performs only an
  authenticated family lookup; absence still raises `NatLiteralUnavailable`.
  (b) fold seams **self-validate structurally** (exact stored arity, no-confusion,
  already-packed fields, non-propositional type), protecting the value invariant even during
  Prelude construction and against malformed trusted values.
  (c) the transparency/perf test pins are the desync alarm: a bundled Prelude edit that changes
  Nat's shape makes Prelude construction fail loudly or un-packs ground data, which the pins catch.
  Reservation is deliberately simpler than attaching codec/native-op state to `ConstructorHead`
  or maintaining a trusted mutable registry.
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
  accelerated-op names to the bundled Prelude, so checked user source cannot give those names
  different declarations or bodies. The fold's local guards remain load-bearing during Prelude
  construction: a nullary zero round-trips to the same head, while a succ fold requires an
  already-packed, well-typed field. The bundled Prelude has already passed the full family check
  before any checked program can construct a literal.
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

Table: reserved canonical definition name → native implementation over payloads. Interception
point: `Interpreter.evalApply`, before `runLam`, keyed on `ValueId.Const(name)` — L8's declaration
reservation makes the name an authenticated identity without per-lambda provenance state. This
covers both `LamBody.Core` definitions and the raw-recursive native wrappers `TerminationChecker` builds
(skipping the runtime decrease check is sound exactly because no recursive call is made). The op
fires only when **all** arguments are packed; otherwise the structural body runs as today (and on
a neutral scrutinee sticks as usual). By L7 the bypass is observationally invisible.

| Op | Structural definition | Convention to pin |
|---|---|---|
| `add`, `sub`, `mul`, `beq`, `ble` | in Prelude today (structural recursion) | `sub` truncates at zero |
| `pow`, `blt` | structural; added with K3 | `pow(a, 0) = 1` |
| `div`, `mod`, `gcd` | WF-recursive; land with K2/T1, K2-sealed | `a / 0 = 0`, `a % 0 = a`, `gcd(0, b) = b` |
| `land`, `lor`, `lxor`, `shiftl`, `shiftr` | WF-recursive (binary decomposition); land with K2/T1 | — |

`pred`/`isZero` are not ops: match on a packed value already computes them in O(1) via
`decodeHead`. `beq`/`ble`/`blt` return `Bool` constructor values resolved from the trusted
lambda's closed global environment and checked against the instantiated codomain. The final op
set is a decision for M0's "literal ops used" stat; the table makes extension a ledger decision,
not an architecture change (plan §8 gate 4). Adding an op also reserves its canonical name.

Two parity notes. (1) Ground reduction is confluent to the numeral, so acceleration is
independent of the structural definition's recursion pattern (Raccoon's `add` recurses
tail-style, Lean's rewraps `succ` — same normal form on ground args). (2) Defeq parity on *open*
args (`n + 1 ≡ succ n` and friends) is a property of the structural definitions and belongs to
T1's prelude-alignment work, not to K3.

Trust stance: per plan §8 gate 4, ops are trusted outright and recorded in the ledger (§9), with
the certification harness (§10) as the engineering backstop — differential tests, not proofs.

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
- **Keys** (`ValueKey`). `Tag.Packed` mixed with a codec id and the payload's canonical bytes,
  plus `tpe.key` (as for constructor-headed `VApp`s). Key equality ⇒ defEq holds by L3⇒; distinct
  codecs mix distinct ids. No `AstNodeId`s involved — this key surface is deterministic in the
  payload and does not extend the node-id risk (kernel-theory §6 "identity keys").
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
- **Quoting** (`ValueQuote`): `VPacked` quotes to the literal node — never to a constructor
  spine (a 10⁶ literal must not quote to a 10⁶-deep term). Round trip: quote → eval → same
  payload, same key.
- **Proof collapse:** no interaction by construction — `VPacked` requires a non-propositional
  type (L1/L2), `collapseIfProof` passes it through, decoded proof fields collapse at their own
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
- **PrettyPrinter:** packed values print as numerals / string literals (diagnostics only).

## 7. String literals (staged)

Gated on the Prelude growing `Char`/`String` (pre-M1). Factoring chosen for K4-compatibility:
`String` (a one-field struct) is eta-eligible, and a whole-string packed form would be a second
representation competing with StructEta's canonical constructor form — exactly the mixed-rule
situation K4 forbids. So the packed value lives **at the field**:

- `StrLit s` evaluates to `VCtor(String.mk, [VPacked(CharList, s)])` — the `String` layer stays
  constructor-headed (K4 canonical), the char *list* is packed.
- CharList codec: payload Scala `String`; `decodeHead("") = List.nil Char`;
  `decodeHead(c ++ rest) = List.cons(char c, VPacked(rest))` with the `Char` built via
  `evalApply` (its proof field collapses on its own, L4). `canonical = false` — structurally
  built ground char lists never pack, so defEq/unify go through the peel arms. No `fold` beyond
  the trivial round trip (cons of packed tail *may* re-fold; nothing requires it), no ops (plan
  §4.K3: none needed).

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
- **× native-op identity:** accelerated names are reserved to the bundled Prelude (L8), so
  name-keyed interception cannot attach a trusted equation to a user-defined body. Custom and
  prelude-less environments simply have no native Nat declarations.
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
- The op table is documented as derived rules under the §4-adjacent trust note (plan §8 gate 4
  default: trusted, ledgered) — one line per op, conventions included. The same ledger entry
  records reserved-name authentication as the reason a table key can identify the bundled
  definition rather than an arbitrary user body.
- The test pins named in §10 live in `NativeLiteralTests`; any future codec must re-walk §8 and add its
  own rows before landing.

## 10. Test plan

- **Certification harness** (`NativeLiteralTests`), tiered by what each tier can afford:
  (a) *structural differential* — the op against its structural definition under an op-table
  kill-switch, on operand ranges sized to the structural path's cost (it is O(magnitude) and
  compounds: comparisons and `add`/`sub` afford dozens, `mul` single digits, `pow` operands ≤3),
  always including the boundary cases (0, 1, equal args, near-equal, `sub` underflow, `pow` zero
  exponent, and the `div`/`mod`/`gcd` zero conventions when those land);
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
  `NativeOperationLimitExceeded` before either host allocation or structural fallback.
- **Consistency suite:** keep the existing proof-theoretic probes semantically unchanged. The
  probe-worthy payload-apartness surface is a law-violating codec, which L8's sealed set makes
  unconstructible; assert that at compile time (no public codec constructor).
- **Reservation pins:** defining `Nat`, its constructors, or an accelerated `Nat.*` name outside
  the bundled default Prelude raises `ReservedKernelName`; the bundled Prelude still loads and
  its reserved operations accelerate normally.

## 11. Residual gaps and non-goals

- **Mixed-form decrease on non-canonical codecs:** a recursion whose metric mixes packed and
  structurally built char lists may be rejected (conservative false in `isStrictSubterm`).
  Acceptable: kernel workloads do not recurse over string payloads; revisit only if T4's failure
  taxonomy says otherwise.
- **Same-codec packed pairs without L9 report stuck** in unification rather than peeling both
  sides to look for a clash — conservative, never apart. Revisit with the first non-L9 codec.
- **The `VPacked` payload field is `BigInt`-typed** in the first implementation (Nat is the only
  codec); the promised per-codec payload type (`codec.P`) is deferred to the CharList landing
  (§7). Architecture cost when it lands: one field generalization plus the codec methods that
  read it — no seam changes.
- **No container codecs, no user codecs** (§1). Array-backed ground-data storage is revisited
  together with the P1 caching decision (hash-consing vs compact spines are alternatives).
- **No custom datatype under the reserved Nat identity.** Custom or prelude-less programs use a
  different canonical family name; supporting an alternate implementation with the native Nat
  names would require a provenance mechanism and is intentionally out of scope.
- **Open-arg unfolding parity** of Prelude definitions with Lean's (T1 concern, §5 note 2).
- **Op set growth** (`log2`, others): only via M0 stats + a new ledger row each.
- Negative literals, `Int`/`Float` primitives: not planned; the export encodes them over Nat.
