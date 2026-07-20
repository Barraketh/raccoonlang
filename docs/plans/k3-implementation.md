# K3 Implementation Plan — `VPacked` native literals

Status: **implemented** (first slice 2026-07-14; full-K3 continuation and simplification pass
2026-07-20). The remaining eight Nat rows and CharList/`StrLit` are exercised against a
kernel-owned synthetic bootstrap. Production acceptance of the checked translated `Init`
definitions and String layout remains a T1 integration gate.

**T1 trust-model addendum (2026-07-17).** The implementation below originally had one trusted
bootstrap producer, the bundled default Prelude. T1 adds a second kernel-owned path: the explicit
pinned translated-`Init` bootstrap. Both follow Lean's model—exact reserved native-operation
identities receive the kernel table's equations outright; their declarations and types are checked,
but no semantic body recognizer, declaration fingerprint, or per-operation capability is required.
Ordinary imports and all custom/prelude-less source paths remain unprivileged. References below to
“the bundled Prelude” describe the first implementation and should be read as “the selected trusted
bootstrap” when applying this plan to T1.

Implementation record. The **design spec is `docs/native-literals.md`**; this document retains the
code-level decisions and historical first-slice handoff after a full survey of the integration
points. Also read `STYLE.md` and the preamble + §6 of `docs/kernel-theory.md` (the design spec's
§8 walks the interaction checklist; nothing here changes those answers).

The original landed scope was the **Nat codec, `NatLit` syntax, and seven then-definable
accelerated ops** (`add/sub/mul/pow`, `beq/ble/blt`). Sections 1–7 retain that first-slice handoff
and should be read as implementation history where they show a `BigInt`-only `VPacked`. Section 0
below records the implemented full-K3 continuation and supersedes those staged notes. Container codecs remain out of
scope.

Build: Scala 2.13, sbt, `-Xfatal-warnings` (exhaustivity warnings are fatal — the compiler will
point at every `match` that needs a new case; treat each one deliberately, don't blanket-default).
Tests: munit, `sbt test`, single suite via `sbt 'testOnly com.raccoonlang.NativeLiteralTests'`.

## 0. Full-K3 continuation — implemented decisions (fixed 2026-07-17, landed 2026-07-20)

These are implementation requirements, not remaining options.

### 0.1 Native Nat table and resource behavior

- Extend the table with `Nat.div`, `Nat.mod`, `Nat.gcd`, `Nat.land`, `Nat.lor`, `Nat.xor`,
  `Nat.shiftLeft`, and `Nat.shiftRight`. Division and modulus by zero return `0` and the dividend;
  `gcd(0, b) = b`. Bitwise operations use non-negative `BigInt` semantics.
- The resulting fifteen entries comprise Lean's fourteen pinned binary native identities plus
  `Nat.blt`. Keep `Nat.blt` because M0 found it in `Init` and the first slice already implements
  it, but label it in code comments, the ledger, and T1's manifest as the deliberate Raccoon
  extension—not as a Lean kernel entry. It receives the same exact-name, trusted-bootstrap rule.
- Add `MaxShiftLeft: BigInt = BigInt(1) << 24`. For `a != 0`, a larger count raises
  `NativeOperationLimitExceeded("Nat.shiftLeft", count, MaxShiftLeft)` and never attempts host
  allocation or structural fallback. `0 << count` returns packed zero for every count.
  `shiftRight` has no count limit: compare the arbitrary-precision count with `a.bitLength` first;
  return zero when it is at least that length, and convert to `Int` only in the smaller case.
- Replace the former dispatch-only `Map[String, NatOp]` with one authoritative immutable
  `NativeNatOpSpec` table. Each row owns the exact name, host implementation, and typed result
  subtype (`NatOpSpec` or `BoolOpSpec`), origin (`LeanKernel` or `RaccoonExtension`), and required bootstrap
  profiles (`BundledSourcePrelude`, `PinnedTranslatedInit`, `SyntheticFullK3`). Dispatch, `opNames`,
  `reservedNames`, expected-type validation, future manifest metadata, extension labeling, and missing-operation
  checks all derive from this table. The private typed subtype exposes the derived read-only
  `returnsBool` classification used by T1's manifest; there is no second handwritten list of native
  names, result types, or origins. `Nat.blt` is the sole `RaccoonExtension` row; the bundled
  profile selects the existing seven rows, and each full profile selects all fifteen.
- Add `Packed.validateNativeOpDeclaration(name, value, env)`. Ordinary checking first produces an
  immutable candidate environment; before the loader commits that candidate to the bootstrap fold,
  it validates the declaration's applicable transparent `VLam` carrying
  `ValueId.Const(name)`, two explicit `Nat` binders, and the exact checked telescope
  `Nat → Nat → Nat` for
  `add/sub/mul/pow/gcd/mod/div/land/lor/xor/shiftLeft/shiftRight`, or `Nat → Nat → Bool` for
  `beq/ble/blt`, modulo only Raccoon's already-validated implicit/explicit calling-convention
  representation. Requiring the `VLam` is an implementation-representation check, not semantic
  body recognition: current `Interpreter.evalApply` intercepts native operations only on that
  value form. An opaque/symbolic value under a native name fails validation rather than silently
  becoming an operation that can never fire. Any identity, value-form, or telescope failure is the
  typed `NativeOperationDeclarationMismatch(name, reason, span)`; T1 wraps it with export
  provenance rather than exposing a checker or pattern-match exception.
- Add `Packed.validateRequiredNativeOps(env, profile)`. The bundled source Prelude installer passes
  `BundledSourcePrelude`, so the eight T1-gated definitions may remain absent there. T1 passes
  `PinnedTranslatedInit` and reports `MissingNativeOperation` for any of its fifteen absent rows;
  the synthetic fixture passes `SyntheticFullK3`. The closed profile value is a bootstrap
  completeness selector only: it is not stored in `Env`, attached to a lambda, or consulted by
  dispatch. Missing rows are returned in stable table order and reported as the typed
  `MissingNativeOperation(name, profile)` failure at the first absent row.
- Define `NativeOperationDeclarationMismatch` and `MissingNativeOperation` in `Errors.scala` with
  the same `TypeError`/span conventions as the existing native-literal errors. Importers translate
  them into provenance-bearing diagnostics; neither validator may leak `MatchError`, `WTF`, or a
  host arithmetic exception for malformed declarations.
- Arithmetic results are still checked per call against the instantiated Nat codomain before
  packing, and comparison constructors are checked against the instantiated Bool codomain. The
  declaration check above is the loud admission check; these per-call checks remain local invariant
  defenses and may fall through. Once a declaration passes and enters a private bootstrap stage,
  its exact reserved identity may reduce while later declarations are checked. A failed stage is
  discarded atomically. No runtime enablement bit, per-operation capability, semantic body
  recognizer, or fingerprint is added; the trusted-bootstrap agreement is the chosen Lean-style
  TCB assumption.

### 0.2 Sealed payloads and codec API

Replace the landed `BigInt` field with a sealed sum whose constructors and codec factories are
kernel-private. Use non-case classes (or equivalently restricted `copy`/`apply` methods) so generated
case-class APIs cannot bypass validation:

```scala
sealed trait PackedPayload
final class NatPayload private (val value: BigInt) extends PackedPayload
final class CharListPayload private (private val scalars0: Vector[Int]) extends PackedPayload {
  private[raccoonlang] def scalars: Vector[Int] = scalars0
}

final class VPacked private (
    val codec: PackedCodec,
    private[raccoonlang] val payload: PackedPayload,
    val tpe: Value
) extends Value with UpdatableType
```

The only construction surface is the private `VPacked` companion/factory API:

```scala
private[raccoonlang] def nat(value: BigInt, tpe: Value): VPacked
private[raccoonlang] def charList(codec: CharListCodec, scalars: Vector[Int]): VPacked
private[raccoonlang] def charListTail(parent: VPacked): VPacked
private[raccoonlang] def retype(packed: VPacked, defEqTpe: Value): VPacked
```

`nat` rejects negative values and a type with syntactic dependencies. `charList` scans once and
rejects every non-Unicode scalar (anything outside `0..0xd7ff` and `0xe000..0x10ffff`), fixes the
packed type to the closed `codec.listCharTpe`, and is the only entry point from AST/import data.
`charListTail` is callable only by `CharListCodec.decodeHead`; it drops one element from an
already-validated persistent vector without rescanning the suffix. This makes peeling a string
linear overall rather than accidentally quadratic.

`retype` is the `UpdatableType.withTpe`/materialization seam. It requires the requested replacement
to be `defEq` the old type (and, for CharList, `defEq codec.listCharTpe`) but returns the original
packed value without replacing its authenticated closed type. This deliberate exception to
“expected type wins” keeps `ValueKey` and quote/evaluate round trips stable when two defEq type
representatives have different keys. Since every permitted packed type is closed, materialization
has no legitimate type substitution to perform. No public `copy`, raw payload constructor, or
generic `(codec, payload, tpe)` factory exists.

Add codec methods `acceptsPayload`, `payloadEquals`, and `mixPayloadKey` (the last may feed the
existing key builder directly rather than allocate bytes). They match exhaustively on the sealed
payload sum and reject codec/payload mismatches. The CharList implementation hashes/compares the
remaining scalar sequence by content, so a decoded tail is identical to an independently
introduced equal suffix. Update every payload match exhaustively: `ValueKey`, defeq/unification,
termination, quoting, pretty-printing, tests, and the native-op table.

For `ValueKey`, retain Nat's signed-magnitude `BigInt.toByteArray` encoding under the Nat codec
tag. Under the distinct stable CharList codec tag, first mix `codec.listCharTpe.key`, then the scalar
count and each scalar as an unsigned 32-bit integer in order. After either codec-specific payload,
always mix the packed value's actual `p.tpe.key`, preserving the current `VPacked`/constructor-key
invariant and `docs/native-literals.md` §6. The CharList factory fixes that actual type to the
descriptor's `listCharTpe`, and `retype` preserves it. Do not hash a host `String`, collection node,
layout object identity, or cached JVM hash code.

Split the old informal fold law into total decode correctness plus optional fold round trip.
`NatCodec` remains canonical and fold-capable. `CharListCodec` is non-canonical, decode-only, and
does not claim L9; there is no global CharList fold or codec registry.

### 0.3 Validated String layout and environment-independent peeling

Add a kernel-private `ValidatedStringLayout` produced only by a trusted bootstrap after the
following exact checks. “Expected constructor” is not a name-only check:

- Resolve the already-validated `Nat`, plus `Char`, `List`, `String`, `String.mk`, `List.nil`,
  `List.cons`, and `Char.ofNat` from the private trusted stage. `Char`, the instantiated `List Char`,
  and `String` must be non-propositional, Type-valued inductive instances.
- `String` has family arity zero, constructor list exactly `[String.mk]`, and an installed
  `ProjectionInfo` for which `etaEligible = true`, `fieldCount = 1`, and projection index `0` is the
  sole field. Its `ctorHead` is the exact resolved `String.mk`, has no-confusion, has no erased
  family arguments and exactly one stored argument, whose instantiated type is `defEq List Char`;
  its instantiated result is `defEq String`.
- Resolve the exact `List Char` family instance and require constructor list exactly
  `[List.nil, List.cons]`; it is therefore not eta-eligible. Instantiate each constructor's erased
  family binders with the arguments of that same family instance and require their
  `numErasedFamilyArgs` to consume exactly those family arguments. `List.nil` has no stored fields
  and result `defEq List Char`. `List.cons` has exactly two stored fields, first `defEq Char` and
  second `defEq List Char`, and result `defEq List Char`. Both heads have no-confusion and are the
  exact resolved globals with those canonical names.
- `Char.ofNat` has exactly the checked callable type `Nat → Char`; its argument family is the
  already-validated Nat representation. The retained `natTpe`, `charTpe`, `listCharTpe`,
  `charOfNat`, `stringTpe`, and `stringMk` values have empty syntactic dependencies and contain no
  stage-local references. Validation failure raises `StringLiteralUnavailable` with the failed
  condition; it never issues a partial layout.

The layout owns one immutable private `CharListCodec` plus the checked closed values needed to
apply `Char.ofNat`. This descriptor is deliberately per bootstrap: `decodeHead` is called from
defeq, unification, matching, and termination code that has no `Env`. It may retain closed checked
bootstrap values, but the `CharListPayload` itself contains no `Value`s and `synDeps` remains only
the packed field type's dependencies.

The concrete ownership shape is:

```scala
final class CharListCodec private[raccoonlang] (
    val natTpe: Value,
    val charTpe: Value,
    val listCharTpe: Value,
    val charOfNat: Value
) extends PackedCodec

final class ValidatedStringLayout private[raccoonlang] (
    val stringTpe: Value,
    val stringMk: ConstructorHead,
    val charListCodec: CharListCodec
)
```

All constructor parameters are closed and are created only by
`Packed.validateStringLayout(env)`. `CharListCodec` equality for packed-value compatibility is
descriptor identity within the selected immutable environment; its `ValueKey` codec tag is the
stable kernel CharList tag combined with `listCharTpe.key`, never a JVM identity hash. Environments
and their layout instances are not mixed.

Store the issued layout in immutable environment state, not a global registry:

```scala
final case class NativeLiteralState private[raccoonlang] (
    stringLayout: Option[ValidatedStringLayout]
)

final case class Env(
    globals: Map[String, GlobalBinding],
    locals: VectorMap[CoreAst.LocalRef, Value],
    nativeLiterals: NativeLiteralState
)
```

`Env.empty` starts with no layout; every existing `copy`-based global/local/closure operation
preserves the field. A private trusted-bootstrap installer atomically replaces `None` with the one
validated layout after the String block and `Char.ofNat` have checked; a second installation is an
internal error. T1 stages this state change with the String transaction so rollback cannot leak a
layout. Typechecking and evaluation of `StrLit` read `env.nativeLiterals.stringLayout` or raise
`StringLiteralUnavailable`; decoded `VPacked` fields carry the descriptor and need no environment.
Ordinary imports have no installer permit.

Following the selected Lean trust model, layout issuance trusts the exact bootstrap `Char.ofNat`
identity to map valid scalars injectively to the intended `Char`. Its declaration and type are
checked, but no semantic body recognizer or fingerprint is added. Record this assumption in T1's
manifest and add Unicode/injectivity differential tests as engineering alarms. Ordinary imports
cannot construct a `ValidatedStringLayout` from a same-named declaration.

For scalar vector `s`, the codec implements:

```text
decodeHead([])        = (List.nil, [])
decodeHead(c +: rest) = (List.cons, [evalApply(Char.ofNat, VPacked.nat(c, natTpe)),
                                    VPacked.charListTail(current)])
strictlyLess(xs, ys)  = xs is a proper suffix of ys
canonical             = false
refutesUnequalPayloads = false
```

The descriptor returns constructor names and ordinary checked field values; it never fabricates a
`ConstructorHead`. Mixed packed/constructor equality and unification use the existing peel paths.

### 0.4 `StrLit`, quotation, and Unicode boundary

- Add `StrLit(scalars: Vector[Int], span: Span)` to SurfaceAst, CoreAst, and ElabAst. T1's matching
  export-IR node is exactly `StrVal(scalars: Vector[Int])`, never a host-`String` payload. Evaluation
  passes the AST payload to `VPacked.charList(layout.charListCodec, scalars)`; no raw
  `CharListPayload` construction is available. The surface parser accepts double-quoted literals
  with the JSON-style escapes fixed below; it combines a valid `\uXXXX` surrogate pair into one
  supplementary scalar and rejects an unpaired escape. The export reader/parser converts without
  normalization to validated Unicode scalars and rejects invalid UTF-8, unpaired host UTF-16
  surrogates, and non-scalar code points before constructing the node. Elaborator lowering is
  one-to-one.
- Typechecking requires the current trusted bootstrap's `ValidatedStringLayout` and assigns its
  `String` type. Evaluation constructs the canonical outer `String.mk` value with one packed
  `List Char` field through the ordinary constructor application seam.
- Quote the exact layout `String.mk` head with exactly one field using that layout's
  `CharListCodec` directly as `StrLit`; leave every other constructor on generic quotation. Quote
  a standalone packed field as
  `ElabAst.Term.Proj("String", 0, ElabAst.Term.StrLit(scalars, span), span)`. This residual has type
  `List Char`, re-evaluates to the same packed field/key, and avoids an O(n) constructor expansion.
- Add all exhaustive AST traversal, captured-reference, inliner, pretty-printer, and typechecker
  cases. Pretty-print strings with deterministic scalar-based escaping; never normalize through a
  host locale or Unicode normalization library. Escape quote, backslash, backspace, form feed,
  newline, carriage return, and tab with standard JSON-style escapes; encode other C0 controls as
  four-hex-digit `\uXXXX`; emit every other scalar literally.
  The exact layout `String.mk` over its packed field prints as the quoted literal; a standalone
  CharList payload prints as `proj[String,0]("...")`, while Nat payloads remain bare numerals.
- Mirror `NatLiteralUnavailable` with a typed `StringLiteralUnavailable` when no validated layout
  is installed. Reader/parser malformed-Unicode failures remain provenance-bearing input
  diagnostics and must not escape as a JSON-library exception, `MatchError`, or host encoding
  replacement character.

### 0.5 Continuation tests and completion gate

Landed K3 coverage:

- [x] Equation examples for all eight new Nat operations, including zero divisors, gcd zero cases,
      bitwise identities, and shifts; large random host-oracle tests cover the native wiring.
- [x] Resource pins: `shiftLeft(1, 2²⁴)` succeeds; `shiftLeft(1, 2²⁴ + 1)` raises without fallback;
      `shiftLeft(0, 2²⁴ + 1) = 0`; `shiftRight(1, 2²⁴ + 1) = 0` without host-`Int` conversion.
- [x] String pins for empty, ASCII, BMP, and supplementary-plane literals; one-layer list/Char
      matching; standalone field projection quote/re-evaluation; suffix key equality;
      malformed-Unicode rejection; and layout preservation through environment materialization.
- [x] Table/profile/admission pins distinguish `Nat.blt`, require all fifteen synthetic-profile
      rows, reject a missing row, reject a wrong Nat-result telescope, and reject opaque or
      misidentified declarations. Layout negatives cover field type, arity, projection,
      no-confusion, and closure.
- [x] Direct hardening pins cover all fifteen reserved operation names, derived Bool-result
      classification, implicit native binders, a wrong Bool-result telescope, distinct
      scalar/`Char.ofNat` behavior, remaining String result/constructor corruptions, a
      20,000-scalar peel, and atomic streamed-bootstrap finalization.

Remaining T1 integration (not required to use the landed synthetic K3 path):

- [ ] T1 must run equation/differential alarms against the actual checked translated-`Init`
      definitions, then validate the `PinnedTranslatedInit` profile and emit the table-derived
      manifest. The synthetic fixture intentionally supplies only type-correct trusted bodies, so
      it cannot serve as a structural oracle for those eight operations.

### 0.6 Post-landing simplification shape (2026-07-20)

- `Prelude.Config` carries one sealed `BootstrapAuthority`, not an independently selectable
  reserved-name permit and native profile. `Interpreter.trustedBootstrap` derives both from the
  authority, and `buildTrustedBootstrapEnv` folds a complete program through that context. Native
  authority constructors are closed; the bundled, synthetic, and pinned values are kernel-owned,
  and ordinary callers receive `Unprivileged`.
- Native result classification is represented by the private `NatOpSpec`/`BoolOpSpec` row subtype,
  eliminating the former `NativeResultKind` plus `NativeNatResult` duplication and per-call result
  wrapper. The shared row exposes name, origin, required profiles, and the subtype-derived
  read-only `returnsBool` classification needed by T1's manifest.
- Sealed-payload destructuring is centralized in `Value.PackedPayload`. Codec-internal hot paths
  use direct authenticated extractors; the `VPacked` observation helpers return `Option` only at
  call sites that do not already know the codec.
- `UnicodeScalarString` is the shared scalar validator/parser/renderer. `LanguageParser` translates
  its committed decode failures into `ParseError`, and `PrettyPrinter` uses the same scalar-aware
  escaping path.
- Synthetic source assembly (`bundled Prelude + full-K3 addendum`) lives in
  `NativeLiteralTests`. Production exposes only the narrow package-private trusted-source entry
  point accepting a native `BootstrapAuthority`. `Interpreter.trustedBootstrap` now exposes the
  same authority-bound `initialEnv`, `add`, and `finish` operations to a streaming T1 caller
  without exposing the raw permit; the whole-program loader is a fold over that context.

## 1. Survey findings the implementation relies on

Facts verified in the current tree (line numbers approximate but recently accurate):

1. **Constructor values are born at exactly two evaluation seams**:
   `Interpreter.evalRef` (nullary heads, `Interpreter.scala:138`) and `Interpreter.evalApply`'s
   `ConstructorHead` branch (`:169-171`). A third *rebuild* seam exists in
   `ValueOps.materialize`'s `VApp` case (`ValueOps.scala:28-29`) — store-solution substitution can
   turn `succ ?x` with `?x := ⟨packed 4⟩` into a ground constructor form, so it must re-fold.
   MatchChecker's reachable-constructor probe is a fourth seam: its nullary `Nat.zero` candidate
   is ground and must fold, while `Nat.succ` of a fresh field remains structural. Other `VCtor`
   factories (`BinderOps.freshCtorArgsAndResult`, StructEta expansion) produce fresh-var or struct
   forms that the fold's packedness checks leave alone naturally.
2. **Match evaluation** pattern-matches `VCtor` and dispatches by constructor *name*
   (`Interpreter.evalMatch`, `:289-308`) — a packed scrutinee needs only `(name, args)` from
   `decodeHead`, never a real `ConstructorHead`.
3. **Key trust**: `defEq` short-circuits on `ValueKey` equality (`ValueEquivalence.scala:136-141`,
   kernel-theory §2 "identity keys"). A packed key must therefore mix the **full payload bytes**
   — never `hashCode` — or a collision is a defEq unsoundness (the §7.7 case-law genre).
4. **The runtime decrease check does not exist.** `TypeChecker.checkLam:294-301` binds
   `TerminationChecker.rawRecursiveSelf` as the recursive self **only while checking the declaring
   body** (recursive calls there produce residuals after the decrease check);
   `Interpreter.runLam:246-248` binds the finished lambda afterward, and runtime recursion is
   unchecked. Consequence: the packed `isStrictSubterm` rule is a *check-time completeness* rule,
   not a runtime-perf necessity. (The design spec has been corrected accordingly.)
5. **`Env.closeForEval` keeps globals** (`Env.scala:93-102`) — closed lambda envs can resolve
   `Bool.true`/`Bool.false` for the comparison ops, and `NatLit` residuals can resolve `Nat`.
6. **`MatchChecker.checkMatch` has a ground-scrutinee arm** (`MatchChecker.scala:198-205`): a
   `VCtor` scrutinee admits exactly its own constructor's case (`UnreachableCase` otherwise).
   Packed scrutinees must mirror it.
7. **`telescope/Projection.project`'s `CtorField` step** (`Projection.scala:251-255`) reads stored
   fields of `VCtor`s; implicits forced through literal indices hit it with a packed value.
   `Projection.compile` needs nothing — it matches patterns over *fresh vars*, and `succ`-of-var
   never folds.
8. **`PrettyPrinter` has a positional 5-field pattern** on `ConstructorHead`
   (`PrettyPrinter.scala:178`). This is one reason the design below adds **no field** to
   `ConstructorHead`.
9. **Existing tests assert unary Nat forms** (e.g. PreludeTests
   `assertEquals(PrettyPrinter.print(natRes), "Nat.succ(Nat.succ(Nat.zero))")`, and
   `ctorName(res) == "Nat.zero"` on Nat-valued results). These are implementation-worldview
   assertions and must be updated to the packed canonical form (§7 below). **Consistency tests
   are different** — kernel-theory §8: never weaken them; if one goes red the change is unsound.

## 2. Resolved design decisions (and why)

**D1 — No install hook, registry state, or `ConstructorHead` field; reserve native Nat names.**
This is the design spec's L8 model. `NatCodec` is a static `case object`, and the kernel reserves
`Nat`, `Nat.zero`, `Nat.succ`, and every canonical name in the accelerated-op table. The landed
sealed `BootstrapAuthority` has unprivileged, bundled-source, synthetic-full-K3, and pinned-
translated-`Init` modes; only the native modes derive the reserved-name permit and validation
profile. The pinned mode is ready for T1 to consume but is not an ordinary importer entry point. Ordinary program/import
declarations, `Prelude.none`, the minimal test Prelude, and path/source-provided custom preludes fail with
`ReservedKernelName`. This makes canonical-name dispatch authenticated without per-lambda state:
unprivileged checked source cannot attach `ValueId.Const("Nat.add")` to a different body.

Implement the exception as an immutable declaration-loading capability used only while building
a trusted bootstrap—never as a global flag and never retained in `Env`. Fold seams still
self-validate exact stored arity, `noConfusion`, already-packed arguments, and a
non-propositional result type, protecting the value invariant during Prelude construction and
against malformed trusted values. A `ConstructorHead` field would break positional patterns and
case-class equality; a mutable registry is unnecessary.

**D2 — Reserved-name ops self-validate per call and fall through, never error.** Interception
happens in `evalApply` keyed on `ValueId.Const(name)`; D1 proves that a matching id denotes a
trusted-bootstrap definition. The op fires only when every argument is a packed Nat
*and* the result type checks out (`defEq` of the instantiated codomain against the argument's own
Nat family for arithmetic; a resolvable nullary `Bool` constructor whose type is `defEq` the
codomain for comparisons). Any mismatch silently falls back to the structural body — the op only
ever *shortcuts* it, which is L7 by construction. This describes the landed per-call defense; full
K3 additionally performs the loud name/value/type/profile admission checks in §0.1. Differential
and transparency pins remain semantic-desynchronization alarms.

**D3 — Deep validation once, when the trusted bootstrap is built.** After the privileged
bootstrap environment is complete, `Packed.validateNatFamily(env)` validates that `Nat` is a
**Type-valued** `familyArity == 0`
inductive with constructors exactly `[Nat.zero, Nat.succ]`; zero nullary, `noConfusion`, type
`defEq` the family; succ unary, zero erased args, `noConfusion`, field type **and result type**
`defEq` the family — the result check is redundant for genuinely installed inductives
(`InvalidConstructorResult` forces it) but this function is the validation boundary; be
explicit, not clever. Failure is the `NatLiteralUnavailable` error. `CA.Term.NatLit` checking then
does only `Packed.natFamily(env, span)`, a constant-time authenticated lookup; absence raises the
same error. `Interpreter.evalTerm`'s `NatLit` case is equally light
(`VPacked(NatCodec, v, env("Nat"))`).

**D4 — Peel by borrowing the concrete side's head.** Codecs expose constructor *names* only.
Where defEq/unify must compare packed against `VCtor(h, …)` and names match, construct the
decoded layer as `VCtor(h, decodedArgs, p.tpe)` — reusing `h` — and recurse into the ordinary
machinery. Guard `decodedArgs.length == h.totalArity - h.numErasedFamilyArgs` first (the `VApp`
constructor has a `require` that would throw).

**D5 — The termination rule never decodes.** Packed-vs-packed strict subterm is a direct payload
comparison (`strictlyLess`); decode-recursion on a 10⁹ payload is a hang.

**D6 — `VPacked` is `UpdatableType`.** The first slice used `withTpe = copy`; full K3 replaced that
with the checked, identity-preserving `VPacked.retype` factory in §0.2. `Value.ascribe` still uses
the uniform interface, but a packed value retains its authenticated closed type after checking the
requested representative is defEq. This prevents both codec/type mismatch and key drift across
quote/evaluate round trips; packed data can never be defEq a proposition.

## 3. Changes by file

Recommended order: **A** = 3.1–3.3a *plus* the exhaustive-match cases 3.1 forces — adding a case
to `sealed trait Value` breaks compilation (fatal warnings) in `ValueKey.orderKey` (3.2),
`ValueOps.materialize` (3.5), the three positivity traversals in `InductiveChecks` (3.5a), and
`PrettyPrinter.print` (3.10's value-printer item) — so phase A is complete only when all of
those cases are in. Then **B** = the remaining seams (3.4–3.9), **C** = syntax (3.10–3.12),
then tests.

### 3.1 `Value.scala` — value form + codec

Insert immediately before the `ConstructorHead` doc comment (after the `VProof` companion). This
block is ready to paste:

```scala
  /**
   * A packed representation codec (K3, docs/native-literals.md §3): one type's compact host-side
   * representation for ground data. The set is closed and kernel-curated by design — each codec is
   * trusted code inside defeq (§1 scope decision). Laws L1–L9 of the spec govern every instance;
   * the ones load-bearing here:
   *   - L3 (injectivity): payload equality ⇔ defEq of decodings. Key trust rests on it;
   *     propositional apartness deliberately does not.
   *   - L5 (canonicity): when `canonical`, every ground value of the type is packed from birth
   *     (all fold seams: `Interpreter.evalRef`/`evalApply`, `ValueOps.materialize`), so key-only
   *     defEq is complete.
   *   - L6 (order realization): `strictlyLess` is exactly reachable-by-≥1-constructor-field-steps
   *     on decodings, making the packed structural-decrease rule an instance of the existing tree
   *     order, not a new one.
   *   - L9 (clash realization): only codecs whose unequal payloads reach a derivable constructor
   *     clash may use payload apartness.
   */
  sealed abstract class PackedCodec {
    /** L5: every ground value of the type is packed; no ground constructor-headed value exists. */
    def canonical: Boolean

    /** One constructor layer of the payload: canonical constructor name plus stored args (which
      * may be packed again). Total on payloads (L4).
      */
    def decodeHead(v: VPacked): (String, Vector[Value])

    /** Strict order realized by constructor-field steps on decodings; well-founded (L6). */
    def strictlyLess(candidate: VPacked, root: VPacked): Boolean

    /** L9 claim: unequal payloads decode to a constructor clash between derivable-no-confusion
      * heads at finite depth. Gates payload apartness in unification — L3's definitional
      * inequality alone is NOT propositional apartness under the planned axioms (funext;
      * kernel-theory §4).
      */
    def refutesUnequalPayloads: Boolean
  }

  /** Nat as arbitrary-precision integers (docs/native-literals.md §4). Canonical: `Nat.zero` and
    * `Nat.succ`-of-packed fold at every value-birth seam, so no ground `succ`-spine ever exists.
    */
  case object NatCodec extends PackedCodec {
    val familyName = "Nat"
    val zeroName = "Nat.zero"
    val succName = "Nat.succ"

    override def canonical: Boolean = true

    override def decodeHead(v: VPacked): (String, Vector[Value]) =
      if (v.payload == 0) (zeroName, Vector.empty)
      else (succName, Vector(VPacked(NatCodec, v.payload - 1, v.tpe)))

    override def strictlyLess(candidate: VPacked, root: VPacked): Boolean =
      candidate.payload < root.payload

    // First-order decodings: unequal numerals clash (zero vs succ) at depth min(m, n).
    override def refutesUnequalPayloads: Boolean = true
  }

  /**
   * A packed literal (K3, docs/native-literals.md §2): ground, closed data whose payload is a host
   * value with no `Value`s inside (L2) — so it cannot capture vars, hide proofs, occur in
   * positivity, or block. Constructor form is derived on demand, one layer at a time
   * (`codec.decodeHead`) — the dual of StructEta, which maintains constructor form eagerly.
   * Never propositional (packed types are Type-valued inductives, L1).
   *
   * Historical first-slice shape: the payload was `BigInt` because Nat was the only codec.
   * Full K3 replaced this field with the sealed sum and private factories in §0.2.
   */
  final case class VPacked(codec: PackedCodec, payload: BigInt, tpe: Value) extends Value with UpdatableType {
    require(payload >= 0, s"Packed payload must be non-negative: $payload")
    require(!isPropositionType(tpe), s"VPacked requires a non-propositional type, got $tpe")

    override lazy val synDeps: DepSet = tpe.synDeps

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }
```

Also extend `needsStructuralDefEq` (`Value.scala:94-100`) with, before the default:

```scala
      case p: VPacked => !p.codec.canonical
```

(Canonical codecs resolve entirely through the key fast path; a future non-canonical codec must
take the structural/peel path against constructor forms.)

Audit note: `collapseIfProof` needs no change (`VPacked` hits the non-proposition arm);
`Blocker`/`Blocked`/`ConstSpine` extractors correctly return `None`; `StructEta.expandIfStruct`
has a default arm and Nat is not eta-eligible.

### 3.2 `ValueKey.scala` — trusted key

Add `val Packed = 18` to `Tag`. Add to `orderKey`:

```scala
    case p: Value.VPacked =>
      // Payload-derived and deterministic (no node ids). Key equality ⇒ defEq rests on codec
      // injectivity (L3). Full payload bytes, never hashCode: a collision here would be a defEq
      // unsoundness (kernel-theory §7.7 genre).
      val codecId = p.codec match { case Value.NatCodec => 1L }
      mixKey(mixBytes(mixLong(tag(Tag.Packed), codecId), p.payload.toByteArray), p.tpe.key)
```

with a helper packing 8 bytes per `mixLong` round:

```scala
  private def mixBytes(key: Key, bytes: Array[Byte]): Key = {
    var cur = mixLong(key, bytes.length.toLong)
    var acc = 0L
    var n = 0
    var idx = 0
    while (idx < bytes.length) {
      acc = (acc << 8) | (bytes(idx) & 0xffL)
      n += 1
      if (n == 8) { cur = mixLong(cur, acc); acc = 0L; n = 0 }
      idx += 1
    }
    if (n > 0) cur = mixLong(cur, acc)
    cur
  }
```

### 3.3 `Packed.scala` — new file: fold seam, ops, literal validation

```scala
package com.raccoonlang

import com.raccoonlang.Value._

import scala.util.DynamicVariable

/** K3 native literals (docs/native-literals.md): the fold seam, the accelerated-op table, and
  * bundled-Nat validation. The value forms (VPacked/PackedCodec) live in Value.scala.
  */
object Packed {

  /** Fold seam (canonicity, L5; validation layering, L8(b)): re-pack a constructor application
    * over packed fields. Keyed by canonical constructor name and self-validating — exact stored
    * arity, no-confusion, already-packed fields, and a non-propositional result type (a
    * Prop-declared lookalike must collapse, never pack; `VPacked`'s require would throw) — so a
    * same-named constructor of a different shape never folds. Deep family validation happens
    * once after the selected trusted bootstrap is built (`validateNatFamily`); checked syntax is trusted
    * downstream (kernel-theory preamble).
    */
  private[raccoonlang] def foldCtor(
      head: ConstructorHead,
      storedArgs: Vector[Value],
      tpe: Value
  ): Option[VPacked] =
    head.name match {
      case NatCodec.zeroName
          if head.totalArity == 0 && storedArgs.isEmpty && head.noConfusion &&
            !isPropositionType(tpe) =>
        Some(VPacked(NatCodec, 0, tpe))
      case NatCodec.succName
          if head.totalArity == 1 && head.numErasedFamilyArgs == 0 && head.noConfusion &&
            !isPropositionType(tpe) =>
        storedArgs match {
          case Vector(p: VPacked) if p.codec == NatCodec => Some(VPacked(NatCodec, p.payload + 1, tpe))
          case _                                         => None
        }
      case _ => None
    }

  private sealed trait NatOp
  private final case class ArithOp(run: (BigInt, BigInt) => Option[BigInt]) extends NatOp
  private final case class CmpOp(run: (BigInt, BigInt) => Boolean) extends NatOp

  private[raccoonlang] val MaxPowExponent: BigInt = BigInt(1) << 24

  // Derived rules (L7): each admitted op is extensionally the structural Prelude definition,
  // pinned by the differential tests. Conventions: `sub` truncates at zero; `pow(a, 0) = 1`.
  // Oversized closed pow requests are resource errors, not eager structural fallbacks.
  private val ops: Map[String, NatOp] = Map(
    "Nat.add" -> ArithOp((a, b) => Some(a + b)),
    "Nat.sub" -> ArithOp((a, b) => Some((a - b).max(0))),
    "Nat.mul" -> ArithOp((a, b) => Some(a * b)),
    "Nat.pow" -> ArithOp { (a, b) =>
      if (b > MaxPowExponent) throw NativeOperationLimitExceeded("Nat.pow", b, MaxPowExponent)
      Some(a.pow(b.toInt))
    },
    "Nat.beq" -> CmpOp(_ == _),
    "Nat.ble" -> CmpOp(_ <= _),
    "Nat.blt" -> CmpOp(_ < _)
  )

  /** Names whose meaning is trusted by the packed representation or native-op table. Checked
    * source may declare them only while a kernel-owned trusted bootstrap is being built (L8).
    */
  private[raccoonlang] val reservedNames: Set[String] =
    ops.keySet ++ Set(NatCodec.familyName, NatCodec.zeroName, NatCodec.succName)

  // Kill-switch for the differential tests: the structural definitions are the ops' spec.
  private val opsEnabled = new DynamicVariable[Boolean](true)
  private[raccoonlang] def withOpsDisabled[A](body: => A): A = opsEnabled.withValue(false)(body)

  /** Accelerated-op interception (called from Interpreter.evalApply before runLam): fires only
    * when the applied lambda has a reserved native name (authenticated by declaration loading,
    * L8), every argument is a packed Nat, and the instantiated codomain matches the op's result
    * shape. Every mismatch returns None — the op only ever shortcuts the structural body it is
    * extensionally equal to (L7).
    */
  private[raccoonlang] def runOp(
      lam: VLam,
      args: Vector[Value],
      resultTy0: () => Value
  ): Option[Value] = {
    if (!opsEnabled.value) return None
    val op = lam.id match {
      case ValueId.Const(name) => ops.getOrElse(name, return None)
      case _                   => return None
    }
    val (a, b) = args match {
      case Vector(x: VPacked, y: VPacked) if x.codec == NatCodec && y.codec == NatCodec =>
        (x.payload, y.payload)
      case _ => return None
    }
    op match {
      case ArithOp(run) =>
        run(a, b).flatMap { r =>
          val resultTy = resultTy0()
          if (ValueEquivalence.defEq(resultTy, args.head.tpe)) Some(VPacked(NatCodec, r, resultTy))
          else None
        }
      case CmpOp(run) =>
        val resultTy = resultTy0()
        boolCtor(lam, if (run(a, b)) "Bool.true" else "Bool.false", resultTy)
    }
  }

  private def boolCtor(lam: VLam, name: String, resultTy: Value): Option[Value] = {
    val env = lam.body match {
      case LamBody.Core(_, env)      => env
      case LamBody.Native(_, env, _) => env
    }
    env.globals.get(name).map(_.value(env)) match {
      case Some(h: ConstructorHead) if h.totalArity == 0 && ValueEquivalence.defEq(h.tpe, resultTy) =>
        Some(VCtor(h, Vector.empty, resultTy))
      case _ => None
    }
  }

  /** Constant-time lookup after bundled-Nat authentication. */
  private[raccoonlang] def natFamily(env: Env, span: Span): Value =
    env.globals
      .get(NatCodec.familyName)
      .map(_.value(env))
      .getOrElse(throw NatLiteralUnavailable("no `Nat` in scope", Some(span)))

  /** One-time trusted-bootstrap Nat validation (L8(a)). */
  private[raccoonlang] def validateNatFamily(env: Env): Unit = {
    def fail(reason: String): Nothing = throw NatLiteralUnavailable(reason)
    def global(name: String): Option[Value] = env.globals.get(name).map(_.value(env))

    val fam = global(NatCodec.familyName).getOrElse(fail("no `Nat` in scope"))
    fam match {
      case VConst(_, Inductive(meta), _)
          if meta.familyArity == 0 &&
            meta.constructorNames == Vector(NatCodec.zeroName, NatCodec.succName) =>
      case _ => fail("`Nat` in scope is not the two-constructor unary inductive")
    }
    if (!ValueEquivalence.defEq(fam.tpe, TypeTpe)) fail("`Nat` in scope is not Type-valued")
    global(NatCodec.zeroName) match {
      case Some(h: ConstructorHead)
          if h.totalArity == 0 && h.noConfusion && ValueEquivalence.defEq(h.tpe, fam) =>
      case _ => fail(s"`${NatCodec.zeroName}` is not a nullary `Nat` constructor")
    }
    global(NatCodec.succName) match {
      case Some(h: ConstructorHead) if h.totalArity == 1 && h.numErasedFamilyArgs == 0 && h.noConfusion =>
        h.tpe match {
          case pi: VPi if pi.binders.length == 1 =>
            val fieldTy = Interpreter.evalTerm(pi.binders.head.ty, pi.env)
            // The result-type check is redundant for genuinely installed inductives
            // (InvalidConstructorResult forces constructor results to the family), but this
            // function is the validation boundary — explicit, not clever.
            val outTy = pi.codomain(telescope.BinderOps.freshen(pi.binders, pi.env))
            if (!ValueEquivalence.defEq(fieldTy, fam) || !ValueEquivalence.defEq(outTy, fam))
              fail(s"`${NatCodec.succName}` is not `Nat -> Nat`")
          case _ => fail(s"`${NatCodec.succName}` is not `Nat -> Nat`")
        }
      case _ => fail(s"`${NatCodec.succName}` is not a unary `Nat` constructor")
    }
    ()
  }

  /** Evaluation of checked literal syntax: trusted (post-CoreAst), so only the family lookup. */
  private[raccoonlang] def evalNatLit(value: BigInt, env: Env): Value =
    VPacked(NatCodec, value, env(NatCodec.familyName))
}
```

### 3.3a `Prelude.scala`, `Interpreter.scala`, `Errors.scala` — reserve native Nat names

Historical first-slice shape. Full K3 replaced the boolean/capability sketch below with one sealed
`BootstrapAuthority` carried by `Prelude.Config`; `Interpreter.buildTrustedBootstrapEnv` derives
the permit and optional native profile from that single authority, making mismatched combinations
unrepresentable at the loader boundary. The public `evalDecl` path remains unprivileged.

Native-op dispatch is keyed by `ValueId.Const(name)`, so the declarations carrying those names
must be the bundled definitions whose equations the op table implements. Enforce that at the
single declaration-publication boundary; no runtime registry or per-value provenance is needed.

- Add an immutable `allowReservedNativeDefinitions` capability to `Prelude.Config`. Set it to
  `true` only for the bundled default Prelude resource. Set it to `false` for `Prelude.test`,
  `Prelude.none`, `fromPath`, and `fromSource`.
- Pass that capability only into `Interpreter.buildPreludeEnv`. Keep the public
  `Interpreter.evalDecl(decl, env)` path unprivileged; `Interpreter.run` and tests that call
  `evalDecl` directly therefore cannot publish reserved declarations.
- T1 generalizes this landed source-Prelude-only path with a distinct caller-authorized
  translated-`Init` bootstrap installer. Do not expose its permit through the general export API;
  a stream cannot grant itself authority through its module name or version header.
- Before evaluating a declaration, enumerate the canonical names it publishes (one for a const
  or axiom; the family plus constructor names for an inductive). If an unprivileged declaration
  intersects `Packed.reservedNames`, throw:

  ```scala
  final case class ReservedKernelName(name: String, span: Option[Span] = None) extends TypeError {
    override def msg: String = s"$name is reserved for the bundled kernel Prelude"
    override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  }
  ```

The capability authorizes only declaration publication while that one Prelude is built; it is
not stored in `Env`, so definitions checked later against the default Prelude cannot acquire a
reserved id. Adding a future accelerated op automatically reserves its name through
`ops.keySet`. After the privileged fold completes, `buildPreludeEnv` calls
`Packed.validateNatFamily(built)` before publishing the environment; unprivileged Prelude
configurations skip validation because they cannot declare the reserved family in the first
place.

### 3.4 `Interpreter.scala` — three seams + match decode

- `evalRef` (`:138`):
  ```scala
  case h: ConstructorHead if h.totalArity == 0 =>
    Value.collapseIfProof(Packed.foldCtor(h, Vector.empty, h.tpe).getOrElse(VCtor(h, Vector.empty, h.tpe)))
  ```
- `evalApply`, `ConstructorHead` branch (`:169-171`):
  ```scala
  case h: ConstructorHead =>
    val resultTy = pi.codomain(envWithArgs)
    val stored = Value.constructorStoredArgs(h, vArgs)
    Value.collapseIfProof(Packed.foldCtor(h, stored, resultTy).getOrElse(VCtor(h, stored, resultTy)))
  ```
- `evalApply`, `VLam` branch (`:160-161`) — op interception (the lazy `envWithArgs` is in scope):
  ```scala
  case lam: VLam =>
    Packed.runOp(lam, vArgs, () => pi.codomain(envWithArgs)).getOrElse(runLam(lam, vArgs))
  ```
  The `StructField` early-return at the top of `evalApply` stays first.
- `evalMatch` (`:289-308`) — refactor the extraction to names and add the packed case:
  ```scala
  val (ctorName, args) = scrut match {
    case VCtor(head, storedArgs, _) => (head.name, storedArgs)
    case p: VPacked                 => p.codec.decodeHead(p)
    case proof: VProof              => return evalProofMatch(m, proof, env)
    case other                      => /* existing stuck/blocked path unchanged */
  }
  val branch = m.cases.find(c => c.ctorName == ctorName).getOrElse(throw UnknownConstructor(ctorName, "", Some(m.span)))
  evalBranch(branch, args, env)
  ```
- `evalTerm` (`:274-283`): `case lit: ETerm.NatLit => Packed.evalNatLit(lit.value, env)`.

### 3.5 `ValueOps.scala` — materialize re-fold + compile-required case

The rebuild match in `Materialize.materialize` (`:22-46`) is exhaustive over `Value` — it needs a
`VPacked` case (in practice unreachable for the Nat codec, whose type is closed so
`mayNeedMaterialization` short-circuits; required for exhaustiveness and correct for future
codec types with parameters):

```scala
        case p: VPacked => VPacked(p.codec, p.payload, materialize(p.tpe))
```

Replace the `VApp` rebuild (`:28-29`):

```scala
        case VApp(head, args, tpe, blockerId) =>
          val mHead = materialize(head)
          val mArgs = args.map(materialize(_))
          val mTpe = materialize(tpe)
          (mHead, blockerId) match {
            // Canonicity is an invariant, not a birth-only courtesy: substituting solved metas can
            // produce a ground constructor form (`succ ?x` with `?x := ⟨4⟩`), which re-folds.
            case (h: ConstructorHead, None) =>
              Packed.foldCtor(h, mArgs, mTpe).getOrElse(VApp(mHead, mArgs, mTpe, blockerId))
            case _ => VApp(mHead, mArgs, mTpe, blockerId)
          }
```

### 3.5a `InductiveChecks.scala` — positivity traversals (compile-required)

All three occurrence traversals are exhaustive matches over `Value` and stop compiling when
`VPacked` lands. The payload contains no `Value`s (L2), so the type is the only occurrence
surface:

- `doesNotOccur` (`:52`): `case p: VPacked => doesNotOccur(target, p.tpe)`
- `occursPositively` (`:86`): `case p: VPacked => doesNotOccur(target, p.tpe)` — strict, like
  the `VProof` arm: a value's *type* is not a positive position. For the Nat codec the type is
  closed, so strictness costs nothing today.
- `sameFamilyArgsDoNotContain` (`:124`):
  `case p: VPacked => sameFamilyArgsDoNotContain(inductiveName, target, p.tpe)`

### 3.6 `ValueEquivalence.scala` — defEq arms + unify arms

In `defEqStructural` (before the `VApp` case, `:123`):

```scala
        case (p1: VPacked, p2: VPacked) =>
          p1.codec == p2.codec && p1.payload == p2.payload && defEq(p1.tpe, p2.tpe)
        case (p: VPacked, VCtor(h, fields, ctorTpe)) => defEqPeeled(p, h, fields, ctorTpe)
        case (VCtor(h, fields, ctorTpe), p: VPacked) => defEqPeeled(p, h, fields, ctorTpe)
```

```scala
    // One decoded constructor layer against a concrete constructor form. For canonical codecs this
    // is only reachable against ctors-over-neutrals (no ground ctor form exists); kept general for
    // the staged non-canonical codecs.
    private def defEqPeeled(p: VPacked, h: ConstructorHead, fields: Vector[Value], ctorTpe: Value): Boolean = {
      val (name, decoded) = p.codec.decodeHead(p)
      name == h.name && decoded.length == fields.length &&
      decoded.zip(fields).forall { case (a, b) => defEq(a, b) } && defEq(p.tpe, ctorTpe)
    }
```

In `Unify.tryUnify`, insert directly after the `VCtor ≠ VCtor` clash arm (`:355-357`):

```scala
        // K3 packed literals (docs/native-literals.md §6). Apartness requires BOTH explicit
        // payload inequality and the codec's L9 claim: unequal payloads decode to a no-confusion
        // constructor clash at finite depth, so the shortcut is the transitive closure of
        // derivable steps. It is NOT gated on canonicity or L3; definitional inequality is not
        // propositional apartness under the planned axioms (funext). Equal payloads can reach here
        // when their annotated types did not compare equal, so handle that type equation normally.
        case (p1: VPacked, p2: VPacked) if p1.codec == p2.codec =>
          if (p1.payload == p2.payload) tryUnify(p1.tpe, p2.tpe, meta, ctx)
          else if (p1.codec.refutesUnequalPayloads) apart(p1, p2)
          else stuck(p1, p2) // Conservative for codecs without L9; spec §11.

        // Peel one decoded layer and let the ordinary VCtor/VApp machinery run (links under
        // constructor frames are consequences as usual). Required for match refinement over
        // literal indices: `succ ?x ~ 5` must solve `?x := 4`.
        case (p: VPacked, other @ VCtor(h, _, _)) => unifyPeeled(p, h, other, meta, ctx, packedOnLeft = true)
        case (other @ VCtor(h, _, _), p: VPacked) => unifyPeeled(p, h, other, meta, ctx, packedOnLeft = false)
```

```scala
    private def unifyPeeled(
        p: VPacked,
        h: ConstructorHead,
        ctor: Value,
        meta: EqStore,
        ctx: Ctx,
        packedOnLeft: Boolean
    ): Result = {
      val (name, decoded) = p.codec.decodeHead(p)
      if (name != h.name) {
        // Mirrors the VCtor clash arm: the codec side's constructors carry no-confusion by the
        // trusted-bootstrap validation; refutation additionally needs it on the concrete head.
        if (h.noConfusion) apart(p, ctor) else stuck(p, ctor)
      } else if (decoded.length != h.totalArity - h.numErasedFamilyArgs) stuck(p, ctor)
      else {
        val peeled = VCtor(h, decoded, p.tpe)
        if (packedOnLeft) tryUnify(peeled, ctor, meta, ctx) else tryUnify(ctor, peeled, meta, ctx)
      }
    }
```

Notes: recursion terminates (each peel strips one concrete constructor layer; ctor spines are
finite syntax). Packed-vs-`Var` needs nothing — the existing Var-linking arms handle it.
Packed-vs-neutral falls to the final `stuck` — correct, never apart.

### 3.7 `TerminationChecker.scala` — packed subterm

In `isStrictSubterm` (`:91-99`) add a root arm:

```scala
      case root: VPacked =>
        candidate match {
          // Direct payload order (L6) — never decode-recurse: peeling a 10^9 literal is a hang.
          case c: VPacked if c.codec == root.codec => root.codec.strictlyLess(c, root)
          case _                                   => false
        }
```

(`applicationOfSubterm` untouched: packed fields under `VCtor` roots are covered by its `defEq`.)

### 3.8 `MatchChecker.scala` — ground packed scrutinee

In `computeReachableCtors`, preserve canonicality for the nullary ground candidate used to refine
branches:

```scala
val ctorValue = Value.collapseIfProof(
  Packed.foldCtor(h, storedArgs, resultTy).getOrElse(VCtor(h, storedArgs, resultTy))
)
```

`Nat.succ` still declines because its field is fresh rather than packed.

In `checkMatch`'s scrutinee match (`:198`), add alongside the `VCtor` arm:

```scala
      case p: VPacked =>
        // A packed scrutinee is a ground constructor value: same single-case discipline as VCtor.
        val (ctorName, decodedArgs) = p.codec.decodeHead(p)
        cases.find(_.ctorName != ctorName).foreach { c =>
          throw UnreachableCase(c.ctorName, Some(c.span))
        }
        val br = cases.find(_.ctorName == ctorName).getOrElse(throw MissingCase(ctorName))
        checkedByCtor += ctorName -> checkBranch(br, decodedArgs, env, motiveTy)
```

### 3.9 `telescope/Projection.scala` — CtorField step

In `project`'s `Step.CtorField` case (`:251-255`):

```scala
          case Step.CtorField(ctor, idx) =>
            v match {
              case VCtor(h, stored, _) if h.name == ctor && idx < stored.length => Right(stored(idx))
              case p: VPacked =>
                val (name, decoded) = p.codec.decodeHead(p)
                if (name == ctor && idx < decoded.length) Right(decoded(idx))
                else Left(s"expected a $ctor value, got $p")
              case other => Left(s"expected a $ctor value, got $other")
            }
```

### 3.10 Syntax pipeline

- **`SurfaceAst.scala`**: `final case class NatLit(value: BigInt, span: Span) extends Term` in
  `object Term`.
- **`LanguageParser.scala`**: follow the `identAtom`/`identTerm` pattern:
  ```scala
  private val natLitAtom: Parser[BigInt] =
    (P(c => c.isDigit) ~ P(c => c.isDigit).rep(0)).!.map(BigInt(_))

  private def natLitTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    natLitAtom.flatSpanned(sourceId).map(NatLit.tupled)
  ```
  Append `| natLitTerm` to **both** `termAtom` (`:79-80`) and `typeAtom` (`:92-96`) — literals
  occur in type argument positions (`Vec(A, 3)`). No keyword/ident conflict: idents must start
  with a letter.
- **`Elaborator.scala`**: `elabTerm` (`:568`) gets `case SA.Term.NatLit(v, sp) => CA.Term.NatLit(v, sp)`.
  (`rewriteFieldType` has a catch-all default at `:420` — no change needed.)
- **`CoreAst.scala`** and **`ElabAst.scala`**: `final case class NatLit(value: BigInt, span: Span)
  extends Term` in each `object Term`. Leaf node — no `AstNodeId` (its value's key is
  payload-derived, no identity involved).
- **`TypeChecker.scala`**, `check` (`:400`):
  ```scala
        case CA.Term.NatLit(value, span) =>
          val fam = Packed.natFamily(env, span)
          val synthed = CheckedTerm(VPacked(NatCodec, value, fam), EA.Term.NatLit(value, span))
          expectedTy.fold(synthed)(expected => checkTermFits(synthed, expected))
  ```
- **`CapturedRefs.scala`**, `goTerm` (`:31`): `case _: Term.NatLit => refs` (the implicit `Nat`
  global needs no capture — `closeForEval` keeps globals).
- **`ValueQuote.scala`**: in `quoteTerm`'s value match add
  ```scala
      case p: VPacked =>
        p.codec match {
          case NatCodec => ElabAst.Term.NatLit(p.payload, span)
        }
  ```
  (never quote to a constructor spine — a 10⁶ literal must not become a 10⁶-deep term), and in
  `ClosedEnvInliner.inlineTerm` add `case lit: ElabAst.Term.NatLit => lit`.
- **`PrettyPrinter.scala`**: `NatLit → value.toString` in the CoreAst atom + term printers
  (`:55-61`, `:65-76`) and the ElabAst pair (`:131-136`, `:140-149`); in the `Value` printer add
  `case p: Value.VPacked => p.payload.toString` (historical first-slice case; full K3 replaced it
  with the exhaustive payload-specific printers in §0.2/§0.4).
- **`Errors.scala`**:
  ```scala
  final case class NatLiteralUnavailable(reason: String, span: Option[Span] = None) extends TypeError {
    override def msg: String = s"Nat literal unavailable: $reason"
    override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  }

  final case class NativeOperationLimitExceeded(
      operation: String,
      argument: BigInt,
      limit: BigInt,
      span: Option[Span] = None
  ) extends TypeError {
    override def msg: String = s"$operation argument $argument exceeds native evaluation limit $limit"
    override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  }
  ```
  (match the surrounding classes' exact style — the trait requires `msg` and `withSpan`).

### 3.11 `src/main/resources/Init/Prelude.rac` — pow and blt

Inside `namespace Nat { … }` (after `mul`/`ble`, before `le`), matching the house style of full
canonical names:

```
  def pow (a: Nat)(b: Nat): Nat decreases structural(b) := {
    match b returning Nat with
    | Nat.zero => Nat.succ(Nat.zero)
    | Nat.succ p => Nat.mul(Nat.pow(a, p), a)
  }

  def blt (a: Nat)(b: Nat): Bool := Nat.ble(Nat.succ(a), b)
```

### 3.12 Docs (at the first-slice landing)

- `docs/mathlib-export-port.md`: the first slice flipped the K3 gate cell to **done** for the Nat
  base and left String/div-class work staged; §0 now specifies that continuation.
- `docs/native-literals.md` §9 ledger obligations: apply them — kernel-theory §2 defeq-component
  bullet, §5 rows (payload apartness, packed structural decrease), and the reserved-name
  authentication rule for native ops. Follow the K4 precedent for wording.

## 4. Behavioral notes and traps

1. **`-Xfatal-warnings` is the todo list**: after 3.1 lands, every non-exhaustive `Value` match
   and every new `Term` node surfaces as a fatal warning. The known exhaustive matches (verified
   against the current tree) are `ValueKey.orderKey` (3.2), `ValueOps.materialize` (3.5), the
   three `InductiveChecks` traversals (3.5a), and `PrettyPrinter.print` (3.10) — plus every
   `Term` walker once the `NatLit` nodes land. For matches with existing defaults that the
   compiler does *not* flag, the audited-safe list is: `collapseIfProof` (non-prop arm),
   `StructEta.expandIfStruct` (default; Nat not eta-eligible), `Blocker`/`Blocked` extractors,
   `Projection.compile.visit` (packed values contain no holes), `Interpreter.valueName`,
   `defEqStructural`/`tryUnify` defaults (covered by the new arms), and
   `TerminationChecker.isStrictSubterm`'s `case _ => false`.
2. **Ops fire during trusted-bootstrap declaration checking too** (eager normalization evaluates
   bodies) — that's intended; while checking `Nat.add` itself its args are fresh Vars, so no
   self-interception. Reserved-name enforcement prevents any later/custom declaration from
   reaching this path with a different body.
3. **The differential path must stay green**: with ops disabled, `add(2, 3)` runs the structural
   body — the match decodes packed `3`, the branch rebuilds `succ`-of-packed which *re-folds* —
   so both paths produce `VPacked(5)` and compare by key.
4. **`VApp`'s `require`**: never construct the peeled `VCtor` before the stored-arity guard.
5. **`BigInt == Int`** comparisons (`payload == 0`) are fine in Scala; keep payload arithmetic in
   `BigInt`.
6. **Do not touch** `BinderOps.freshCtorArgsAndResult` or StructEta. MatchChecker's fresh-copy
   construction folds only its nullary `Nat.zero` candidate; fresh-field candidates remain
   structural by design.
7. Literal-scrutinee matches now follow the ground-value discipline (§3.8): `match 5 with`
   requires exactly the `succ` case; a `zero` case is an `UnreachableCase` error. This mirrors
   existing behavior for `match Nat.zero with …` — it is not a regression.

## 5. Existing-test fallout policy

Running the suite after phase C will break assertions that pin the *unary representation* of
ground Nats. Find them with:

```
grep -rn '"Nat\.succ\|"Nat\.zero"' src/test/scala/com/raccoonlang/
```

Known: `PreludeTests` ("Prelude Bool and Nat APIs reduce" asserts
`"Nat.succ(Nat.succ(Nat.zero))"` prints; several `ctorName(res) == "Nat.zero"` on Nat-valued
results — `ctorName` will now see `VPacked` and fail). Others likely in `InterpreterTests`,
`TerminationTests`, `ValueQuoteTests`, `PrettyPrinterTests`, `MatchRefinementTests`.

Policy: these are implementation-worldview assertions — update them to the packed canonical form
(`PrettyPrinter.print(res) == "2"`, or payload assertions on `VPacked`). **Exception:** the
logical probes in `ConsistencyTests` (and the consistency-genre tests in `QuotientTests`) must
not be weakened (kernel-theory §8). A mechanical `Nat` → `Peano` fixture rename solely to satisfy
the reserved-name rule is allowed, but the expected accept/reject result and derivation must stay
identical. Constructor-clash apartness survives via the peel/apartness arms (`VPacked(0)` vs
`succ x` decodes to a genuine zero/succ clash). A red result after any required rename means the
change is unsound: stop and re-derive, don't weaken the test.

Reserved-name enforcement has a separate, broad test fallout: many suites use `Prelude.test`
(which intentionally contains no Nat) and declare a local fixture named `Nat`; namespace tests
also declare their own `Nat.add`. Those declarations must no longer use reserved names. Prefer
renaming isolated fixtures to `Peano` (including constructors and qualified operations); where a
test is specifically about the real Nat API, switch it to `Prelude.default` and remove the local
copy. Do not grant the minimal test Prelude or ordinary test declarations the reserved-name
capability merely to preserve old fixtures — that would reopen the native-op identity hole.

## 6. New suite: `NativeLiteralTests.scala`

Follow `PreludeTests`' harness (`LanguageParser.parseProgram` → `Elaborator.elab` →
`Interpreter.run`, with `typecheckDecls`/`runProgram` helpers). Add a `payload` helper
(`case p: VPacked => p.payload`). Before writing the refinement pins, check the Prelude's exact
`Eq`/`Eq.refl` signatures and crib from `MatchRefinementTests`/`ConsistencyTests` phrasing.

1. **Literal forms**: `{ 5 }` → payload 5, prints `"5"`; `{ Nat.zero }` → payload 0;
   `{ Nat.succ(41) }` → payload 42 (fold); `def x : Nat := 5` typechecks.
2. **defEq across forms**: `def p : Eq(Nat, 5, Nat.succ(4)) := Eq.refl(5)` typechecks;
   `def q : Eq(Nat, Nat.succ(Nat.succ(Nat.zero)), 2) := Eq.refl(2)` typechecks.
3. **Transparency + perf pin**: `{ Nat.pred(1000000) }` → payload 999999 (must be instant —
   one decode, not 10⁶).
4. **Ops**: `{ Nat.add(2, 3) }` → 5; `{ Nat.sub(3, 5) }` → 0 (truncation);
   `{ Nat.pow(2, 10) }` → 1024; `{ Nat.pow(7, 0) }` → 1; `beq/ble/blt` on
   (0,0), (0,1), (1,0), (5,5) → the right `Bool` constructors. At the resource boundary,
   `Nat.pow(1, 2²⁴)` → 1 and `Nat.pow(1, 2²⁴ + 1)` raises
   `NativeOperationLimitExceeded` without structural fallback.
5. **Differential certification (structural tier)**: for each op, run the same program normally
   and inside `Packed.withOpsDisabled { … }`; assert equal payloads / the same Bool constructor.
   Size operands to the structural path's O(magnitude) cost, which compounds through nested
   recursion: `beq`/`ble`/`blt`/`add`/`sub` over pairs in 0..12, `mul` over pairs in 0..6, `pow`
   over pairs in 0..3 — plus boundary cases (equal args, near-equal, `sub` underflow, `pow` zero
   exponent). Do **not** push large operands through the structural path; that tier exists to
   pin L7's extensional-equality obligation on feasible inputs.
6. **Op-path oracle checks**: large random operands (e.g. ten pairs up to 2¹²⁸) through the
   normal accelerated pipeline, asserting payloads against host-`BigInt` expectations computed
   in the test — e.g. `{ Nat.mul(Nat.pow(2, 64), Nat.pow(2, 64)) }` → `BigInt(2).pow(128)`.
   This tier guards wiring and conventions, not the arithmetic itself (the op *is* host
   arithmetic); the perf pins (items 3 and 11's timing expectations) are separate tests.
7. **Refinement pin** (the peel+link rule): a match on `h: Eq(Nat, Nat.succ(n), 5)` whose refl
   branch must check with `n` refined to `4` (e.g. goal `Eq(Nat, n, 4)` proved by `Eq.refl`).
8. **Apartness pin**: `(h: Eq(Nat, 3, 5)) -> False` provable by an empty (refl-pruned) match.
9. **Stuck pin**: with `opaque def k : Nat := 5`, a match on `Eq(Nat, k, 5)` must still require
   the refl case (packed vs neutral is stuck, never apart).
10. **Ground-scrutinee discipline**: `match 3 returning Nat with | Nat.succ p => p` typechecks
    (→ 2); adding a `Nat.zero` case is an `UnreachableCase` error.
11. **Termination**: two-level `fib` with `decreases structural(n)` typechecks; `{ fib(20) }` →
    6765.
12. **Residual round-trip**: `def addFive : (n: Nat) -> Nat := fun (n: Nat): Nat => Nat.add(n, 5)`
    then `{ addFive(2) }` → 7 (literal survives quote/re-eval inside the lambda body).
13. **Reserved identity**: under `Prelude.none`, `Prelude.test`, and a path-provided custom
    Prelude, attempts to declare `Nat`, `Nat.zero`/`Nat.succ`, or an accelerated name such as
    `Nat.add` fail with `ReservedKernelName`. The bundled default Prelude loads successfully and
    its `Nat.add` still takes the native path. T1 must add a parallel pin: the exact same identity is
    accepted through the caller-authorized pinned translated-`Init` bootstrap and rejected through
    ordinary import mode.

## 7. First-slice acceptance checklist

- [x] `sbt compile` clean (fatal warnings resolved deliberately, not defaulted away).
- [x] Full `sbt test` green; `ConsistencyTests`/`QuotientTests` logical probes are not weakened
      (mechanical reserved-name fixture renames only).
- [x] `NativeLiteralTests` green, including the differential pass and the perf pins.
- [x] Docs updated per 3.12.
- [x] No new mutable global state except the `DynamicVariable` kill-switch; no `ConstructorHead`
      shape change; codec set sealed with no public constructor.
- [x] Reserved Nat family/constructor/op names can be published only under a sealed native
      `BootstrapAuthority`; the derived permit/profile is immutable and is not retained in `Env`.
      T1 receives the pinned authority only through its caller-selected trusted-bootstrap entry
      point, while ordinary import mode remains unprivileged.
- [x] Payload apartness in unification requires explicit payload inequality and
      `refutesUnequalPayloads` (L9), never `canonical` or L3 alone.
- [x] `foldCtor` declines propositional result types and no-confusion-less heads.
