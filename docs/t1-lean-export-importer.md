# T1: Lean Export Importer and Translated Prelude

Status: **implementation specification, draft for review** (2026-07-16). Companion to
mathlib-export-port.md, kernel-theory.md, wf-recursion.md, native-literals.md, and
k6-mutual-nested-inductives.md.

Authoritative producer references: the
[lean4export 3.1.0 wire format](https://github.com/leanprover/lean4export/blob/master/format_ndjson.md),
the [exporter implementation](https://github.com/leanprover/lean4export/blob/master/Export.lean),
and the pinned
[Lean declaration model](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Declaration.lean).

## 1. Outcome

T1 turns a pinned lean4export 3.1.0 NDJSON stream into a checked Raccoon environment. It replaces
the benchmark's ordinary Raccoon Prelude with a translated Lean Init environment, retaining only
the small kernel-owned bootstrap needed to express and check that environment.

The importer is not a second elaborator. It consumes closed, fully elaborated kernel terms,
mechanically lowers them to CoreAst, and submits every declaration to the ordinary Raccoon
checker. The successful result is:

~~~scala
final case class LeanImportResult(
    env: Env,
    manifest: LeanImportManifest,
    metrics: LeanImportMetrics
)
~~~

The initial result is in-memory and benchmark-oriented. Serializing or linking a reusable frozen
environment artifact is follow-up work after M1; T1 does not print a giant translated Raccoon
source program.

The first benchmark target is the complete kernel-safe portion of the pinned Init export. T1 is
complete when that stream can be read, translated, checked in order, and reported without loading
Raccoon's source Prelude. Every use of name-based kernel trust must be explicit and ledgered: K3's
exact native Nat identities and exact `Char.ofNat` String-literal identity in the trusted
translated-`Init` bootstrap are the deliberate Lean-compatible exceptions; ordinary declarations
and the other primitive clusters never gain authority from a familiar name alone.

T1 owns:

- the semantic export IR and streaming reader;
- the injective Lean-name encoding;
- universe, term, and ordinary-declaration lowering;
- the full-source-application to Raccoon-calling-convention adapter;
- the minimal translated-Prelude bootstrap and authenticated primitive dispatch;
- atomic declaration staging, diagnostics, manifests, and benchmark instrumentation;
- lossless handoff records for inductive blocks, exported recursors, and the K2/T3 cluster.

T1 does not own:

- mutual/nested inductive checking or logical-block construction (K6);
- ordinary recursor synthesis and exported-rule validation (T2);
- sealed accessibility semantics, which are already implemented by K2;
- the Acc/WellFounded wrapper transaction (T3);
- the kernel-side native Nat operations and String representation, which are already implemented
  by K3; T1 owns only their checked translated-`Init` activation and manifest integration;
- the propext/choice evidence-grade changes (K7);
- post-check defeq repair (T4).

Those workstreams expose narrow adapters to T1. Until an adapter is available, the importer must
fail at the first declaration that requires it with a typed unsupported-feature diagnostic. It
must not substitute an axiom, omit a safe declaration, or weaken a shape check to continue.

## 2. Fixed decisions

The following are decisions, not implementation options:

1. **Translated Init is the benchmark prelude.** A benchmark import starts from the minimal
   kernel bootstrap in §5, not from Prelude.default. Lean's Eq, Nat, Bool, Quot, and the rest of
   Init are installed from the export.
2. **The producer is pinned.** The accepted target is lean4export 3.1.0 tag `v4.30.0` built against
   Lean 4.30.0 at commit d024af099ca4bf2c86f649261ebf59565dc8c622. Another producer version is a
   hard error until its schema and declaration shapes have been reviewed.
3. **Safe declarations are checked.** The importer has no “already checked by Lean” publication
   path. Source bodies for definitions, opaque declarations, and theorems are checked once before
   their ordinary Raccoon representation is published.
4. **Unsafe code is not axiomatized.** Unsafe and partial declarations are recorded and skipped.
   Any kernel-safe declaration whose type or value refers to a skipped declaration is a hard
   error.
5. **Names are not semantic authority, except for the explicit K3 bootstrap identities.** Ordinary
   names select ordinary dependencies. Eq, Quot, Acc, and other primitive clusters require their
   structural validators. Following Lean's kernel trust model, the exact K3 native-operation names
   may select their trusted defeq rules, and the exact `Char.ofNat` identity may support packed
   String decoding, only while the dedicated pinned translated-`Init` bootstrap mode is active and
   after the Nat/Bool/String representation shapes and operation types have checked. The Nat table
   is Lean's fourteen pinned binary identities plus the explicitly ledgered Raccoon extension
   `Nat.blt`. Ordinary import mode has no such authority.
6. **Every exported argument is accounted for.** The export supplies universe and term
   implicits explicitly. T1 either emits an argument required by Raccoon's checked calling
   convention or checks that Raccoon's reconstruction is definitionally equal to the supplied
   value. It never discards an argument unchecked.
7. **Core saturation is preserved.** Raccoon applications saturate one complete Pi telescope.
   Lean underapplications are eta-expanded mechanically; they are not represented as malformed
   Core App nodes.
8. **Input order is retained.** Ordinary declarations are processed in export order. An
   inductive object, quotient package, or T3 wrapper cluster may stage several declarations
   atomically, but successful publication retains their producer order.
9. **The import is all-or-error for kernel-safe content.** T1 does not perform general
   reachability pruning. The only filtering is the producer's unsafe/partial boundary.
10. **M0 and T1 share one parser.** LeanExportM0 becomes a statistics consumer of the reader and
    IR defined here; it must not remain a second interpretation of the wire format.

## 3. Trust boundary

An ordinary NDJSON file is untrusted input. Array positions, redundant metadata, declaration
names, universe order, binder annotations, recursor rules, safety flags, and source order are
claims to validate, not facts to assume. The pinned translated-`Init` input is additionally opened
through a distinct trusted-bootstrap entry point. As in Lean's own bootstrap, that authority makes
the agreement between the exact reserved K3 operation definitions and the kernel's native
arithmetic table, plus the exact `Char.ofNat` definition and String-literal scalar mapping, part of
the TCB; it does not waive ordinary typechecking or any structural check outside those narrow
agreement assumptions. A general stream cannot obtain bootstrap authority by claiming the right
module name, producer version, or declarations.

The importer may rely on:

- the selected format grammar after the meta object matches the exact supported version;
- successful JSON decoding with explicit bounds checks;
- ordinary Raccoon type checking and definitional equality;
- kernel-owned primitive validators and their unforgeable capability objects;
- the pinned producer's documented meanings only where T1 also checks every locally redundant
  fact available in the stream;
- in trusted translated-`Init` mode only, the exact K3 native-operation table and `Char.ofNat`
  scalar-mapping assumption documented in `native-literals.md`; agreement with the checked bodies
  is trusted outright rather than inferred from their names or proved by a body recognizer.

The importer may not rely on:

- a declaration being safe because its name is familiar, outside the explicit trusted-bootstrap
  K3 identities;
- an inductive being Eq, Nat, Acc, or Quot solely from its name;
- exported isRec, numParams, numIndices, or recursor rule arrays without recomputation;
- a theorem body being irrelevant as a reason not to check it;
- an exported implicit argument being equal to the one Raccoon would infer;
- an all array as permission to resolve a missing global;
- a successful “has type Prop” check as authentication of equality.

Ordinary exported axioms remain assumptions of the imported object theory, just as source
AxiomDecl values are assumptions. They are listed in the manifest with their checked types.
Kernel-owned behavior is a different category: attaching evaluator behavior, proof-constructor
recipes, a sealed primitive equation, or a native codec requires a structural capability. K3
native arithmetic and String scalar construction are the narrow exceptions: their representation
families validate structurally, while exact operation equations and the `Char.ofNat` scalar mapping
are admitted by trusted-bootstrap identity, mirroring Lean, and recorded as such in the manifest
and kernel ledger.

## 4. Pipeline

~~~text
NDJSON bytes
    |
    v
version gate + intern-table reader
    |
    v
compact semantic export IR
    |
    +--> M0 statistics consumer
    |
    v
safety filter + name/provenance registry
    |
    v
type-directed term/declaration lowerer
    |
    +--> K6/T2 inductive-block adapter
    +--> quotient validator/installer
    +--> K2/T3 WF adapter
    +--> K3 native literal/name adapters
    |
    v
ordinary checker in a temporary immutable Env
    |
    v
atomic publication + manifest + timing record
~~~

The reader is streaming at the declaration-object level. Names, levels, and expression nodes stay
in compact indexed stores because later declarations refer to earlier interned nodes. A simple
declaration is lowered and checked as soon as its object is read. Its temporary recursive term
memo and JSON object are then released. An inductive export object stays intact until its whole
block transaction succeeds.

No phase constructs one recursive Scala tree for the entire export, and no phase accumulates all
lowered Core declarations in a Program before checking.

## 5. Minimal bootstrap and translated-Prelude mode

### 5.1 Bootstrap contents

LeanImportBootstrap starts from the same irreducible meta-level base currently created by
`Interpreter.buildTrustedBootstrapEnv`:

~~~text
Type
Level
Level.zero
Level.one
Prop
~~~

It then installs only the checked builtin constants needed to express arbitrary exported
universes:

~~~text
Sort
Level.succ
Level.max
Level.imax
~~~

Their types are built by kernel-owned code and checked through the ordinary declaration path.
Their identities are reserved. The bootstrap installer receives a permit containing exactly
those four names; no importer-wide builtin permit exists.

The bootstrap does not contain Eq, Nat, Bool, Unit, Empty, Nonempty, Quot, Acc, WellFounded, or
any user-facing theorem. Those arrive from the export.

### 5.2 Quotient staging

Quot.mk, Quot.lift, and Quot.ind are evaluator builtins, but they are not installed during the
initial bootstrap because their types depend on the translated equality and quotient families.
T1 introduces a QuotientPrimitives validator analogous to WfPrimitives:

1. aggregate the four declaration objects in kind order type, ctor, lift, ind;
2. require the canonical producer ownership and order;
3. check the translated Quot family and all exported types ordinarily;
4. consume a ValidatedEquality capability rather than resolving Eq by spelling;
5. derive the expected mk/lift/ind types mechanically and compare them to the checked exports;
6. install the three builtins with a permit containing exactly their reserved names;
7. publish the immutable environment only after the whole package succeeds.

The wire format emits those as four quotient declaration objects, with interned primitive objects
possibly appearing between them while each type is dumped. A pending quotient-package state may
consume those primitives but no unrelated declaration. An interruption, duplicate kind, wrong
order, or end of stream before ind fails the package and publishes none of it.

Quot.sound is an ordinary exported axiom after its type checks. It receives no evaluator behavior.
The exact quotient type templates and trust-ledger rows belong beside the implementation in
kernel-theory.md; the validator must land before a complete translated Init import is accepted.

### 5.3 Bootstrap API

Add a distinct entry point rather than overloading Prelude.none:

~~~scala
object LeanImportBootstrap {
  def build(): Either[Vector[Diagnostic], Env]
}
~~~

Prelude.default remains the source-language Prelude. Tests must prove that the translated import
does not accidentally consult it by installing a conflicting sentinel under a familiar Prelude
name and observing no effect.

## 6. Semantic export IR

The IR mirrors format 3.1.0 semantically while avoiding JSON-library types and recursive expansion.
Names, levels, and expressions use contiguous Int IDs. Every lookup checks non-negativity,
existence, and “defined earlier” ordering.

Name ID 0 is the pre-seeded anonymous name and Level ID 0 is the pre-seeded zero level; neither
has a wire object. Expression IDs begin with the first expression object at 0. Numeric name
components are non-negative arbitrary-precision values even though store offsets are bounded Ints.

~~~scala
object LeanExportIr {
  final case class NameId(value: Int) extends AnyVal
  final case class LevelId(value: Int) extends AnyVal
  final case class ExprId(value: Int) extends AnyVal

  sealed trait NameNode
  final case class NameStr(prefix: NameId, value: String) extends NameNode
  final case class NameNum(prefix: NameId, value: BigInt) extends NameNode

  sealed trait LevelNode
  case object LevelZero extends LevelNode
  final case class LevelSucc(of: LevelId) extends LevelNode
  final case class LevelMax(left: LevelId, right: LevelId) extends LevelNode
  final case class LevelIMax(left: LevelId, right: LevelId) extends LevelNode
  final case class LevelParam(name: NameId) extends LevelNode

  sealed trait BinderInfo
  case object Default extends BinderInfo
  case object Implicit extends BinderInfo
  case object StrictImplicit extends BinderInfo
  case object InstImplicit extends BinderInfo

  sealed trait ExprNode
  final case class BVar(index: Int) extends ExprNode
  final case class Sort(level: LevelId) extends ExprNode
  final case class Const(name: NameId, levels: Vector[LevelId]) extends ExprNode
  final case class App(fn: ExprId, arg: ExprId) extends ExprNode
  final case class Lam(
      name: NameId,
      binderType: ExprId,
      body: ExprId,
      binderInfo: BinderInfo
  ) extends ExprNode
  final case class ForallE(
      name: NameId,
      binderType: ExprId,
      body: ExprId,
      binderInfo: BinderInfo
  ) extends ExprNode
  final case class LetE(
      name: NameId,
      binderType: ExprId,
      value: ExprId,
      body: ExprId,
      nonDependent: Boolean
  ) extends ExprNode
  final case class Proj(typeName: NameId, fieldIndex: Int, struct: ExprId)
      extends ExprNode
  final case class NatVal(value: BigInt) extends ExprNode
  final case class StrVal(scalars: Vector[Int]) extends ExprNode
  final case class MData(expr: ExprId) extends ExprNode
}
~~~

The implementation may use tagged primitive arrays and side tables instead of allocating these
case classes. The public cursor presents the cases above. MData's JSON metadata object is consumed
without interpreting its producer-specific entries and is not retained; only its semantically
relevant child expression and provenance remain.

Declaration objects retain every format field:

- axiom: name, universe parameters, type, unsafe flag;
- def: name, universe parameters, type, value, reducibility hint, safety, all;
- opaque: name, universe parameters, type, value, unsafe flag, all;
- theorem: name, universe parameters, type, value, all;
- quotient object: its declared kind, name, universe parameters, and type;
- inductive object: its arrays of family, constructor, and recursor records;
- family record: name, universe parameters, type, numParams, numIndices, all, ctors, numNested,
  isRec, isUnsafe, and isReflexive;
- constructor record: name, universe parameters, type, induct, cidx, numParams, numFields, and
  isUnsafe;
- recursor record: name, universe parameters, type, all, numParams, numIndices, numMotives,
  numMinors, rules, k, and isUnsafe;
- recursor rule: ctor, nfields, and rhs;
- def hints: abbrev, regular with height, and opaque;
- safety: safe, unsafe, and partial.

The cursor-level declaration model is:

~~~scala
sealed trait ExportDecl {
  def provenance: ExportProvenance
}

final case class ExportAxiom(
    name: NameId,
    levelParams: Vector[NameId],
    tpe: ExprId,
    isUnsafe: Boolean,
    provenance: ExportProvenance
) extends ExportDecl

sealed trait ExportDefHint
case object HintOpaque extends ExportDefHint
case object HintAbbrev extends ExportDefHint
final case class HintRegular(height: BigInt) extends ExportDefHint

sealed trait ExportSafety
case object Safe extends ExportSafety
case object Unsafe extends ExportSafety
case object Partial extends ExportSafety

final case class ExportDef(
    name: NameId,
    levelParams: Vector[NameId],
    tpe: ExprId,
    value: ExprId,
    hint: ExportDefHint,
    safety: ExportSafety,
    all: Vector[NameId],
    provenance: ExportProvenance
) extends ExportDecl

final case class ExportOpaque(
    name: NameId,
    levelParams: Vector[NameId],
    tpe: ExprId,
    value: ExprId,
    isUnsafe: Boolean,
    all: Vector[NameId],
    provenance: ExportProvenance
) extends ExportDecl

final case class ExportTheorem(
    name: NameId,
    levelParams: Vector[NameId],
    tpe: ExprId,
    value: ExprId,
    all: Vector[NameId],
    provenance: ExportProvenance
) extends ExportDecl

sealed trait ExportQuotKind
case object QuotType extends ExportQuotKind
case object QuotCtor extends ExportQuotKind
case object QuotLift extends ExportQuotKind
case object QuotInd extends ExportQuotKind

final case class ExportQuot(
    name: NameId,
    levelParams: Vector[NameId],
    tpe: ExprId,
    kind: ExportQuotKind,
    provenance: ExportProvenance
) extends ExportDecl

final case class ExportInductiveValue(
    name: NameId,
    levelParams: Vector[NameId],
    tpe: ExprId,
    numParams: Int,
    numIndices: Int,
    all: Vector[NameId],
    ctors: Vector[NameId],
    numNested: Int,
    isRec: Boolean,
    isUnsafe: Boolean,
    isReflexive: Boolean
)

final case class ExportConstructorValue(
    name: NameId,
    levelParams: Vector[NameId],
    tpe: ExprId,
    inductive: NameId,
    constructorIndex: Int,
    numParams: Int,
    numFields: Int,
    isUnsafe: Boolean
)

final case class ExportRecursorRule(
    constructor: NameId,
    numFields: Int,
    rhs: ExprId
)

final case class ExportRecursorValue(
    name: NameId,
    levelParams: Vector[NameId],
    tpe: ExprId,
    all: Vector[NameId],
    numParams: Int,
    numIndices: Int,
    numMotives: Int,
    numMinors: Int,
    rules: Vector[ExportRecursorRule],
    supportsK: Boolean,
    isUnsafe: Boolean
)

final case class ExportInductive(
    types: Vector[ExportInductiveValue],
    constructors: Vector[ExportConstructorValue],
    recursors: Vector[ExportRecursorValue],
    provenance: ExportProvenance
) extends ExportDecl
~~~

Every wire value used as a store offset, arity, or field index is non-negative and range-checked
before conversion to Int. Arbitrary-precision informational values such as regular height remain
BigInt.

No declaration field may live only in a log message. Even when Raccoon does not give a field
operational meaning, it is retained for validation, manifest reporting, and producer-parity tests.

### 6.1 Provenance

Every interned node and declaration object has:

~~~scala
final case class ExportProvenance(
    source: Path,
    line: Long,
    column: Int,
    objectOrdinal: Long,
    kind: String,
    internId: Option[Int],
    declaration: Option[String]
)
~~~

Lowered Core nodes receive a stable synthetic SourceId and Span. The diagnostic retains
ExportProvenance separately; it must never infer an export identity back from a Span offset.
Generated eta binders, level binders, and staging wrappers use fresh AstNodeIds.

### 6.2 Compact-store requirements

Init contains millions of expression nodes. The implementation therefore must:

- store the expression tag and fixed-width operands in segmented primitive arrays;
- intern variable-length level lists, universe-parameter lists, and all arrays in compact slices;
- avoid one closure or one Scala collection per interned expression;
- use an iterative cursor for application-spine and binder-chain traversal;
- memoize lowering only within the declaration currently being checked;
- release per-declaration memo, source-reference counts, and temporary Core terms after
  publication;
- retain counters for current and high-water node-store bytes.

The first implementation is allowed to optimize after functional tests, but M1 is not accepted if
it uses a recursive object graph for all 4.3 million Init expressions.

## 7. Reader contract

LeanExportReader replaces the parsing core inside LeanExportM0. It:

1. requires the meta object first and exactly once;
2. compares the format version and producer parity fields to the pin in §2;
3. rejects unknown, missing, or duplicate fields/tags and every wrong JSON value kind, except
   that entries inside the opaque MData data object are skipped;
4. requires contiguous intern IDs beginning at their format-defined bases;
5. rejects a name, level, or expression reference that is negative, missing, or forward;
6. checks integer overflow before converting an index to Int;
7. parses Nat values as non-negative arbitrary-precision integers;
8. decodes String values without normalization into Unicode scalar sequences, rejecting invalid
   UTF-8, unpaired host UTF-16 surrogates, and every non-scalar code point before constructing an
   IR String value;
9. rejects duplicate declarations after canonical name encoding;
10. delivers one immutable declaration object to a consumer before reading the next object;
11. reports malformed input as LeanExportDiagnostic, never MatchError, assertion failure, or a
    JSON-library exception.

The all arrays are retained but are not a trust or dependency oracle. For def, opaque, and theorem
objects, all records the declarations written in the same user mutual block; the Lean kernel does
not use it because recursive definitions have already been compiled through recursors or
WellFounded.fix. T1 requires that array to be nonempty and contain the current name, and requires
members present in the stream to report the same group. It records the group but does not delay,
reorder, or jointly publish those ordinary constants.

Inside an inductive object, each family all and each recursor all must instead equal the object's
ordered family-name vector; a recursor array therefore does not contain the recursor's own name.
The family ctors arrays, constructor owners/cidx values, and recursor rules provide additional
redundant order checks. Direct global references found while lowering a type or body remain
authoritative.

LeanExportM0 and the importer are consumers:

~~~scala
trait LeanExportConsumer {
  def onMeta(meta: ExportMeta): Unit
  def onDeclaration(decl: ExportDecl, tables: ExportTables): Unit
  def finish(tables: ExportTables): Unit
}
~~~

M0's existing text output and JSON fields must remain stable after switching to the shared
reader. Any deliberate report-schema change requires a separately reviewed golden update.

## 8. Names and global registry

Lean Name.str and Name.num are distinct, while a plain dotted String cannot represent that
distinction injectively. T1 uses this canonical encoding:

- a nonempty name consisting only of safe string components keeps its normal dotted spelling;
- every other name is encoded under the reserved $lean.name prefix using tagged,
  length-delimited UTF-8 components;
- the empty anonymous name is permitted only where the wire format permits a binder display name;
- a declaration under the anonymous name is rejected;
- decoding the encoded form must recover the exact component sequence.

A safe component matches the ordinary Raccoon identifier component grammar and cannot begin with
$lean or $raccoon. Consequently Eq, Nat.add, Acc.rec, and Mathlib.Logic.Basic retain their
expected spellings, while numerical and exotic internal names cannot collide with them.

Do not introduce a blanket namespace prefix. T1's translated environment is isolated by its Env,
so prefixing every global would only complicate primitive validation and benchmark diagnostics.
The registry rejects collisions with bootstrap and internal names before lowering a body.

The registry stores, for every installed or skipped global:

~~~scala
sealed trait ImportedGlobalStatus
case object Installed extends ImportedGlobalStatus
case object SkippedUnsafe extends ImportedGlobalStatus

final case class ImportedGlobal(
    sourceName: NameId,
    coreName: String,
    provenance: ExportProvenance,
    status: ImportedGlobalStatus,
    levelParameters: Vector[NameId],
    callingConvention: Option[ImportedCallingConvention],
    primitiveCapability: Option[PrimitiveCapabilityTag]
)
~~~

No native operation is enabled through name mangling. K3 registers the exact pinned producer
names it supports. The earlier M0 suggestion to rename xor/shift spellings is superseded: aliases,
if a later producer actually requires them, must be an explicit one-to-one authenticated table.

## 9. Universe lowering

### 9.1 Declaration parameters

Lean universe parameters become leading requested-implicit Raccoon binders of type Level. For a
declaration with parameters u₁ … uₙ:

~~~text
exported type T
    becomes
{u₁ : Level} … {uₙ : Level} -> lower(T)

exported value v
    becomes
fun {u₁ : Level} … {uₙ : Level} => lower(v)
~~~

These binders are added even though the export expression has no lambda nodes for universe
parameters. Each Level.param node resolves by exact NameId against the current declaration's
universe context. Duplicate universe-parameter names and undeclared parameters are hard errors.

The same leading-zone rule applies to family, constructor, and recursor types retained from an
inductive object. The exported universe ordering is stored independently and compared where K2,
K6, or another primitive validator requires a specific order.

### 9.2 Level expressions

The translation is mechanical:

~~~text
zero       -> Level.zero
succ l     -> Level.succ lower(l)
max l r    -> Level.max lower(l) lower(r)
imax l r   -> Level.imax lower(l) lower(r)
param u    -> the LocalRef allocated for u
~~~

Level expressions are ordinary Core terms and are checked at type Level. T1 does not normalize
or reorder them itself; the kernel's K5 implementation is authoritative. Applications of
Level.succ/max/imax and Sort itself are constructed through §11 using the bootstrap globals'
checked calling conventions, not by assuming their explicit arities.

### 9.3 Constant instantiation

Expr.const contains a complete list of source universe arguments. Its length must equal the
registered universe-parameter count of the selected global. These levels are the first
full-source arguments passed through the application adapter in §11. Missing, extra, or
ill-typed levels are errors even when all corresponding Raccoon binders remain implicit.

## 10. Binder and expression lowering

The lowerer is bidirectional: lowerSynth returns a Core term and its checked semantic type, while
lowerCheck additionally receives an expected Value. Read-only TypeChecker calls during lowering
provide the semantic information needed by §11; they do not publish globals. The final
declaration check in §14 remains authoritative.

~~~scala
final case class LoweredTerm(
    core: CoreAst.Term,
    checked: TypeChecker.CheckedTerm,
    convention: Option[ImportedCallingConvention]
)
~~~

### 10.1 Local context

Lean bvar 0 selects the innermost binder. The lowerer maintains an indexed stack of fresh
LocalRefs; a bvar outside that stack is an error. Binder display names are diagnostics only and
never determine identity.

Default binders request explicit Raccoon binders. implicit, strictImplicit, and instImplicit all
request implicit binders. T1 performs no typeclass search: the export already supplies every
instance argument. The original four-way BinderInfo is retained in the calling convention even
though Raccoon's checked binder has only an implicit Boolean.

Raccoon's ordinary BinderOps rejects an unforceable requested implicit, except for its existing
constructor-family-parameter demotion. T1 adds an importer classification mode to the shared
Projection compiler: every exported implicit and every synthetic universe parameter is
demotable, because the export supplies its value at every use. The compiler repeatedly demotes
the rightmost still-unforced demotable binder and recompiles projections until every remaining
implicit is forced. It then constructs the Core Pi with those final Boolean markings and submits
it to ordinary BinderOps, which must reproduce the same projections/classification.

Demotion changes calling syntax, not the dependent Pi proposition represented by the export. The
application adapter records every demotion and emits the source argument at all translated call
sites. No source binder may be made implicit when Lean marked it default.

### 10.2 Pi and lambda chains

The lowerer coalesces a maximal adjacent ForallE chain into one Core Pi telescope and a maximal
adjacent Lam chain into one Core Lam telescope. It preserves source binder order, dependency, and
requested implicitness. The lambda's checked type must agree with the translated Pi type; T1 does
not infer missing binder types.

When a lambda is lowered against an expected translated Pi, it reuses that Pi's final imported
calling convention rather than independently choosing demotions. A synthesized lambda first
classifies the Pi obtained from its annotated source binder chain, then checks its body under that
classification.

Coalescing changes Lean's unary application granularity. Section 11 compensates by saturating
each checked Core telescope and eta-expanding a source underapplication.

### 10.3 Let

A maximal LetE chain becomes Body.lets followed by Body.ret. Every exported let type is retained
as an explicit annotation and checked. Each value is lowered in the preceding context; the body
is lowered with the new LocalRef in scope.

The redundant nonDependent flag is an optimization hint and is never used to remove a binder.
When it is true, T1 validates that the body does not reference the bound bvar. False makes no
claim: the default exporter deliberately normalizes this flag to false while stripping metadata
so structurally equal expressions receive one intern ID.

### 10.4 Remaining expression nodes

~~~text
sort l          -> Sort applied through §11 to lowerLevel(l)
proj T i s      -> CoreAst.Term.Proj(canonical(T), i, lower(s))
natVal n        -> CoreAst.Term.NatLit(n), gated by K3's validated installed Nat state
strVal scalars  -> CoreAst.Term.StrLit(scalars), gated by K3's validated installed String layout
mdata e         -> lower(e)
~~~

Projection indices are bounds-checked by K4 against the checked family metadata. A named selector
is not resolved or trusted.

Nat and String nodes always parse into the export IR. If the corresponding validated K3 bootstrap
state/layout is not installed, failure occurs during lowering with the enclosing declaration's
provenance. The String IR payload is a normalization-preserving sequence of validated Unicode
scalars, not an unrestricted host `String`; the reader performs this validation before constructing
`StrVal`, and lowering does not decode or validate a second host representation. These state
markers certify representation shape and installation order; they do not certify native arithmetic
bodies. T1 never desugars a large literal into a constructor chain as a fallback.

The format has no source match node; eliminations appear as recursor applications. T1 creates
Match only for the validated synthesis paths owned by T2 or T3.

## 11. Full-source application adapter

This is T1's central translation rule. Lean export applications are unary and contain all
universe, implicit, instance, and explicit arguments. Core App supplies only the binders that
remain explicit after checking and must saturate one complete Pi telescope.

### 11.1 Calling-convention record

After a global type checks, T1 registers a convention for each maximal Pi layer:

~~~scala
sealed trait ImportedSourceBinder
final case class SourceTermBinder(info: BinderInfo) extends ImportedSourceBinder
case object SourceUniverseParameter extends ImportedSourceBinder

final case class ImportedBinder(
    sourceOrdinal: Int,
    sourceInfo: ImportedSourceBinder,
    coreBinderId: LocalRef,
    requestedImplicit: Boolean,
    checkedImplicit: Boolean
)

final case class ImportedTelescope(
    binders: Vector[ImportedBinder],
    corePi: CoreAst.Term.Pi
)

final case class ImportedCallingConvention(
    universeCount: Int,
    telescopes: Vector[ImportedTelescope]
)
~~~

Local lambdas and Pi-valued local terms carry the same convention in the lowering context. The
record is derived from the source telescope and the checked Raccoon Pi; it is not copied from
export metadata alone.

### 11.2 Saturated application

For a source application spine, flatten App nodes iteratively into a head and ordered argument
vector. A Const head contributes its universe list before its term arguments. Then, for each
checked Core telescope:

1. align one supplied source expression with every binder in source order;
2. lower, typecheck, and bind those supplied values from left to right, using earlier supplied
   values to instantiate dependent binder types;
3. collect the supplied values whose checkedImplicit flag is false as the Core explicit-argument
   vector;
4. after all explicit roots are known, run every checked implicit binder's compiled Projection
   against that vector;
5. require defEq between each projected value and the corresponding checked supplied source
   value;
6. run BinderOps.checkAndInstantiate over the full projected/explicit checked vector as a final
   telescope-order verification;
7. construct and check one saturated Core App from the explicit Core terms;
8. continue with its result type and the remaining source arguments.

Step 5 is mandatory even if the supplied expression is a proof, a universe, or syntactically
identical to a nearby argument. This rule makes calling-convention adaptation a checked erasure
rather than a trust boundary.

The implementation should expose this as a package-local helper shared by the lowerer and its
unit tests:

~~~scala
object ImportedApplication {
  def lower(
      head: LoweredTerm,
      fullSourceArgs: Vector[PendingExpr],
      expected: Option[Value],
      context: ImportContext
  ): Either[Vector[Diagnostic], LoweredTerm]
}
~~~

It may add a read-only TypeChecker helper for checking/reconstructing one full Pi telescope.
That helper must ultimately call the existing binder checking, projection, and defEq machinery;
it is not a supplied-type installer and cannot publish a value.

### 11.3 Underapplication

If the source supplies fewer arguments than a checked Core telescope contains, the lowerer
eta-expands the missing suffix:

~~~text
source:  f a
Core:    fun b ... => f(a, b, ...)
~~~

The generated binders have the specialized remaining source binder types and preserve requested
BinderInfo. The wrapper body is built by re-entering the saturated-application algorithm with
fresh LocalRefs for the missing arguments. A capture-avoiding Core substitution utility
specializes dependent binder types by the already supplied arguments.

This applies equally to:

- a first-class universe-instantiated constant;
- a partially applied local function;
- a partial constructor or recursor;
- a partial Acc.rec occurrence handled by T3;
- a source application that stops between two coalesced Lean binders.

If source arguments remain after one Core telescope is saturated, the adapter continues through
the result's next Pi layer. If the result is not a Pi, extra arguments are an error.

### 11.4 Validation tests for the adapter

Tests must cover:

- all explicit binders;
- forceable requested implicits;
- an unforceable exported implicit demoted by the importer classification pass;
- strictImplicit and instImplicit arguments;
- dependent implicit reconstruction;
- a mismatching supplied implicit;
- universe instantiation with zero, one, and several level parameters;
- underapplication before and after an implicit;
- over-one-telescope application;
- a first-class polymorphic constant;
- partial Acc.rec translated to a saturated sealed head;
- proof-valued omitted arguments, showing that equality is checked at their propositions.

## 12. Declaration policies

### 12.1 Safety filter

Safe definitions, axioms, opaques, theorems, and inductive objects proceed to lowering.
DefinitionSafety.unsafe and DefinitionSafety.partial definitions, unsafe axioms/opaques, and
unsafe inductive objects are recorded as SkippedUnsafe without an Env entry. The ordinary
lean4export command omits unsafe declarations unless run with its explicit unsafe option; the
filter remains load-bearing for hostile input and diagnostic exports.

An inductive object is safe only when every family, constructor, and recursor record has
isUnsafe=false. A mixed set of flags is a malformed producer object, not a partially importable
block. A theorem has no safety field and follows the safe theorem path.

While lowering any safe type or body, a reference to SkippedUnsafe is an
UnsafeDependency diagnostic. A reference to a name not yet installed is a ForwardGlobal
diagnostic unless it is an explicitly staged member of the current atomic object.

This is not arbitrary dependency pruning. It follows Lean's logical safety boundary and never
turns unchecked executable code into a logical axiom.

### 12.2 Axioms

For an ordinary safe axiom:

1. add leading universe binders;
2. lower and check its type as a sort;
3. run the benchmark's theory-capability policy;
4. publish AxiomDecl through ordinary Interpreter.evalDecl;
5. record its canonical name, checked type key, source provenance, and policy class in the axiom
   manifest.

The standard propext and Classical.choice assumptions are rejected until K7's evidence-grade
changes and consistency probes are present. The theory policy does not attach evaluator behavior.
Primitive packages use their own structural validators and are not installed by this ordinary
path.

### 12.3 Definitions

For a safe def:

- abbrev and regular hints become transparent ConstDecl values;
- an opaque hint becomes an opaque ConstDecl;
- the regular height is retained in the manifest but has no Raccoon conversion meaning;
- the source body is wrapped in the declaration's universe lambdas and checked at the translated
  declared type;
- lazyGlobal is false in T1. P1 may change evaluation strategy only after measurement and kernel
  review.

T1 must not make every regular definition opaque as an early performance optimization; doing so
changes Lean definitional equality and hides parity failures.

### 12.4 Opaque declarations and theorems

Opaque and theorem bodies are lowered and checked once inside the transaction. They publish as
opaque ConstDecl values. The ordinary proof representation policy then canonicalizes theorem
values: checking the source proof is mandatory even though the retained proof value contains no
source witness.

An implementation must force any lazy checker result before publishing the transaction Env. A
body that has merely been stored in an unevaluated thunk does not count as checked.

### 12.5 Inductive export objects

T1 produces one lossless ExportedInductiveBlock containing:

- the translated family and constructor headers;
- original universe order, BinderInfo, numParams, numIndices, isRec, isUnsafe, ownership, and all
  metadata;
- all exported recursor types and ordered rules;
- canonical names and provenance for every member;
- source-to-Core binder split maps, including Eq's two-parameter/one-index Lean presentation
  versus its Raccoon parameter/index presentation.

The provisional ordinary split takes the maximal family Pi chain, places the leading declaration
universe binders and the first exported numParams term binders in Core parameters, and places the
next numIndices binders in Core indices. It rejects leftover or missing family binders before K6.
K6 then derives the actual block facts and compares them with this metadata.

For each constructor, T1 separately validates its universe list, owner, cidx, and exported
numParams against the candidate family. The constructor's family-parameter prefix is represented
by the Core header and removed from its proper-field telescope; the translated result application
must reproduce the candidate family's parameters and indices. K6 recomputes all of these facts.

Eq is the documented exception required by Raccoon's proof-recovery representation. Its candidate
adapter retains Lean's numParams=2/numIndices=1 claim but provisionally places only the carrier
among its term parameters and both equality endpoints among its indices; the universe binder is
also a Core parameter. Correspondingly, Eq.refl removes the carrier prefix but retains Lean's
left-endpoint parameter as its one proper diagonal field and checks the result Eq a a. The
reserved Eq name cannot fall back to an ordinary split if ValidatedEquality rejects this shape.
No other family receives an ad hoc split in T1.

T1 sends the object atomically to K6. K6 recomputes positivity, recursion, ownership,
parameter/index splits, universes, and proof-recovery information. T2 validates or synthesizes
the recursors. T1 publishes no family or constructor before both adapters have completed the
block transaction.

The current singleton InductiveDecl path may be used behind the K6 adapter for a singleton block,
but T1 must not expose a second importer-only singleton policy. This prevents singleton,
mutual, and nested blocks from acquiring different validation rules.

The Eq block must issue ValidatedEquality before quotient or K2 equation builders use it. The Acc
block and exported recursors must retain the exact metadata required by WfPrimitives. Names alone
do not select either capability.

### 12.6 Recursors and derived declarations

Exported recursor declarations and their rule arrays belong to their inductive object and are not
processed as independent definitions. T2 owns their generated Core bodies or bodiless Prop
principles and validates the rules against K6's checked logical block.

Later casesOn, recOn, noConfusion, selector, below, and other ordinary exported definitions use
the ordinary declaration path once their recursor dependencies are installed. The sole
name-recognized cluster is the structurally authenticated T3 Acc/WellFounded transaction in §13.

## 13. Authenticated special clusters

Primitive selection uses a two-stage rule:

1. a canonical name may nominate a candidate adapter;
2. the adapter must validate the complete checked shape and dependencies before receiving its
   narrow reserved-name permit or capability.

Failure does not fall back to an ordinary declaration when the name is reserved.

### 13.1 Equality

T1 retains the exported Eq metadata and invokes WfPrimitives.validateEquality after K6 installs
the checked singleton block. The resulting ValidatedEquality is session state. Quotient and K2
equation construction receive the capability object directly.

### 13.2 Nat, String, and native operations

The checked Nat block issues K3's Nat representation capability only after its kernel-defined
shape validates. String requires a new producer-specific adapter for the 4.30 target. Lean 4.30's
`String` is a one-constructor structure headed by `String.ofByteArray`; it stores a `ByteArray` and
a proof that the bytes are valid UTF-8. `String.ofList : List Char → String` encodes its input and
constructs that representation, and the kernel expands a String literal through `String.ofList`
over `List.cons (Char.ofNat ...)`/`List.nil`.

The existing private `ValidatedStringLayout` validates Raccoon's synthetic/source-Prelude
`String.mk (List Char)` representation. It must not be issued for the 4.30 export. T1.5/K3 must
choose and validate a packed representation compatible with `String.ofByteArray`, including its
proof field and observable `String.ofList` reduction, before enabling `StrLit` in translated-Init
mode. Until that adapter lands, reaching the String block is a typed missing-kernel-gate failure;
falling back to the old CharList layout would silently assert a false producer shape.

Native operation declarations are admitted only in the dedicated trusted translated-`Init`
bootstrap mode. K3 owns one authoritative `NativeNatOpSpec` table from which T1 derives exact
producer names, typed Nat-result/Bool-result classification, reservation, and manifest entries.
Each row exposes the subtype-derived read-only `returnsBool` classification, so the importer need
not duplicate the three Bool-result names. Ordinary checking first produces an immutable candidate
environment; before committing that
candidate to the private session, T1 invokes K3's declaration validator. The value must be an
applicable transparent `VLam` with the exact `ValueId.Const(name)` and checked type
`Nat → Nat → Nat` or `Nat → Nat → Bool` selected by that table row. The `VLam` condition
reflects K3's current `Interpreter.evalApply` interception seam; it is not a semantic body
recognizer. An opaque/symbolic candidate is rejected as unavailable
rather than being admitted as an operation that can never reduce. T1 deliberately does **not**
compare checked bodies with structural templates, fingerprint them, or issue per-operation
semantic capabilities. Agreement with K3's host arithmetic table is trusted outright, following
Lean's kernel model and the ledger entry in `native-literals.md`. Reservation plus immutable
publication ensures that the same identities cannot later be replaced. The importer cannot
publish `ConstBody.Builtin` directly; the checked definition remains the fallback for
non-literal arguments, while K3
intercepts admitted literal applications by exact `ValueId.Const` identity.

K3 admission requires both native operands to be explicit `Nat` binders in addition to checking
the operation-specific codomain. T1 does not need a separate native-operation binder rule.

The trusted table has fifteen entries. Fourteen match Lean's pinned binary kernel table;
`Nat.blt` is an explicit Raccoon extension whose checked bootstrap definition is trusted under the
same isolation. The manifest distinguishes `Nat.blt` as an extension rather than attributing it to
Lean. K3's nonzero `shiftLeft` resource bound is `2²⁴`; zero left-shift and sufficiently large
right-shift return zero without allocating or converting an arbitrary exported Nat to host `Int`.
Before returning the completed translated-`Init` bootstrap to its caller, T1 calls K3's
completeness validator with the closed `PinnedTranslatedInit` profile; the authoritative table
selects all fifteen rows. Absence of any row is `MissingNativeOperation`. This profile is not stored
in `Env` and is never consulted by runtime dispatch; it is a whole-import completion check, not a
semantic capability. The bundled source Prelude uses the table's `BundledSourcePrelude` profile
and is not required to contain the eight T1-gated definitions.

Ordinary import mode receives an empty K3 native-name permit. A stream cannot activate the table by
declaring itself to be `Init`, copying the pinned version header, or presenting the right names;
trusted-bootstrap authority comes from the caller-selected import entry point.

If K3 has no implementation for an operation used by the pinned Init export, T1 stops with
MissingNativeOperation. Translating the exported structural body remains permitted when the
producer actually supplies a safe body and no reserved native identity is involved.

### 13.3 Accessibility and well-founded recursion

T1 recognizes the pinned Eq, Acc, and WellFounded declarations and supplies T3 with:

- the validated equality capability;
- the checked Acc block and Acc.intro;
- ExportedRecursor including universe order, checked type, ordered rules, and provenance;
- checked-but-unpublished wrapper declarations with their original bodies available;
- the session's temporary environment and a permit factory restricted to WfPrimitives names.

T3 follows wf-recursion.md. The Acc inductive block, sealed Acc.rec, and generic primitive equation
publish as one inductive/K2 transaction after Eq is already available. Acc.casesOn is separately
validated and synthesized as a non-recursive match; recOn/ndrec/ndrecOn are ordinary checked
wrappers over the sealed head. WellFounded and its constructor use the ordinary inductive-block
transaction.

The later WellFounded.recursion/fixF/fix wrappers and synthesized fixF_eq/fix_eq proofs form the
atomic wrapper/equation transaction. T3 extracts the minor and accessibility terms from the
checked wrapper-body patterns, eta-expands partial Acc.rec uses through §11, checks both proof
applications, and only then applies exported wrapper opacity and publishes that transaction.

### 13.4 Reserved names

ReservedNames must include Builtins, native K3 identities, internal proof primitives, quotient
identities, and WfPrimitives. An ordinary importer declaration receives the empty permit. Each
special installer receives a permit for exactly the names it has already authenticated. For K3
native operations, “authenticated” means admitted by the caller-authorized pinned translated-Init
bootstrap table plus exact name/type checking; it does not mean semantic body certification.

K2's supplied-type installer remains test-only and must not be reachable from any T1 code path.

## 14. Checking and atomic publication

LeanImportSession holds an immutable current Env. For every declaration or atomic object:

1. create a Stage with the current Env and a private registry overlay;
2. lower all member types and bodies;
3. invoke the relevant structural adapters;
4. run ordinary declaration checking in producer order against the stage Env;
5. force every staged body/check result required by §12;
6. compare exported redundant metadata and expected primitive types;
7. finalize manifest and metrics entries;
8. replace the session Env and registry only if every step succeeded.

On failure, both immutable values remain unchanged. The failed stage is retained only as a
diagnostic summary, not as a source of resolvable globals.

The session used by the pinned translated-`Init` entry point is itself private until the entire
stream succeeds. After the final declaration, T1 validates the `PinnedTranslatedInit` K3 profile,
forces the final manifest, and only then returns the Env to its caller. A missing native operation
or any later import error discards that session and exposes no partial bootstrap, while ordinary
declarations inside the private session still publish in producer order as required by §2.

T1 creates the package-private `Interpreter.TrustedBootstrap` context from the kernel-owned
`BootstrapAuthority.Native`. Its `initialEnv`, `add`, and `finish` operations derive the permit
and profile internally, perform the same per-declaration admission as the source-Prelude path, and
run final profile/layout validation. The context does not expose a raw native
`ReservedNamePermit`, accept a supplied value, or accept a “Lean already checked this” flag.

Transactions are required for:

- a quotient package;
- an inductive block and its recursors;
- the checked String/Char block together with `ValidatedStringLayout` installation;
- the Acc/K2 installation group;
- the T3 WellFounded wrapper/equation group.

## 15. Diagnostics

All failures use one algebraic diagnostic family:

~~~scala
sealed trait LeanImportDiagnostic {
  def provenance: ExportProvenance
  def declaration: Option[String]
  def path: Vector[ImportPathElement]
  def message: String
}
~~~

Required categories:

- UnsupportedProducer and MalformedExport;
- InternOrder, MissingIntern, IndexOverflow, and DuplicateGlobal;
- UnknownLevelParameter, BadBVar, and InvalidBinderMetadata;
- UnknownGlobal, ForwardGlobal, and UnsafeDependency;
- TypeLowering, BodyLowering, and ApplicationConventionMismatch;
- SuppliedImplicitMismatch and UnsaturatedCoreApplication;
- UnsupportedFeature and MissingKernelGate;
- PrimitiveShapeMismatch and ReservedNameViolation;
- NativeOperationDeclarationMismatch and MissingNativeOperation;
- ExportMetadataMismatch and RecursorRuleMismatch;
- DeclarationTypeError and DeclarationBodyError;
- AtomicStageFailure.

An error message includes the canonical declaration name, wire line/object ordinal, expression or
intern ID when available, lowering path, expected checked type, actual checked type, and the
adapter/gate involved. Pretty printing is bounded: diagnostics must not normalize or print an
unbounded export DAG.

T4 consumes these structured categories. It must not scrape human-readable checker strings to
decide whether to patch a declaration.

## 16. Manifest and benchmark instrumentation

LeanImportManifest records:

- producer/version pin and SHA-256 input digest;
- installed globals in order;
- skipped unsafe/partial globals and their safety class;
- ordinary axioms with checked type keys and policy class;
- primitive capabilities issued and the validators that issued them;
- trusted K3 native identities admitted by translated-`Init` bootstrap authority, recorded
  separately from structurally validated capabilities and including the table-derived bootstrap
  profile, typed Nat-result/Bool-result classification, and Lean-kernel versus Raccoon-extension origin;
- exported versus checked binder conventions;
- transparent/opaque decisions and ignored regular heights;
- inductive block classifications and adapter results;
- unsupported or patched declarations, which must be empty for a successful unpatched M1 run.

LeanImportMetrics records at least:

- bytes and objects read by kind;
- compact-store current/high-water bytes;
- names, levels, expressions, declarations, blocks, and rules;
- parse, lower, check, primitive-validation, and publication time;
- per-declaration wall time and allocation estimate;
- eta wrappers generated;
- requested implicits retained, reconstructed, and demoted;
- defEq calls made solely to validate supplied implicits;
- proof declarations canonicalized;
- transparent and opaque global counts;
- the slowest declarations and largest lowered declaration DAGs.

The benchmark command emits a stable JSON result plus a short console summary. It accepts a
declaration limit only as a diagnostic option; a limited run is never reported as milestone
success. Both total import time and final declaration-check time are reported, so read/lowering
overhead is distinguishable from the kernel benchmark. Prefix runs may be used as early
performance samples but are labeled with their stopping declaration and missing gate.

The deterministic manifest digest covers semantic names, declaration order, checked type keys,
policy choices, capabilities, and the input digest. It excludes absolute host paths, timestamps,
timings, heap measurements, and other machine-specific metric fields.

## 17. Planned code layout

The implementation is expected to separate these responsibilities:

~~~text
src/main/scala/com/raccoonlang/
  LeanExportIr.scala             compact stores and semantic cursors
  LeanExportReader.scala         versioned NDJSON decoder
  LeanExportNames.scala          injective name encoding and registry
  LeanImportBootstrap.scala      minimal Sort/Level environment
  LeanImportSession.scala        staging, publication, manifest
  LeanTermLowerer.scala          level/expression/declaration lowering
  ImportedApplication.scala      full-source calling-convention adapter
  ExportedInductiveBlock.scala   T1/K6/T2 handoff records
  QuotientPrimitives.scala       validated quotient installer
  LeanImportDiagnostics.scala    structured errors
  LeanImportMetrics.scala        counters and benchmark output
  LeanImportBenchmark.scala      command-line benchmark entry point
  LeanExportM0.scala             existing stats consumer, parser removed
~~~

Small supporting changes are expected in:

- CoreAst.scala / ElabAst.scala: the landed `StrLit` with a validated Unicode-scalar payload;
  no generic importer escape node; standalone packed `List Char` quotation is the checked
  `Proj("String", 0, StrLit(...))` residual;
- Env.scala / Packed.scala: immutable `NativeLiteralState.stringLayout` and the private atomic
  trusted-bootstrap installer; ordinary import mode cannot mutate or synthesize that state;
- TypeChecker.scala and BinderOps.scala: read-only checked-telescope support for §11;
- telescope/Projection.scala: explicit demotable-binder policy used only to classify imported
  fully explicit telescopes;
- ReservedNames.scala: explicit bootstrap/quotient/native/WF permit sets;
- Interpreter.scala: transaction-friendly checked declaration result, without supplied values;
- ValueQuote or a new CoreSubstitution helper: specialization for eta expansion;
- MathlibExportStats.scala: consume the shared reader and preserve M0 output.

Test files should mirror the components rather than place all cases in one end-to-end suite.

## 18. Implementation sequence

### T1.1 — Shared semantic reader

- add the IR, compact stores, provenance, version gate, and structured parse diagnostics;
- move LeanExportM0 onto the shared reader;
- pin golden M0 summaries and malformed-input cases;
- add heap instrumentation for a full Init read.

Exit: M0 results are unchanged and the reader retains enough data to lower any one declaration.

### T1.2 — Names, bootstrap, levels, and simple types

- implement injective names and the global registry;
- add LeanImportBootstrap and reserve its four builtin identities;
- lower levels, Sort, bvars, Pi, lambda, and simple constants;
- install and check small synthetic axiom/definition/theorem streams.

Exit: a synthetic polymorphic prelude imports without Prelude.default.

### T1.3 — Calling-convention adapter

- record checked telescope conventions;
- implement supplied-implicit validation, telescope saturation, substitution, and eta expansion;
- add the complete §11.4 matrix;
- exercise real Init declarations through the first unsupported inductive.

Exit: no export argument is silently omitted and no malformed Core application is generated.

### T1.4 — Remaining terms and ordinary declarations

- implement let, proj, metadata, literals, safety filtering, hints, opaque/theorem checking, and
  manifest entries;
- gate literals on validated K3 representation state;
- add transaction staging and bounded diagnostics.

Exit: all ordinary declaration kinds have synthetic positive and adversarial tests.

### T1.5 — Inductive and primitive adapters

- emit complete ExportedInductiveBlock records;
- connect K6/T2, ValidatedEquality, quotient, K3, and T3 adapters;
- replace the old `String.mk (List Char)` translated-Init assumption with a validated Lean 4.30
  `String.ofByteArray`/`String.ofList` adapter;
- reserve every privileged identity;
- add hostile same-name/wrong-shape tests for Eq, Quot, Nat, String, and Acc.

Exit: each special declaration obtains behavior only through its reviewed admission path:
structural capabilities generally, and caller-authorized trusted-bootstrap identity for K3 native
operations after their representation dependencies and checked types validate.

### T1.6 — Real Init benchmark

- run the complete pinned Init export;
- close importer bugs before classifying genuine kernel parity failures as T4;
- emit the stable manifest and metrics artifact;
- record wall time, peak memory, slowest declarations, and first post-Init gate.

Exit: the M1 acceptance conditions in §20 pass.

The phases should land independently. T1.1–T1.4 can proceed before all K3/K6/T2/T3/K7 gates are
implemented because their failure modes are explicit. T1.6 requires them.

## 19. Test plan

### 19.1 Reader and adversarial input

- every wire object and enum case in 3.1.0;
- wrong/missing/duplicate meta;
- forward and duplicate intern IDs;
- negative/overflowing indices and literals;
- invalid UTF-8/JSON string cases;
- malformed every declaration kind;
- bounded failure on a deliberately deep App and Pi chain;
- M0 golden parity on real Init, and on Mathlib.Logic.Basic once its 4.30-matched export is generated.

### 19.2 Lowering

- de Bruijn shadowing and out-of-range indices;
- universe parameters, imax, and constant universe arity;
- every BinderInfo, importer demotion, and constructor-family BinderOps demotion;
- dependent Pi/lambda and let specialization;
- projection by family/index;
- metadata erasure;
- Nat/String validated-representation-state success and failure, including rejection of the old
  `String.mk (List Char)` layout for translated 4.30 Init and round trips for the replacement
  `String.ofByteArray`/`String.ofList` adapter;
- application tests from §11.4.

### 19.3 Declarations and transactions

- transparent, opaque, theorem, and axiom publication;
- source theorem body rejected before proof canonicalization;
- unsafe/partial skip and safe-to-unsafe dependency rejection;
- failed member rolls back an entire atomic stage;
- no leaked reserved permit after a stage;
- no accidental dependency on Prelude.default;
- deterministic manifest and installed order.

### 19.4 Hostile primitive candidates

- empty or wrong Eq under the canonical name;
- malformed Quot package with individually well-typed members;
- wrong Nat/String constructors under familiar names, including a 4.30 stream presenting the old
  `String.mk (List Char)` shape;
- a reserved K3 operation in ordinary import mode, even with the right name and type;
- a K3 operation with the wrong checked type in trusted-bootstrap mode;
- manifest separation of Lean's fourteen pinned Nat identities from the `Nat.blt` Raccoon
  extension, plus the `shiftLeft` resource boundary and arbitrarily large `shiftRight` zero case;
- wrong Acc recursor universe order or rule;
- exported builtin spelling with an ordinary safe body;
- a valid primitive-like shape under a noncanonical exotic name, which remains ordinary and
  receives no capability;
- use of K2's test-only supplied-type installer from production code, which a reachability test
  must reject.

### 19.5 End to end

- a tiny hand-authored export;
- a lean4export-produced polymorphic fixture;
- Init prefixes ending before/after Eq, Quot, Nat, and Acc;
- complete pinned Init through the caller-authorized trusted-bootstrap entry point;
- the same stream through ordinary import mode, rejected at its first reserved K3 identity;
- complete Init with one corrupted implicit argument;
- complete Init with one corrupted recursor rule;
- repeat import with identical manifest digest and installed-order digest;
- native operation applied to a sealed/stuck argument, showing the Packed fallback stays stuck
  rather than crashing.

## 20. Acceptance criteria

T1's translation implementation is accepted when:

1. the shared reader accepts the real pinned Init file and preserves its M0 statistics; the same
   applies to Mathlib.Logic.Basic after a producer-matched export is generated;
2. malformed or unsupported producer input fails deterministically with provenance;
3. the importer starts from LeanImportBootstrap and never loads Prelude.default;
4. every kernel-safe ordinary declaration is checked in export order, while unsafe/partial
   declarations are skipped and audited;
5. every universe and term argument supplied by the export is either emitted or checked against
   Raccoon's reconstructed value;
6. all emitted Core applications saturate one complete checked telescope;
7. inductive objects reach K6/T2 without metadata loss and publish atomically;
8. Eq, quotient, Nat/String representation, and Acc/WF behavior is issued only after structural
   validation; the String capability validates the 4.30 `String.ofByteArray`/`String.ofList`
   representation and cannot be confused with the old synthetic `ValidatedStringLayout`; K3
   native-operation equations are confined to the explicit trusted-bootstrap path, the
   `PinnedTranslatedInit` all-fifteen profile passes before the Env is returned, and the identities
   are separately identified in the manifest, with `Nat.blt` labeled as the Raccoon extension;
9. theorem and opaque bodies are checked before their retained opaque/proof values publish;
10. the complete pinned Init import succeeds with no importer fallback axioms, no supplied-type
    publication, no unresolved safe globals, and no T4 patches;
11. the run emits a deterministic manifest and benchmark JSON including wall time and peak memory;
12. the kernel consistency, proof-collapse, termination, K2, K3, K4, and K5 suites remain green.

M1 is the first meaningful performance sample, not a performance pass/fail threshold. Its numbers
decide whether P1 work is needed.

## 21. Review points

This draft deliberately fixes the main architectural choices so implementation can begin. The
following details are suitable for iteration without reopening the trust boundary:

- the exact compact-store layout and segment size;
- the spelling of the reversible exotic-name encoding;
- whether the calling-convention helper lives beside TypeChecker or entirely in the importer
  package;
- the stable JSON schema for manifest and metrics;
- whether regular-height data should be used only for diagnostics or later conversion heuristics.

Changing any of the following requires a soundness review and edits to kernel-theory.md:

- importing unsafe/partial declarations as axioms or definitions;
- accepting supplied implicit arguments without a defEq check;
- installing a builtin or sealed primitive from name/type alone, except for an operation already
  enumerated in K3's reviewed trusted-bootstrap table;
- publishing a theorem without checking its body;
- bypassing K6/T2 validation for singleton inductives;
- adding partial application as an unchecked Core form;
- making exported recursor rules into evaluator rewrites.
