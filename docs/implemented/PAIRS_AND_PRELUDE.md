# Pairs, destructuring and the trusted prelude

Status: **implemented** (2026-09-29). `docs/language.md` and `docs/kernel.md`
state its rules, and this document stays as the design record; §8 records what
implementation decided.

This document specifies four changes, driven by the GPU library spike in
`gpu/`, where most lines of a kernel thread a linear emitter and tokens through
`match … returning` on pairs:

1. the bundled prelude's trust rules become obligations on axioms and builtins,
   instead of bans on what a prelude may declare (§1);
2. the bundled prelude gains `Pair`, a pair whose components may be linear (§2);
3. `let (a, b) := e` destructures a value of any single-constructor family
   without naming its constructor (§3), and `(a, b)` builds a `Pair` (§4);
4. two defects are fixed: native Nat operations on a non-literal argument (§5),
   and blank or comment lines inside blocks, matches and inductives (§6).

Each section states its syntax, its rules and the diagnostic each rule raises;
§7 collects them. Where this document is silent on a case, the implementation
stops and reports the gap rather than choosing. §8 records the choices made in
review, and §9 places pair expressions relative to a later notation mechanism.

## 1. The trusted prelude

**1.1 What changes.** Today the bundled prelude may not declare a sealed
family, anything at a kind other than `Kind.unr`, or a kind variable, and a
test walks every prelude declaration's type to keep it so. Those bans stand in
for facts about axioms and builtins, the only parts of a prelude the kernel
does not check. An ordinary prelude declaration is checked exactly as one in
any module: the `trusted` flag only admits builtin bodies, native operations,
native literal layouts and axioms. So the bans go, and the facts they protected
become obligations of the trusted bootstrap, stated below.

**1.2 Obligations.** A trusted prelude, bundled or given with `--prelude`,
keeps these. They are audited, not checked:

- **T1 Consistency.** The axioms are consistent with the kernel's rules.
- **T2 Sealing.** No axiom or builtin yields a value of a sealed family except
  by applying that family's constructors. Structure eta and proof
  reconstruction apply to sealed families because of this (kernel reference,
  Sealing).
- **T3 Linearity.** A builtin uses each argument whose type is linear, or at a
  kind variable, exactly once on every path. No axiom takes or yields such a
  value, since an axiom has no body to account for it.
- **T4 Lifetimes.** No axiom makes two distinct lifetimes, or two instances of
  a family at distinct lifetime arguments, provably equal. No two lifetimes are
  apart, so such an equation is consistent, yet refinement along it links a
  lifetime variable and lets a token leave its scope.
- **T5 Native equations.** Each native operation's declared body agrees with
  its host equation, as today.

T1 subsumes nothing: a consistent axiom can still break T2–T4.

**1.3 What stays checked.** Unchanged:

- only a trusted prelude declares axioms and builtins (`UntrustedAxiom`,
  `ReservedKernelName`), and only its declarations receive native operations
  and native literal layouts;
- a native literal layout refuses a sealed family;
- no prelude declaration's type names an atom, since `LifetimeEscapes` already
  refuses a global whose type does. The bundled prelude's "every declaration at
  `Lifetime.empty`, a lifetime variable or a union of them" is a consequence,
  not a rule.

**1.4 The inventory test.** The conformance walk in `PreludeLifetimeTests` is
replaced by a golden inventory of the bundled prelude's trusted surface: every
axiom and builtin with its type, every native operation, every native literal
layout, and every sealed family. Changing any of them changes the golden file,
so the change is reviewed against §1.2. The bundled prelude's inventory is
today's: `Quot` and `Quot.sound` as axioms; `Quot.mk`, `Quot.lift` and
`Quot.ind` as builtins; the native Nat operations; the `Nat` layout; no sealed
family.

**1.5 Documents.** `docs/implemented/LEMUR_ON_RACCOON.md` §3.4's last sentence and §7.1's
and §7.3's prelude rules, `docs/kernel.md`'s Sealing section and its paragraph
on axioms, and `docs/language.md`'s Sealed families and Bundled prelude
sections restate the bans; each is rewritten to cite §1.2 instead.

## 2. `Pair`

**2.1 Declaration.** The bundled prelude declares:

```raccoon
inductive Pair {u: Level}{v: Level}{k1: Kind}{k2: Kind}{S: Lifetime}{T: Lifetime}
    (A: Sort { level = succ(u), kind = k1, scope = S })(B: Sort { level = succ(v), kind = k2, scope = T })
    : Sort { level = succ(max(u, v)), kind = join(k1, k2), scope = union(S, T) }
 | mk (fst: A)(snd: B) : Pair(A, B)
```

An instance is at the kind and scope its components give it:
`Pair(Tok(l), Nat)` is at `Type { kind = lin, scope = l }`,
`Pair(Nat, Bool)` at `Type`, and `Pair(Type, Type)` at
`Sort { level = succ(one) }`. Every implicit is forced from the constructor's fields,
so `Pair.mk(a, b)` writes neither the types nor their kinds, levels or scopes.

**2.2 Why a new family.** `Prod` is unchanged. Made kind-polymorphic, it would
lose its selectors: `Prod.fst` binds `snd` and drops it, which is
`LinearUnused` once `snd` may be linear, so `p.fst` would go for every program.
`Pair` is an `inductive` for the same reason and has no selectors; its values
are taken apart by destructuring (§3) or `match`.

**2.3 Components are types.** A component's level is a successor, as every sort
at a kind variable must be (`LinearProp`). A proof is paired with a value by
`Prod`, `Sigma` or `Subtype`.

## 3. Destructuring

**3.1 Syntax.**

```text
Let      ::= let Pattern [: T] := e
Pattern  ::= name | _ | ( Pattern , Pattern , ... , Pattern )   -- two or more components
```

`let (x) := e` is a parse error. A pattern appears only in a block's `let`, not
in a binder, a lambda or a `match` case.

**3.2 Scrutinee.** `e` is checked as a `let`'s value is, against `T` when one
is written. Its type, evaluated, must be an instance of a structure-eta
eligible family: one constructor, no indices, no recursive constructor field,
and not in `Prop` (kernel reference, Structure eta and projections). Otherwise
the destructuring is `NotDestructurable`, naming the type. A type that a
transparent definition computes to such an instance is one; a type variable, a
function type, and a blocked type are not.

**3.3 Components.** A pattern `(p1, …, pn)` matches the constructor's stored
fields in order. Erased family parameters are not fields, as in a `match`
pattern. `n` must equal the number of stored fields, else `ArityMismatch`.
There is no flattening: `(e, a, b)` against a two-field family is
`ArityMismatch`, and a nested value is taken apart by a nested pattern,
`(e, (a, b))`. A nested pattern means `let (e, t) := x` followed by
`let (a, b) := t` for a fresh anonymous `t`, so every rule below applies to it
at each level.

**3.4 Names.** Each name, or `_`, binds a local whose extent is the rest of the
block, as a `let`'s does. A name may occur once in a pattern, else
`AlreadyDefined`, as in a `match` case. Names may shadow earlier locals, the
scrutinee's included: `let (e, x) := op(e, y)` is the common form.

**3.5 Typing.** Checking binds each name to the corresponding field of the
scrutinee value's eta view: a constructor-headed value's stored field, or a
neutral's field projection. Like a `let`, the binding is transparent. So a
field whose type names an earlier field gets that type at the scrutinee, and
any type the rest of the block computes from the names is stated about the
scrutinee. The destructuring's type is the rest of the block's type. The
derivation reads only the scrutinee and the block, never an expected type.

**3.6 Linearity.** The scrutinee is a use, at the destructuring, of every local
it mentions. Each name is tracked by its field's kind, as a `let`'s local is by
its value's. So a linear field bound to `_`, or bound and not used on some
path, is `LinearUnused`, and one used twice is `LinearReused`. Destructuring a
linear scrutinee consumes it, as matching does. The family has one constructor,
so every path destructures.

**3.7 Sealing.** A destructuring is a match on its scrutinee. Outside a sealed
family's module it is `SealedConstructor`, naming the family, since no
constructor is written.

**3.8 Evaluation.** Evaluation binds the names to the eta view of the
scrutinee's value, as a one-branch match on an eta-eligible family already does.
Such a value always has an eta view, so a destructuring never blocks. Its
checked form therefore carries no motive, and nothing is written for one. Where
evaluation instantiates a level-polymorphic instance's levels to zero, putting it
in `Prop`, each name is bound to its field's canonical projection, which for such
an instance is a proof, so a destructuring still never blocks. The residual keeps
the destructuring as binding forms (a nested pattern as a destructuring into an
anonymous local followed by a destructuring of it), and the printer folds them
back and prints the pattern as written. Structural descent reads the same eta view, so a destructured name
is a subterm of its scrutinee exactly as a one-branch match's field is.

**3.9 Example.** One K step of the spike's SGEMM (`gpu/examples/gemm.rac`), 50
lines of nested `match` today, becomes:

```raccoon
let (ta, tb) := st
let (e, x) := Gpu.gload(e, k.a, k.row, Gpu.add(Gpu.mulC(kt, 16), k.tx))
let (e, ta) := Gpu.storeMine(e, sa, ta, x)
let (e, y) := Gpu.gload(e, k.b, Gpu.add(Gpu.mulC(kt, 16), k.ty), k.col)
let (e, tb) := Gpu.storeMine(e, sb, tb, y)
let (e, (ta, tb)) := Gpu.sync2(e, ta, tb)
let (e, (ta, tb)) := Gpu.reads(e, ta, accumulate)
Gpu.sync2(e, ta, tb)
```

## 4. Pair expressions

**4.1 Syntax.**

```text
Term ::= ... | ( e , e )
```

`(a, b)` is the active prelude's `Pair.mk(a, b)`, looked up among the prelude's
names before any of the program's, so no local, namespace, open or declaration
of the program named `Pair` changes what it means. (A program cannot redeclare a
prelude name, so where the prelude declares `Pair.mk` this is
`_root_.Pair.mk(a, b)`.) It is checked as that application, and its type is
local: `Pair.mk` forces its implicits from the components' types. Where the
active prelude declares no `Pair.mk`, the expression is `NotFound`. Within a
prelude, a pair expression names the `Pair.mk` that prelude has declared so far.

**4.2 Arity.** A pair expression has exactly two components. `(a, b, c)` is a
parse error, and `(a, (b, c))` is written instead; `(e)` stays a parenthesized
term. There is no pair type syntax: a type is written `Pair(A, B)`, since `(`
in a type position begins a binder group, and a pair where a type stands is the
parse error "There is no pair type syntax". An argument of an application is a
term, in a type too, so `Eq(Pair(Nat, Nat), p, (1, 2))` is a type.

**4.3 Arguments follow without a space.** A term followed on its line by spaces
and then `(` is a parse error: that `(` would otherwise begin another item, a
block's result or the program's, as a pair or a parenthesized term, so `f (a, b)`
quietly meant `f` and then a pair. The printer prints `Pair.mk(a, b)` as that
application; printing it as `(a, b)` is left open.

## 5. Native Nat operations on a non-literal argument

**5.1 The defect.** A native operation applied to two literals uses its host
equation. Applied to anything else, it runs its declared body, which unfolds
one layer per unit of its recursion argument. With a large literal that is
billions of layers: checking `let v := Nat.mod(n, 4294967296)` for a variable
`n` unfolds `Nat.mul(…, 4294967296)` and overflows the host stack. That is a
host exception, which is a defect whatever the program.

**5.2 Rule.** Applied to anything but two literals, a native operation runs its
body only when every literal argument is at most the unfolding limit, `2^8`.
Otherwise the application is a neutral:

- it is blocked on what its non-literal arguments are blocked on, and is rigid
  when they are not blocked, as a quotient builtin applied to a blocked
  quotient is;
- it resumes when re-evaluated with literal arguments, and then uses the host
  equation;
- two such applications are equal when they apply the same operation to
  convertible arguments.

**5.3 Consequences.** Conversion no longer unfolds an application with a
literal above the limit: `Nat.add(x, 2000)` is not definitionally
`Nat.succ(Nat.add(x, 1999))`. This loses definitional equations and adds none,
so it cannot make a program unsound, only reject one that relied on such an
equation. Small offsets such as `Nat.add(n, 1)` and `Nat.mul(n, 2)` still
unfold. The limit stays below the recursion depth at which the host overflows:
checking `Nat.mul(n, 1024)` exhausts a default 2MB stack, and `Nat.mul(n, 512)`
a 1MB one.

The limit bounds every literal argument, not just the recursion argument:
declared bodies are checked but not semantically recognized, so the kernel
does not know which argument a body recurses on.

## 6. Blank and comment lines

**6.1 The defect.** Three separators accept exactly one line break:

- between the statements of a term block, and after its `{` and before its `}`;
- between the cases of a `match`;
- between an inductive's constructors, and after the last one, before the next
  declaration.

A blank line or a comment-only line at any of them is a parse failure, reported
without a useful message. So is a declaration on the line right after an
inductive's last constructor. Top-level declarations, namespace and `mutual`
blocks, the program's final block and argument lists already accept both.

**6.2 Rule.** Wherever a line break separates two items, any number of blank
lines and comment-only lines may stand in its place. A comment that ends an
item's line is accepted as today. Cases and constructors still begin on their
own lines, so a `match` written on one line remains a parse error.

## 7. Diagnostics and test obligations

```text
NotDestructurable
```

`NotDestructurable` is new (§3.2). Existing diagnostics gain these cases:

- `ArityMismatch`: a pattern with the wrong number of components (§3.3);
- `AlreadyDefined`: a name repeated in a pattern (§3.4);
- `LinearUnused`, `LinearReused`: a destructured linear field (§3.6);
- `SealedConstructor`: destructuring a sealed family outside its module (§3.7);
- `NotFound`: a pair expression with no `Pair.mk` in scope (§4.1);
- `TypeMismatch`: an annotated destructuring whose value has another type.

These are parse errors: a one-component pattern, and a pair expression of more
than two components.

Every rule above is a test obligation: one program the rule admits, and the
smallest mutation that reaches its named diagnostic and no earlier one. Beyond
those:

- the golden inventory of §1.4, with a prelude declaring a linear or
  kind-polymorphic family and a sealed family now loading, and each appearing
  in the inventory only if it is trusted surface;
- §5: `Nat.mod(n, 4294967296)` checks for a variable `n`, evaluates natively
  once `n` is a literal, and `Nat.add(n, 1)` still converts with `Nat.succ(n)`;
- §6: a program with a blank and a comment line at each separator of §6.1
  parses;
- the GPU spike as an end-to-end client: `gpu/Prelude.rac` drops `LPair`, the
  kernels use `Pair`, destructuring and pair expressions, `gpu/check.sh`
  stays green, and the generated `sgemm16` and `relu16` are byte for byte what
  they are today.

## 8. Decisions

1. **The name `Pair`.** `Tuple` is kept free for a later n-ary form. A module
   cannot redeclare a prelude name (`AlreadyDefined`), so the families named
   `Pair` today are renamed: 19 declarations across 8 test files,
   `examples/universe_polymorphic_vec.rac`, the `struct` example in
   `docs/language.md`, and the lifetime-indexed example of
   `docs/implemented/LEMUR_ON_RACCOON.md` §6.2 and §7.3.
2. **Levels.** `Pair` is level-polymorphic above `Prop`, as §2.1 declares, and
   holds types at any level. That declaration checks on today's kernel as a
   custom prelude addition, with linear and unrestricted instances.
3. **Arity.** No flattening in patterns (§3.3) and only binary pair
   expressions (§4.2). Right-nested n-tuples could be added later without
   changing what any program written under these rules means.
4. **The unfolding limit.** `2^8` (§5.2). Review chose `2^10`; implementation
   showed that checking `Nat.mul(n, 1024)` overflows a default 2MB host stack,
   so the limit was lowered to keep §5's purpose.
5. **Inventory, not a flag.** §1.4 makes the trusted surface visible in review.
   A CLI flag printing a custom prelude's inventory is deferred.
6. **Decided during implementation, for ratification.** §3.2 was implemented
   literally (outside `Prop` where checked; a level-polymorphic instance may land
   in `Prop` at evaluation, §3.8), after a first cut refused any instance whose
   level may be zero. §4.1's lookup is the prelude's names, which differs from a
   literal root lookup only for a program declaring its own root `Pair.mk` under a
   prelude without one (`NotFound`). Pairs are allowed among a type's arguments
   (§4.2), and §4.3's no-space rule was added after review found `f (1, 2)`
   silently parsing as two items.

## 9. Notation

Pair expressions (§4) are the one rule here that is pure notation: they name
a family, and nothing else in their meaning depends on types. They are meant
to move into a general notation mechanism once one exists, redeclared in the
prelude with the same meaning, so no program written under §4 changes. That
mechanism is deferred until kernels show what they need. The smallest
candidate is fixed operator syntax whose meaning is resolved by scope, such as
`a + b` meaning `add(a, b)` under ordinary name resolution. Destructuring (§3)
is not notation: its constructor and its bindings come from the scrutinee's
type, which no rewrite before checking can see.
