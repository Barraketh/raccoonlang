# Raccoon kernel reference

This document records the semantic rules implemented by the current trusted
checker and evaluator. It states the behavior that code may rely on. Historical
design alternatives and proposed extensions do not belong here.

## Trust boundary

The elaborator resolves source names and lowers surface syntax to `CoreAst`.
From `CoreAst` onward, declaration checking, evaluation, conversion,
unification, inductive validation, match refinement, termination checking, and
residual construction form one trusted implementation. There is no smaller
independent kernel that rechecks a certificate produced by those components.

A declaration is checked once. The checked value is then published in the
environment and trusted by later declarations. Transparent definitions publish
their evaluated values. Data-valued opaque definitions and axioms publish
symbolic heads; proof-valued declarations are canonicalized from their exact
propositions before publication.

The bundled source prelude is a trusted bootstrap. A prelude is still parsed,
elaborated, and typechecked, but prelude loading alone may install builtin
declarations and native equations. Selecting `--prelude` therefore selects a
different trusted bootstrap.

## Equality and evidence

Three judgments must remain distinct.

| Judgment | Meaning | Main consumers |
|---|---|---|
| Definitional equality, `a ≡ b` | The terms are interchangeable during typechecking. | Conversion and type fitting |
| Constructor consequence | An equation is forced inside a branch because the scrutinee is that constructor. | Index refinement and branch checking |
| Propositional equality, `Eq(A, a, b)` | The object theory contains a proof of equality. | User proofs and any claim of uninhabitedness |

Definitional inequality is not propositional disequality. A failed or stuck
unification attempt is not evidence that a constructor is impossible.

### Definitional equality

`ValueEquivalence.defEq` is the ordinary unifier run with an empty set of
refinable variables. Its successful rules are:

- evaluation, including beta reduction, constructor-match reduction, and
  registered builtin reduction;
- structural congruence for values and applications;
- extensional comparison of lambdas on shared fresh arguments;
- equality of normal forms for universe levels, kinds and lifetimes, and of
  sorts field by field;
- proof irrelevance at definitionally equal propositions;
- structure eta for eligible non-Prop inductive instances;
- equality and constructor peeling for validated packed values;
- conservative congruence of blocked matches with the same checked behavior.

Function binder grouping is exact. Two Pi values compare binder-for-binder and
must have the same binder count and implicitness within the current group.
`(a: A)(b: B) -> C` is not convertible with
`(a: A) -> ((b: B) -> C)`. Their closures compare exactly too: equal closure
kinds and equal closure scopes, as normal forms.

Conversion does not include universe cumulativity. Type fitting succeeds by
definitional equality, not by a general subtyping relation. Checking a term
against an expected type is synthesis followed by that equality: no check reads
the expected type, or its syntax, to decide the term's type.

### Refinement unification

The match checker runs the same unifier with a controlled set of refinable
variables. A link may be recorded only when the presented equation forces that
solution. In particular:

- genuine inductive family and data-constructor frames are invertible;
- arbitrary applications, Pi components (closures included), blocked
  computations, and closure captures are not invertible frames;
- an occurs failure or an equation that has several possible solutions remains
  stuck;
- level variables link only when normalization leaves a forced solution;
- a kind or lifetime variable links only when it is alone on one side and does
  not occur on the other; when both sides are variables, the later-bound one
  links to the earlier-bound one. An atom is not a variable and never links:
  admitting a value's ids as refinable leaves its atoms out. Every other kind or
  lifetime equation, a join or union on both sides included, is stuck;
- refinable values at eta-eligible structure types are expanded at the
  refinability boundary, where eta makes the expansion unique.

The store records consequences, never guesses. Evaluation does not consume a
refinement store.

### Apartness

Apartness is the stronger result used to omit an unreachable match branch. It
is produced only by evidence that supports propositional no-confusion:

- a clash between distinct constructors of a non-Prop inductive, when both
  constructor heads carry checked no-confusion evidence;
- unequal payloads of a packed codec that explicitly certifies that finite
  decoding reaches such a constructor clash. The Nat codec has this property.

Proof constructors, quotient constructors, family heads, opaque applications,
level, kind and lifetime failures, and ordinary unification failures do not
produce apartness. No two kinds and no two lifetimes are apart, so refinement
never prunes a branch on one.

## Universes and function types

A sort is a Core term of its own with three fields, a level, a kind and a
scope: `Sort { level = e, kind = k, scope = S }`. `Type` and `Prop` elaborate
to it at `Level.one` and `Level.zero`, and an omitted kind or scope to
`Kind.unr` or `Lifetime.empty`. The primitive universe equations are:

```text
Prop = Sort { level = Level.zero }
Type = Sort { level = Level.one }
Prop : Type
Sort { level = u, kind = k, scope = S } : Sort { level = Level.succ(u), scope = S }
```

`Level`, `Kind` and `Lifetime` are the sort parameters. Their forms,
`Level.zero`, `Level.one`, `Level.succ`, `Level.max`, `Level.imax`, `Kind.unr`,
`Kind.lin`, `Kind.join`, `Lifetime.empty` and `Lifetime.union`, are Core terms
too, always applied to all of their arguments. The kernel owns the parameters,
their forms and the sort formers: no declaration introduces them, the prelude
declares none of them, and no global or builtin carries a form's name.

Every sort parameter expression is normalized at birth, and its only neutrals
are variables:

- Levels normalize to maxima of offset atoms plus an optional constant.
  `imax(a, b)` reduces when `b` is known to be zero or positive and otherwise
  remains a conditional atom.
- A lifetime is the set of its lifetime variables and atoms (see
  [Scopes and atoms](#scopes-and-atoms)); `Lifetime.union` is set union.
- A kind is `Kind.lin` or a set of kind variables, the empty set being
  `Kind.unr`; `Kind.join` unites the sets, and `Kind.lin` absorbs.

Normalized representation equality is equality of levels, kinds and lifetimes.
Each normal form is built only by its own constructors, which sort and
deduplicate, so one implementation of union, join and containment serves the
checker and the evaluator. A kind or lifetime has no neutral other than a
variable or an atom, so no two of them are ever apart.

A sort of a kind other than `Kind.unr` must have a level that is never zero,
since proofs are unrestricted; the checker rejects any other sort term with
`LinearProp`. Substitution preserves both a level that is never zero and the
kind `Kind.unr`, so every sort the kernel builds satisfies the rule.

A telescope

```text
{ kind = k, scope = C } (x1 : A1) ... (xn : An) -> B
```

that binds no level has the sort

```text
Sort { level = imax(u1, ... imax(un, v) ...),
       kind = k,
       scope = union(C, S1, ..., Sn, SB) less the telescope's own lifetime variables }
```

where each `Ai : Sort { level = ui, scope = Si }` and
`B : Sort { level = v, scope = SB }`. The closure `{ kind = k, scope = C }` is
the function type's closure kind and closure scope: how its values may be
applied, and what they hold. It is evaluated where the Pi stands, outside its
own binders, and a closure kind other than `Kind.unr` at a level that may be
zero is `LinearProp`. A binder of type `Kind` or `Lifetime` contributes neither
a level nor a scope. Consequently, a Pi whose codomain is a proposition lives
in `Prop` at its scope, regardless of its domain universes. A codomain equal to
the sort `Prop` is different: `Prop` itself lives in `Type`.

A function type captures nothing, so the elaborator writes an omitted closure
field of one as `Kind.unr` or `Lifetime.empty`, and a declaration's own type is
always at that closure. A lambda's closure is part of its type and is decided by
the lambda alone. Its captures are the locals bound outside it that its body
mentions; its binder types and result are not its body, and implicit arguments
are never written, so neither contributes. Each capture contributes the kind and
scope of its type's sort, except that a variable of a sort parameter contributes
nothing, and neither does a recursive definition's reference to itself, which
names a global. An omitted closure field is the join of the captures' kinds or
the union of their scopes; a written one must contain it, else `KindExceeded` or
`ScopeExceeded` naming a capture it does not contain. The residual carries a
derived field as a kind or lifetime expression over the locals bound to its
variables (any one of them, where a refined branch binds two locals to one
variable), and evaluation re-evaluates it where the lambda stands. Sorts commute
with substitution, so that agrees with deriving the closure again from the
captures' instantiated types; the key-coherence switch asserts it on every
evaluation of such a lambda.

A telescope that binds a level is instead classified by `Large`. A level binder
changes the universe of everything after it, so no sort contains the Pi. `Large`
is kernel-internal: it is not a sort, no program writes it, and it classifies
itself, which is harmless because nothing quantifies over it. A type's
classifier is therefore a sort or `Large`, and code that reads a Pi's
classifier handles both. Instantiating a large Pi's binders yields small types
again: its codomain is always a type. Kind and lifetime binders never make a
Pi large.

The sort parameters are not types: their classifier is not a sort. Every
checked term must have a type, except in the positions that admit something
else:

- a binder of a sort parameter is admitted only where its site allows: a
  parameter site (a declaration's header, the binders before its `:`, or a
  family parameter) may bind any sort parameter, a function type's or lambda's
  binder only a lifetime, and a family index or constructor field none.
  Everywhere else a binder's type must be a type. The elaborator records each
  binder's site, so a function type written after a declaration's `:` binds no
  level;
- an expression of a sort parameter stands only where a sort parameter is
  expected: a sort's field and the argument at a binder of a sort parameter,
  which is checked against that parameter rather than synthesized alone. A term
  of another type there, another sort parameter's included, is a type mismatch;
- a reference whose type is large stands only as the head of an application;
- a large type is admitted only as a declaration's type: a definition, opaque
  definition, axiom, family or constructor, and a definition's lambda at that
  type.

Anywhere else a sort parameter, an expression of one, or a large reference is
`NotAType`.

Universes are non-cumulative, and so are kinds and scopes: two sorts are
convertible only when their levels, kinds and scopes are. Constructor-field
universe checks enforce the declared inductive's size bound, but they do not
introduce general sort subsumption.

A sort is `Prop` exactly when its level is zero, and a type is a proposition
exactly when its sort is `Prop` (a Pi by its codomain, so a large Pi into a
proposition is one too). The kernel has one definition of each, which the
checker and proof irrelevance share. Sorts are compared only by conversion.

An implicit binder is accepted only with a compiled projection that recovers
it from later explicit arguments. A sort's level, kind and scope, and a function
type's closure kind and closure scope, are projection positions; the kinds and
scopes recover a variable only when the field is exactly that variable. Checked
applications retain only explicit arguments. Checking and evaluation
reconstruct every implicit with the same projection and then check it against
its instantiated binder type. Constructor family parameters that cannot be
projected are demoted to explicit arguments; other unforced implicits are
rejected.

## Scopes and atoms

`scope l => e` is a Core term of its own. It opens an atom: an id in a
lifetime's set, allocated like a variable's and printed as the `scope`'s
binder, but not a variable. One registry, shared by checking and evaluation,
maps the term's AST node identity to its atom, so two `scope` terms are two
atoms and one term checked or evaluated any number of times is one atom, a
recursive call re-entering it included. Both checking and evaluation bind `l`
to the lifetime holding exactly that atom, and the term denotes its body's
value. A residual keeps the term with its node identity, so re-evaluating it
opens the same atom. An atom is never refinable, so refinement never links it,
and nothing abstracts over it: a function type's scope drops only its own
binders' variables.

Confinement is the one check an atom needs. A type whose value's dependency
set holds an atom whose `scope` does not enclose the position is
`LifetimeEscapes`. The checker keeps the atoms whose `scope` encloses the
position in its environment; they are lexical, and closing an environment over
a value drops them. One test applies the rule, at these choke points:

- every type the checker synthesizes, at the one exit of synthesis, so a
  `scope`'s own type is tested where its atom is no longer open; this is what
  keeps the body's type, its sort included, from naming the atom;
- every type a term is checked against;
- a binder's type, which is the type of the local it binds, and a pattern
  field's type;
- an argument at a binder whose type is a sort, which is itself a type.

Evaluation never makes the check. A value computed under a `scope` may leave it
whenever its type does not name the atom, even when the value itself holds the
atom: a closure whose code names `l` but captures nothing scoped, or a type
computed under the `scope` as the value of a definition whose type is a sort.
Every use of such a type as a type is then confined. So a global value may hold
an atom, though never a variable.

A derived closure names an atom by the `scope` binder's local, as it names a
variable by a binder's (see
[Universes and function types](#universes-and-function-types)): a capture's
type names only atoms whose `scope` encloses the lambda.

## Linearity

A type is linear when its kind is not `Kind.unr`: `Kind.lin`, or a kind
involving a variable, which some instantiation makes `Kind.lin`. A function
type's kind is its closure kind, and any other type's is its sort's, so a
family instance is linear when its declared kind under its arguments is, and a
type variable when the sort its type states is. Sorts and propositions are at
`Kind.unr`. One function decides it, and every linearity rule asks it.

Every local of linear type is used exactly once within the extent of its
binder. The binders are a lambda's or definition's parameters, whose extent is
the later binders' types, the result type and the body; a `let`, whose extent
is the rest of its block; and a pattern field, whose extent is its branch. A
pattern binds a local for every field, a `_` an anonymous one no name resolves
to, and so does `let _`. Whether a local is tracked is decided once, from its
type at its binder, so refinement never changes it. Globals are never tracked,
so a definition or opaque definition whose type is linear is `LinearGlobal`.

The ledger checks the residual of each tracked binder's extent once that
extent has checked. It counts uses along every path that takes one branch at
each `match`, and a use is any occurrence of the local. A match's scrutinee and
motive lie on every path through it; a match with no branch ends every path
through it, so it uses every linear local live at it. A lambda's body lies on
the paths at the lambda's position, so a use of a captured local inside a
lambda is one use, by the lambda, there, and the lambda uses it on every path
through its body or on none. Such a lambda is itself linear, since it captures
a local of a linear type, and is tracked like any linear value: applying it is
its use. A lambda's `decreases` clause is not in its body and is not a use.

A second use on some path is `LinearReused`, located at that use; otherwise no
use on some path is `LinearUnused`, located at the binder. So matching a
linear scrutinee consumes it once, and its fields are released to the ledger
at the branch's extent, where a wildcard over a linear field is
`LinearUnused`. A struct selector is a definition whose body is a match, so
applying one to a linear value is that value's use. The ledger is one walk,
an exhaustive match over Core terms with no wildcard arm, and runs only for a
binder of linear type. Evaluation makes none of its checks.

## Inductives and matching

An inductive declaration is installed only after checking:

- that the family result is a sort;
- universe bounds for every constructor field;
- kind and scope bounds: the family's declared kind and scope, which are never
  derived, contain every constructor field's kind and scope, `Prop` families
  included; the declared scope also contains the scope of every parameter's
  and index's type, a sort parameter's contributing nothing; and a family at a
  kind other than `Kind.unr` names each of its lifetime parameters in its
  scope;
- that every constructor result is the declared family with uniform
  parameters and well-typed indices;
- strict positivity of recursive occurrences;
- nested positivity only through parameters that the referenced inductive
  block certifies as positive.

A family instance's sort is the declared result sort under the instance's
arguments, never something read off the arguments' values, so it commutes with
substitution. A family at a kind variable is therefore linear exactly at the
instances whose kind argument is. A field of a sibling or of the family itself
is read by that declared sort, so the bounds need no fixed point. A variable in
the declared sort can only be a parameter, since no index binds a sort
parameter.

Atomic mutual-inductive blocks are available through the surface `mutual { ... }`
form. Every family in a block has the same parameter telescope and sort, level,
kind and scope alike. All provisional family heads are visible while
constructors are checked, but the block publishes only after every family
succeeds. Positivity and recursion metadata are computed for the whole block.

Constructor values erase family parameters and retain ordinary constructor
fields. Each family records only its own constructors for match
exhaustiveness.

A checked match establishes all of the following:

- the scrutinee has an inductive family type;
- every case names a constructor of that family;
- case field counts and field types agree with the constructor;
- no constructor is duplicated;
- every reachable constructor is present;
- constructor-result equations provide only justified branch refinements;
- the motive, which the match writes as its `returning` clause, is a type;
- every branch has the instantiated motive.

An omitted constructor is valid only when its result is apart from the exact
scrutinee type. A stuck equation keeps the constructor reachable and provides
no refinement.

Evaluation reduces a match only when the scrutinee exposes a justified
constructor view. Otherwise it retains a blocked match with the dependencies
that could make reevaluation productive, whose type is the motive evaluated in
the match's environment.

## Proofs and elimination

Proof irrelevance is definitional:

```text
p : P, q : Q, P and Q propositions
-----------------------------------
p ≡ q  iff  P ≡ Q
```

Operational behavior must be congruent with that equality. A proof's canonical
outer representation is chosen only from its exact proposition:

1. A declaration-certified, one-constructor recovery plan may reconstruct a
   constructor after every field is recovered and the constructor result is
   definitionally equal to the exact proposition.
2. A Pi proposition becomes a synthetic proof eta-lambda. Applying it produces
   the canonical proof of the instantiated codomain; the checked source proof
   body does not run. A large Pi into a proposition is proof-valued too, so a
   level-polymorphic lemma such as `Eq.symm` publishes as this eta-lambda and
   its body never runs.
3. Every other proof is the structureless `VProof(proposition)`.

This is finite, type-directed reconstruction, not proof search. It performs no
runtime unification. A data field is recoverable only when the exact family
instance directly determines it. A proof field is recoverable from its
instantiated proposition. Hidden existential data, constructor choice, and
values occurring only underneath another function are not recovered.

For example, any inhabitant of
`Eq(Nat, Nat.zero, Nat.zero)` canonicalizes to
`Eq.refl(Nat.zero)`. An inhabitant of `Eq(Type, Nat, Bool)` cannot reconstruct
`refl` and remains `VProof`.

A match from a proposition to a proposition is ordinary small elimination. A
match from a proposition to data is accepted only when:

- no constructor is reachable at the exact proposition; or
- every field of every reachable constructor is recoverable from that
  proposition.

Eligibility alone does not force reduction. Evaluation selects a branch only
after exact constructor-result validation reconstructs a constructor. A
non-reconstructible proof leaves a data-valued match blocked. This separation
prevents constrained indexed propositions from manufacturing data.

Proof constructor identity and fields provide no injectivity, apartness, or
termination evidence. Recursive proof fields are exposed one layer at a time,
so canonicalization never builds an infinite proof value eagerly.

## Structure eta and projections

Every one-constructor family records positional field metadata. A non-Prop
instance is structure-eta eligible exactly when the checked family has:

- one constructor;
- no indices;
- no recursive constructor field in its inductive block.

Eligibility depends on the checked family, not on whether the source used
`struct`. Prop instances use canonical proof representation and never structure
eta.

Eta is a rule, not a representation invariant. At an eligible type, a value is
definitionally equal to its constructor applied to its fields. A
constructor-headed value exposes stored fields; a neutral value exposes virtual
field projections. Conversion, match evaluation, and structural-subterm
checking all use the same eta view.

There is no primitive projection value. A positional projection is the
ordinary one-branch match that returns the chosen field. Like every match, it
has a motive: a synthetic local bound to the field's type at the projected
value. Surface `struct` selectors are generated definitions containing those
matches, with the selector's declared result type as motive. Therefore a
projection from `Prop` is governed by the proof-elimination rules above.

## Termination

Recursive functions are checked with a well-founded strict-subterm order over
strictly positive inductive data.

- A structural metric must become a strict constructor-field descendant.
- A lexicographic metric compares an equal prefix followed by one strict
  descendant.
- For a measure specification, the same expression is evaluated in the current
  call environment and with the proposed recursive arguments. The proposed
  value must be smaller in the same structural order; a measure does not
  introduce a user-defined relation.
- Applying a function-valued constructor field may produce one of that node's
  structural children.
- Fields reached virtually through valid structure eta are structural children
  of the structure value.
- Packed Nat values use numeric `<`, which is the compact form of repeated
  predecessor descent.

Every metric must have a genuine non-Prop inductive type. Proofs, quotients,
and values of user-axiomatized types are rejected as metrics.

While checking a recursive body, a raw recursive reference is valid only as
the head of a direct call whose metric decreases. It cannot escape into a
closure, constructor field, argument, return value, or opaque application.
Runtime recursion uses the already checked lambda and performs no further
decrease test.

Mutually recursive definition blocks are available through the surface
`mutual { ... }` form and are published atomically. Their members have
compatible lexicographic metric shapes, and every cross-component call must
decrease from the caller's current metric. Measure specifications are not
supported for recursive definition blocks.

## Axioms, opacity, and quotients

Axioms and opaque definitions break closed canonicity. A closed value of an
inductive type may remain a symbolic or blocked application instead of reducing
to a constructor. Kernel code must therefore never assume that every closed
inductive value is constructor-headed.

User `axiom` declarations may introduce arbitrary symbolic inhabitants. They
are typechecked, but their consistency is the user's responsibility. Proof
axioms still canonicalize according to their exact proposition; data axioms
remain symbolic.

The bundled quotient interface is the fixed non-inductive primitive surface:

- `Quot` is an axiomatically declared type former;
- `Quot.mk`, `Quot.lift`, and `Quot.ind` are prelude-only builtins;
- `Quot.sound` is an axiom identifying related representatives.

`Quot` is an axiom, so no family check applies to its classifier: its scope,
the union of the scopes of `A`'s and `r`'s types, is written by hand as part of
the trusted bootstrap. The builtins locate their arguments in
their declared types by binder name, so the prelude may add binders, such as
lifetime variables, without moving them.

`Quot.mk` is not a no-confusion constructor. Quotient equality is intentionally
coarser than representative structure, so quotient values supply neither
constructor injectivity nor apartness. `Quot.lift` reduces on `Quot.mk` only
through its registered builtin equation; `Quot.ind` provides the Prop-valued
eliminator.

## Trusted bootstrap and native values

Only a trusted prelude may publish builtin declarations or native literal
layouts. Ordinary modules cannot gain native semantics by declaring a reserved
name.

### Natural numbers

At the end of prelude loading, a declaration named `Nat` is accepted for
literal syntax only if it is exactly a Type-valued unary inductive with the
no-confusion constructors:

```text
Nat.zero : Nat
Nat.succ : Nat -> Nat
```

Ground natural numbers then use an arbitrary-precision packed payload.
Constructor formation folds ground `zero` and `succ` values into that form;
matching and mixed conversion decode one constructor layer on demand. The
representation is definitionally transparent to ordinary unary Nat programs.

The kernel has one closed table of binary Nat equations:

```text
add sub mul pow div mod gcd land lor xor shiftLeft shiftRight
beq ble blt
```

An equation attaches only to the exact transparent lambda published under its
canonical `Nat.*` name while a trusted prelude loads, after its two explicit
Nat arguments and Nat/Bool result are validated. The declaration body is
typechecked but not semantically recognized; agreement between that body and
the host equation is part of the bootstrap trust assumption. Application never
consults a global name registry, so later same-named source cannot acquire the
equation.

Subtraction truncates at zero. Division by zero returns zero, modulus by zero
returns the dividend, and `pow(a, 0)` returns one. `pow` and nonzero
`shiftLeft` reject exponents or counts above `2^24`; sufficiently large
`shiftRight` returns zero without allocating an enormous intermediate value.

The bundled prelude defines and accelerates `add`, `sub`, `mul`, `pow`, `beq`,
`ble`, and `blt`. Other table entries become available only if the selected
trusted prelude declares their exact validated definitions.

### Strings

String literals require an optional validated bootstrap layout:

- a Type-valued `Char`;
- `List(Char)` with exact `nil` and `cons` constructors;
- an eta-eligible one-field `String` with constructor `String.mk` storing
  `List(Char)`;
- a closed checked `Char.ofNat : Nat -> Char`.

The kernel trusts the exact `Char.ofNat` identity to map Unicode scalar values
injectively. A string evaluates to `String.mk` containing a packed scalar list.
The outer `String` remains constructor-headed, preserving structure eta. List
matching decodes one `nil` or `cons` layer at a time. The bundled prelude does
not currently install this layout.

## Value identity

Fast equality keys may prove definitional equality, so every value component
used to build a key must be semantically identifying. Source and synthesized
Pi, lambda, and blocked-match nodes carry distinct AST node identities;
captured values are part of closure identity. Packed keys include the codec,
canonical payload, and packed type. Source spans are diagnostic metadata and
are not identities.

A key only accelerates conversion. Equal keys must be convertible, and a key
mismatch that conversion treats as conclusive must be unconvertible. The
key-coherence assertion (`-Draccoon.keyAssertions`, on by default and off for
benchmarking) runs the conversion rules beneath every equation a key decides
and fails loudly on disagreement. Only atoms whose key is their identity are
exempt: variables (by id), constants and constructor heads (by name), and
levels (by normal form). Kinds and lifetimes key by their normal forms too, an
atom by its id, which its `scope` term's node identity determines, but
their conversion rule compares the normal forms itself, so the assertion checks
their keys. A sort's key mixes in its level, kind and scope, and a Pi's key its
closure kind and closure scope, explicitly rather than through its captures.
The kernel singletons `Level`, `Kind`, `Lifetime`, their classifier and `Large`
are equal only to themselves, which object identity decides before any key is
read.

Blocked applications and matches carry dependency sets describing which
refinement-store events could make reevaluation productive. An empty dependency
set means the computation is rigid. Materialization may rerun a blocked
computation after one of its dependencies is solved, but it does not use that
mechanism to invent proof or structure representations.

## Maintained invariants

Changes to the checker or evaluator must preserve these rules:

1. Conversion success is justified by a definitional equality rule.
2. Refinement links are forced consequences; the unifier never chooses among
   several solutions.
3. Match pruning uses apartness, never ordinary unification failure.
4. A proof's behavior depends only on its exact proposition.
5. Runtime proof reconstruction is finite and never invokes unification.
6. Proof structure supplies no no-confusion or termination evidence.
7. Structure eta applies only to checked non-Prop, nonrecursive,
   zero-index singleton families.
8. Recursive calls are accepted only from genuine structural descent.
9. Axiom, opaque, and quotient values are allowed to remain closed neutrals.
10. Native equations and literal layouts are installed only by a selected
    trusted prelude and remain attached to validated values, not global names.
11. A value key never decides an equation the conversion rules would decide
    differently.
12. Whether a sort is `Prop` or a type is a proposition has one definition.
13. A term's type never depends on where it stands: checking is synthesis
    followed by definitional equality with the expected type.
14. Sorts, levels, kinds and lifetimes are built only by the kernel's own sort
    former and forms; no global, builtin or prelude declaration names one.
15. Every checked term has a type, except where the checker's position rules
    admit otherwise: a sort parameter as the type of a binder at a site that
    may bind it, an expression of a sort parameter where one is expected, a
    large reference at an application head, and a large type as a
    declaration's type.
16. Kinds and lifetimes exist only in normal form, so their structural
    equality is definitional equality; no two of them are apart.
17. A sort whose kind is not `Kind.unr` has a level that is never zero.
18. A family's kind and scope are declared, never derived. An instance's sort
    is the declared sort under its arguments, and its declared kind and scope
    contain whatever a value of it holds or carries in its type.
19. A function type's closure is part of its identity and its sort. A lambda's
    closure is written or derived from its captures' types alone, never from
    where the lambda stands, and re-evaluating a derived closure agrees with
    deriving it again.
20. An atom is opened only by a `scope` term and is determined by that term's
    node identity, in checking and evaluation alike. It is never refinable and
    never abstracted, and no type the checker synthesizes, checks against or
    binds names it outside its `scope`; evaluation never checks this.
21. A type is linear exactly when its kind is not `Kind.unr`, and one function
    decides it. Every local bound at a linear type by a lambda, a definition's
    parameters, a `let` or a pattern, `_` included, is used exactly once on
    every path through its binder's checked extent, and no global has a linear
    type.
