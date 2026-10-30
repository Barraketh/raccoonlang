# Kinds, no cumulativity, and affine linearity

**Status: 2026-10-30. Decided and implemented**, in the order of §9
(`docs/kernel.md`, "Kinds and universes"); §10 records what the
implementation had to settle. This settles
[KERNEL_FOLLOWUPS.md](KERNEL_FOLLOWUPS.md) 3.1 (kind polymorphism) and 3.6
(exactly-once versus affine use), and removes universe cumulativity. That
removal also covers 1.1 and 1.2, which are both disagreements between a
value's own universe and the universe it is used at.

## 1 Goals

- **One family per shape.** `List` and `Prod` serve copyable and linear
  contents alike, so `LList`, `Tensor` and their libraries are retired.
- **No universe cumulativity.** This applies to levels and to the copy/linear
  distinction. A type is used at exactly its universe. The current
  half-cumulativity, which applies at arguments but not under function types
  or at results, is a source of bugs.
- **Affine use.** A linear value is used at most once on every path, and
  dropping it is allowed everywhere. Soundness needs only no-duplication; the
  formalization's `Inv.forget` already shows that forgetting tokens preserves
  the invariant.

## 2 Kinds

`Kind` is a kernel sort like `Level`. Its values are:

- `Kind.copy` and `Kind.lin`, with `copy < lin`;
- variables, bound by captures;
- `Kind.join(k1, k2)`.

The normal form is either `lin`, or a finite set of variables, where the empty
set is `copy`. Joins with `copy` vanish, and a join with `lin` is `lin`.

**Universes.** A universe is `Univ(k: Kind)(l: Level)`, whose type is
`Sort(Level.succ(l))`. `Sort(l)` and `Lin(l)` stay as the names of
`Univ(Kind.copy, l)` and `Univ(Kind.lin, l)`, so most existing code reads
unchanged. `Prop` stays outside `Univ`.

**Captures.** `(A: Univ($k, $u))` binds a kind variable and a level variable,
as `Sort($u)` binds a level today. `Sort($u)` and `Lin($u)` fix the kind.

**Apartness.** `Univ` forms whose kinds are different constants are apart.
Forms whose kinds contain variables stay stuck, as level mismatches do.

## 3 Linearity from kinds

- **Linear types.** A type is linear when its kind is not provably `copy`:
  either `lin`, or a normal form that contains a variable. A value is linear
  when its type is.
- **Tracking** is decided at the binder from the binder type's kind, as now.
  A binder of variable kind is tracked.
- **Kind-polymorphic code.** A body that is polymorphic in `k` treats values of
  kind `k` as affine. This is like Rust generic code over a `T` without a
  `Copy` bound. A caller instantiates `k := copy` and passes copyable values
  freely. There is no kind case analysis and no "copy when copyable"
  specialization (§9).
- **Function types** have kind `copy`, `Univ(Kind.copy, max of levels)`,
  whatever their domains' kinds (F1). Every function value is copyable (F5).
- **Unchanged rules:**
  - instance binders (L7) and `Eq` carriers (L8) must be provably `copy`;
  - relaxed S1 reads are unchanged, and values of variable kind carry
    provenance like other linear values.

## 4 Families

A family's universe may be a kind expression over its parameters' kind
variables:

```text
inductive List (A: Univ($k, $u)) : Univ(k, u)
inductive Prod (A: Univ($k1, $u))(B: Univ($k2, $v)) : Univ(Kind.join(k1, k2), Level.max(u, v))
```

- **L1, generalized.** A field's kind is at most the family's kind in the
  lattice: the family is `lin`, or the field kind's variables are among the
  family kind's. A field's level is at most the family's level, as now. This is
  family formation, not subtyping of values.
- **L2.** Parameters such as `A : Univ($k, $u)` are types, so they are
  unrestricted. Indices have `copy` kind, as now.
- **The nominal size rule** is unchanged. Kinds cost nothing.
- **Instances.** `List(Nat)` is copyable and `List(Tok(…))` is linear. Under
  affine use, a `struct`'s selectors are usable at linear instances: a
  selector consumes the struct and drops the other fields. That is why `Prod`
  can replace `Tensor`.

## 5 No cumulativity

- **No subsumption.** `Univ(k, u) ≤ Univ(k', v)` is gone. Conversion is the
  only relation used to check a value against an expected type. `sortLeq`'s
  ordering cases, the subsumption in `checkFits` and `tryLinkVar`, and the
  `opensLin` flag on level captures (`Lin($u)` opening on `Sort`) are
  removed.
- **What still orders universes** is only family formation (L1, levels and
  kinds) and the nominal size rule. Neither relates values.
- **Universe-polymorphic signatures instead.** A function that wants small
  types as well as large ones is polymorphic, `(A: Sort($u))`. A function
  that wants copyable and linear values alike is kind-polymorphic,
  `(A: Univ($k, $u))`, which replaces `$A in Lin($u)`.

## 6 Affine use

- **Use at most once.** A tracked value is used at most once on every path
  (`LinearReused`). `LinearUnused` disappears, along with the special cases for
  `_` fields and branches that end.
- **Read extents** (relaxed S1) were already affine, so the distinction
  between affine and exactly-once binders goes away.
- **`Protocol.discard` is removed.** Under affine use, an entry may simply not
  use its last supply. The trusted primitives are then `new`, `step` and
  `observe`.
- **Protocols need no drop rules** for a program to finish.
- **Scoped exactness** (open question 7), a primitive certifying that a packet
  is an instance's whole ledger, would need a separate kind of instance. It is
  no longer planned.

## 7 Migration

- **The kernel's `List`** becomes `List (A: Univ($k, $u)) : Univ(k, u)`. Its
  natives `List.append` and `List.length` take kind-polymorphic arguments; at a
  linear instance they consume their arguments. Packed words store linear
  elements as they store any others.
- **The prelude.**
  - `Prod`, `Option`, `Sigma` and the other containers become kind-polymorphic
    where their fields allow.
  - `LList` and `Tensor` are removed, and `Eq.substLin` merges into the general
    transport where its motive can be kind-polymorphic.
  - `Fact` stays.
- **Callers** in `lib/Protocol`, the tests, `examples/` and the GPU experiment
  move from `LList` and `Tensor` to `List` and `Prod`.

## 8 Formalization

`raccoon-formalization/DESIGN.md` §10 already rates kind polymorphism as one
lemma, through the `Unr` predicate, and affine use as one lemma
(`Reachable.forget`). Removing cumulativity also removes its `ULift`
coherence risk. DESIGN.md is to be updated to say that cumulativity is gone
and that `discard` is removed.

## 9 Implementation order

1. **Affine use.** The ledger and its tests, and the removal of `discard`.
2. **No cumulativity.** `sortLeq`, `checkFits`, `tryLinkVar` and captures,
   with tests migrated to polymorphic signatures.
3. **Kinds.** `Kind`, `Univ`, captures, the join, L1, the ledger's tracking,
   the kernel `List`, the prelude, and the library and test migration.

Each step is its own commit, with its tests passing.

Open, and not in scope now:
- kind case analysis or `Copy` bounds;
- linear closures (follow-ups 3.2), for which kinds give a natural home: a
  closure's kind is the join of its captures' kinds.

## 10 Implementation notes

What this document did not settle, and how the implementation settled it:

- **Constrained nested captures.** A capture nested in a pattern has its
  parameter's type, so `$A` in `List($A)` is of any kind, and code over it is
  kind-polymorphic. Code that needs copyable elements, because it states an
  equation of lists, a permutation or a membership, or copies an element,
  writes `List($A in Sort($u))`: a capture may carry a constraint, as a
  binder's `$A in Sort($u)` does, which every use checks. The prelude's
  `List.filter` and `List.append_assoc`, and `lib/Protocol/Lists`, use it.
- **Captures under computed heads.** A capture reads the argument's type
  by position, which inverts the application only at a family or opaque
  head. Before kinds this let an alias `Small (A: Sort(0)) := List(A)` take
  `A := Type`, and once `List` was kind-polymorphic, an alias
  `SList (A: Sort($u)) := List(A)` took a linear `A` that its body copied.
  Every binding now checks the opened values as the arguments of each
  application above a capture, against the head's parameters, and function
  types compare in both directions (kernel.md, "Type patterns").
- **Read binders.** §6 says that the distinction between affine and
  exactly-once binders goes away. A binder whose extent is a read extent is
  still distinct: it is not used at most once, but read as often as its
  extent likes, so the ledger keeps that one flag.
- **Ended paths.** With `LinearUnused` gone, the ledger no longer tracks
  whether a path continues past an empty match, so a use after one counts.
  This refuses only reuses in code that no run reaches.
- **Transport.** `Eq.subst` takes the motive's kind before its level,
  `Eq.subst(p, k, v, motive, h)`, and replaces `Eq.substLin`.
- **Containers.** `Prod`, `Option`, `Sum` and `Subtype` are kind-polymorphic.
  Only `Sigma`'s first component is, since its family `B: A -> Sort(v)` would
  need a kind parameter, which changes its arity. `Exists` and `Nonempty` are
  propositions, and `Eq`, `Inhabited` and the classes need copyable carriers
  or instances (L7, L8), so they keep `Sort`.
- **Conversion of kinds.** A kind that is one variable converts with that
  variable, so `Kind.join(Kind.copy, k)` is `k`. Levels have no such rule:
  `Level.max(Level.zero, u)` does not convert with `u`, as before. The
  constant kinds are apart, so an empty match refutes
  `Eq(Kind, Kind.copy, Kind.lin)`.
- **Limits.** A universe holds a kind normal form, so its kind must be a
  constant, a variable or a join of those: a kind computed by a match, or read
  from data as in `Univ(b.k, Level.zero)`, is `NotAKind`. Refinement solves
  only a kind that is one variable, so an equation
  `Eq(Kind, Kind.join(a, b), Kind.copy)` refines nothing, and code under it
  still treats a value of kind `Kind.join(a, b)` as affine.
- **Interim forms.** Step 2 came before kinds, so for one commit `LList` and
  `Tensor` held only linear values and `Fact` was linear, and the ledger tests
  moved to a test-local linear list of `Nat`, `LNats`, which a kind-polymorphic
  `List` cannot replace, since `List(Nat)` is copyable.

