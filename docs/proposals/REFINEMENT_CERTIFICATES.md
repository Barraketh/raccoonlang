# Refinement certificates

Status: **implemented** (2026-10-01). Third of three consistency changes, after
[Prop separation](PROP_SEPARATION.md) and [nominal families](NOMINAL_FAMILIES.md).
The authoritative rules are in [the kernel reference](../kernel.md#checked-constructor-exclusion).

The match checker keeps the existing unifier and branch substitutions. A proposed
constructor exclusion gains authority only after a local refutation passes ordinary
typechecking. This applies to coverage, written `UnreachableCase` diagnostics,
constructor-form scrutinees, wildcard expansion and the empty-fiber exception to
restricted large elimination from `Prop`. They consume one certified reachability
result. A failed synthesis or failed check retains the constructor and supplies no
candidate refinement store for that fallback branch.

This change implements exclusion certificates only. It does not certify links,
replace refinement unification, add a separate proof calculus, or claim to remove
conversion and branch unification from the trusted implementation.

## Constructor hypotheses

For `s : F(p̄, ī)` and a proposed constructor `C` with fresh fields `f̄` and
result `F(p̄, j̄(f̄))`, checking starts in the original match context, including
already established outer facts. The constructor fields and their dependent types
are checked there, and the constructor application is independently checked. No
store from the proposed exclusion, including a partially failed store, is supplied.

The local hypotheses are a conservative subset of the constructor consequences:

- Each data index coordinate whose two domains are already convertible and
  unrestricted contributes `Eq(T, i, j(f̄))`. Parameters are uniform and require no
  equation. Proof coordinates contribute none.
- If the scrutinee is unrestricted data and its full type is convertible to the
  constructor's full type, it also contributes `Eq(T, s, C(p̄, f̄))`.
- Proof scrutinees and linear or possibly linear scrutinees contribute only the
  eligible index equations. Proof representatives never supply value apartness.

Each hypothesis proposition is ordinarily checked before it enters the local
context. The final synthesized term must check against a private empty proposition
in that context. The fresh rigid fields and hypotheses are local universally
quantified assumptions, not published definitions or source-visible axioms.

This implementation does not build a total-space `Sigma` equality. Dropping
heterogeneous or linear coordinates weakens the hypotheses, so it can lose an
exclusion without introducing one. In particular, a known linear constructor with
only a value clash still requires the other constructor cases. A later dependent
coordinate can become homogeneous after an earlier checked equality elimination;
otherwise synthesis declines it.

## Checked proof construction

A private equality inductive, empty proposition and equality transport definition
are checked independently of the source prelude. Their unspellable global names
remain internal. The source need not supply `Eq`, `False` or a transport theorem.

Synthesis uses existing `CoreAst` terms:

| Equation | Refutation step |
|---|---|
| Distinct constructors at one unrestricted data type | A complete constructor discriminator and checked equality transport |
| Same constructor | A checked field-equality theorem, proved by a complete `Eq.refl` match; only homogeneous fields are projected |
| Same nominal Type family | A restricted N1 theorem premise for an eligible homogeneous argument |
| Different nominal Type families or approved different Type forms | A restricted N2/N3 theorem premise |
| A variable equal to a value not containing it | Ordinary equality elimination surrounds the remaining proof |
| Convertible endpoints | Delete the equation |

Packed literals are quoted through their ordinary constructor decoding or registered
literal syntax. Type-valued Pi codes are quoted with their checked binders and
codomain, so closed nested nominal contradictions remain supported. Every quotation
is checked against its semantic value and type. Structure-eta data can use an
existing source local only after this check confirms its exact value; unsupported
values are not replaced by assumed aliases.

`F.noConfusionType` and `F.noConfusion` are internal proof constructions generated on
demand, rather than public declaration members. A discriminator covers every
constructor, including constructors that ordinary pruning would omit. A
same-constructor theorem abstracts its endpoints before checking its complete
reflexivity branch. Certificate checking disables further certificate discharge,
including while checking the private foundation. It therefore cannot certify its
own missing branches. Existing branch substitution rules still check those complete
proofs.

## Nominal trust boundary

N1–N3 concern Type codes and cannot be defined by matching over universe codes.
Their private theorem premises are trusted instances of the
[reviewed nominal model](../nominal-model.md), not ordinary generated no-confusion
proofs. The factory checks their signatures and typed forms independently of the
unifier's verdict and store: N1 requires the same checked Type-family declaration;
N2 requires different checked Type-family declarations; N3 requires distinct
approved family, Type-valued Pi or Type-universe forms. Prop families, proposition
Pis, quotient heads, axiomatized heads and failures in sort fields provide no such
premise. Generalized signatures preserve rigid nominal forms rather than abstracting
a materialized Type alias into an arbitrary Type variable.

This factory and the constructor-hypothesis schema remain trusted. Ordinary
checking validates all applications of these premises, the private proof
foundation, and the resulting refutation. The nominal model is an informal relative
consistency argument; it does not establish correctness of the implementation or
collision freedom of finite value hashes.

## Fallback and validation

Neutral applications, unsupported quotations, heterogeneous field projections and
value-only linear clashes can retain a constructor. A missing case is then
`MissingCase`; a written case is checked rather than rejected as unreachable.
The existing successful unifier links remain in use and receive no certificates.

Focused tests inject incorrect exclusion proposals and invalid proof syntax. They
exercise inhabited and blocked cases, constructor shortcuts, wildcard expansion,
written unreachable cases, the Prop large-elimination gate, source-independent
bootstrap, dependent fields, linear index-only certificates and speculative
checking's enclosing linear state. The nominal tests cover nested N1–N3 and rigid
root Prop indices, including Pi codes. Completion also requires `sbt validate`, the
full GPU proof/check/rejection corpus, and byte-identical generated CUDA against the
original consistency-series baseline. The private foundation is cached once;
local proof terms and nominal signatures are checked at each discharge. Structural
search uses deterministic equality elimination/decomposition and a bounded recursion depth;
it retains the case on reaching that limit.
