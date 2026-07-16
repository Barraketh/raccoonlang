# M0 Mathlib Export Statistics

Status: **done** (2026-07-14). This is the evidence record for
`mathlib-export-port.md` milestone M0 and the K5/K6 decisions.

## Scanner

`LeanExportM0` reads lean4export NDJSON format 3.1.0 directly from an input stream. It validates
the sequential name, level, and expression intern tables and rejects forward references. It does
not retain an export AST: bitsets carry the transitive facts needed to identify declared types
containing `Sort (imax ...)` and declarations using a Sort-motive `Acc.rec`.

Run it with:

```text
sbt "runMain com.raccoonlang.MathlibExportStats export.ndjson"
sbt "runMain com.raccoonlang.MathlibExportStats --json export.ndjson"
```

The JSON form contains complete declaration provenance for every count. Tests cover transitive
expression summaries, mutual/nested blocks, the fix-cluster exclusion, literal operations,
projections, irreducibility, unsupported versions, and invalid forward references.
`ConsistencyTests` separately pins the Abel–Coquand Ω term: with a local `propext` axiom, the
closed proof function evaluates immediately to its canonical `ProofEta` lambda rather than
entering proof-driven reduction.

## Inputs and results

Both inputs were generated with lean4export 3.1.0 built against Lean 4.24.0-rc1
(`919e297292280cdb27598edd4e03437be5850221`). `Mathlib.Logic.Basic` is the first Mathlib slice;
as a raw module export it includes its imported Lean and Std declarations.

| Statistic | `Init` | `Mathlib.Logic.Basic` |
|---|---:|---:|
| Export size | 233 MB | 491 MB |
| Interned expressions | 4,307,977 | 8,415,362 |
| Declarations | 44,691 | 116,180 |
| Inductive blocks | 491 | 2,137 |
| Declared types containing `Sort (imax ...)` | 15 | 33 |
| Mutual inductive blocks | 0 | 8 |
| Inductive values flagged nested | 1 | 49 |
| Sort-motive `Acc.rec` users outside the fix cluster | 4 | 4 |
| Projection nodes | 2,434 | 13,326 |
| Nat / String literal nodes | 214 / 1,547 | 573 / 10,512 |
| Distinct planned native Nat operations | 15 | 15 |
| Irreducible declarations | 458 | 3,407 |

The four `Acc.rec` users are `Acc.recOn`, `Acc.ndrecOn`, `Acc.casesOn`, and `Acc.ndrec`. T3 must
translate these derived recursors against the K2 primitive in addition to mapping
`WellFounded.fixF`/`fix` and their equations.

Every staged native Nat operation occurs already in `Init`: `add`, `sub`, `mul`, `pow`, `beq`,
`ble`, `blt`, `div`, `mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`, and `shiftRight`. T1 maps
Lean's last three spellings to the Raccoon plan's `lxor`, `shiftl`, and `shiftr` names. This makes
the full table, rather than a usage-selected subset, the M1 requirement.

## Gate decisions

**K5 — extend the level algebra.** The `Init` hits include `pi_congr`, `implies_congr`, and generated
constructor-elimination types. Genuine `imax` therefore survives in declaration types before
Mathlib proper; semantic recomputation with failure on surviving polymorphism is not a general
translation strategy.

**K6 — implement mutual and nested inductives in the kernel.** The first Mathlib slice contains
eight mutual blocks and 49 inductive values flagged nested. Many are in the imported Lean compiler
and metaprogramming closure, but they are still part of an unpruned lean4export stream. Deferring
them would require a separately specified and validated dependency-pruning pass, which is not part
of T1. Native support preserves the exported no-confusion and recursor behavior.

The high irreducibility and projection counts also confirm the existing P1 opaque-by-default plan
and make K4's representation-based projections a prerequisite rather than a tail optimization.
