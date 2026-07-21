# M0 Mathlib Export Statistics

Status: **done; both Lean 4.30 inputs refreshed** (2026-07-20). This is the evidence record for
`mathlib-export-port.md` milestone M0 and the K5/K6 decisions.

## Scanner

`LeanExportM0` reads lean4export NDJSON format 3.1.0 directly from an input stream. It validates
the sequential name, level, and expression intern tables and rejects forward references. It does
not retain an export AST: bitsets carry the transitive facts needed to identify declared types
containing `Sort (imax ...)` and declarations using a Sort-motive `Acc.rec`.

Run it with:

```text
sbt "runMain com.raccoonlang.translator.MathlibExportStats export.ndjson"
sbt "runMain com.raccoonlang.translator.MathlibExportStats --json export.ndjson"
```

The JSON form contains complete declaration provenance for every count. Tests cover transitive
expression summaries, mutual/nested blocks, the fix-cluster exclusion, literal operations,
projections, irreducibility, unsupported versions, and invalid forward references.
`ConsistencyTests` separately pins the Abel–Coquand Ω term: with a local `propext` axiom, the
closed proof function evaluates immediately to its canonical `ProofEta` lambda rather than
entering proof-driven reduction.

## Inputs and results

The current input was generated with lean4export 3.1.0 tag `v4.30.0` against Lean 4.30.0
(`d024af099ca4bf2c86f649261ebf59565dc8c622`). The exact toolchain, exporter commit, checksums,
and regeneration command are recorded under `artifacts/lean/v4.30.0/`. The earlier 4.24
`Mathlib.Logic.Basic` sample is retired; the table below uses the matching Mathlib `v4.30.0` tag at
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

| Statistic | `Init` | `Mathlib.Logic.Basic` closure |
|---|---:|---:|
| Export size | 324 MB | 524 MB |
| Objects | 6,354,855 | 9,927,630 |
| Interned names / levels / expressions | 288,269 / 576 / 6,009,998 | 646,629 / 954 / 9,166,175 |
| Declarations | 57,425 | 118,254 |
| Inductive blocks | 598 | 1,662 |
| Declared types containing `Sort (imax ...)` | 22 | 36 |
| Mutual inductive blocks | 0 | 2 |
| Inductive values flagged nested | 1 | 31 (86 occurrences) |
| Sort-motive `Acc.rec` users outside the old fix cluster | 11 | 11 |
| Projection nodes | 3,385 | 7,805 |
| Nat / String literal nodes | 247 / 1,764 | 556 / 6,808 |
| Distinct K3 Nat-operation candidates | 15 | 15 |
| Irreducible declarations | 465 | 2,749 |

The eleven `Acc.rec` users are `Acc.recOn`, `Acc.ndrecOn`, `Acc.ndrecOn.eq_1`,
`Acc.rec_eq_recC`, `Acc.ndrecOn_eq_ndrecOnC`, `WellFounded.fixF.eq_1`, `Acc.ndrec`,
`Acc.ndrec.eq_1`, `Acc.ndrec_eq_ndrecC`, `Acc.casesOn`, and
`WellFounded.fixF_eq_fixFC`. Lean 4.30's `Init.WFComputable` therefore reopens T3's old
four-wrapper assumption: the generated equation declarations and computable-recursion bridge must
be classified and translated without granting definitional recursion through proofs.

Every staged K3 Nat operation occurs already in `Init`: `add`, `sub`, `mul`, `pow`, `beq`,
`ble`, `blt`, `div`, `mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`, and `shiftRight`. T1
preserves these producer spellings and K3 reserves the exact corresponding `Nat.*` identities.
Fourteen are in Lean's pinned kernel reduction table; `blt` is K3's deliberate Raccoon extension
using the same trusted-bootstrap isolation. This makes the full fifteen-entry K3 table, rather than
a usage-selected subset, the M1 requirement.

## Gate decisions

**K5 — extend the level algebra.** The `Init` hits include `pi_congr`, `implies_congr`, and generated
constructor-elimination types. Genuine `imax` therefore survives in declaration types before
Mathlib proper; semantic recomputation with failure on surviving polymorphism is not a general
translation strategy.

**K6 — implement mutual and nested inductives in the kernel.** The 4.30 `Init` export has no mutual
blocks and has one nested inductive (`Lean.Syntax`, with two nested occurrences). The matching
`Mathlib.Logic.Basic` closure has 2 mutual blocks and 31 nested inductive values with 86 nested
occurrences. Current-producer evidence therefore confirms native mutual/nested support as a real
raw-export requirement and closes the K6 M0 evidence gate.

The high irreducibility and projection counts also confirm the existing P1 opaque-by-default plan
and make K4's representation-based projections a prerequisite rather than a tail optimization.
