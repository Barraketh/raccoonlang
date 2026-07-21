# Lean v4.30.0 export artifacts

These artifacts were produced by the official `lean4export` tag `v4.30.0` with its matching Lean
toolchain. The uncompressed NDJSON files are reproducible build inputs and are intentionally ignored
by Git because the full `Init` export is hundreds of megabytes.

| Component | Version / commit |
|---|---|
| Lean | `4.30.0` / `d024af099ca4bf2c86f649261ebf59565dc8c622` |
| lean4export | `3.1.0` / tag `v4.30.0` / `a3e35a584f59b390667db7269cd37fca8575e4bf` |
| Mathlib | tag `v4.30.0` / `c5ea00351c28e24afc9f0f84379aa41082b1188f` |
| NDJSON format | `3.1.0` |

| Artifact | Lines | Size | SHA-256 |
|---|---:|---:|---|
| `Init.Prelude.ndjson` | 64,112 | 3.6 MB | `802e80820fe7b48f475182851f6c2385e647691596a45a8ed312b3e8e3ce452f` |
| `Init.ndjson` | 6,354,855 | 324 MB | `75b2cb000d698aac2946ea76d3401d5939c9274ebd7849d1b46f25ee2fcd28d9` |
| `Mathlib.Logic.Basic.ndjson` | 9,927,630 | 524 MB | `be0803746160ed431cc077e7af6c3c7bc5831a5df3623a1da23ad8ac2a7c58dd` |

Run `scripts/fetch-lean-artifacts.sh` from any directory to install the exact Lean toolchain, build
the matching exporter and Mathlib release, and fetch or verify all three files. The complete `Init.Prelude` export is also
checked in as a deterministic gzip test fixture at
`src/test/resources/lean/v4.30.0/Init.Prelude.ndjson.gz` (SHA-256
`315f55c34b5a2acd2f66de493497936b280c3f2a7988015bccd753a5e1309654`).
