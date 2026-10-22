# Interpreter performance

> **Historical measurements.** This report describes the named source snapshots,
> not current compiler performance. Revision IDs and hashes below identify the
> original measurements and may belong to histories outside this branch. GPU
> workloads and their scripts now live in the external Lemur repository. Paths
> under `target/performance` name ignored local artifacts from those runs; the
> logs and binaries are not included in a clean checkout. Current evaluator
> behavior is documented in [the kernel reference](kernel.md#evaluation-depth).

## Checked constructor result specialization (2026-10-02)

At base `c6599774890b42b4c4bb9985a20b07c4253572d7`, a constructor result was cached only when its codomain mentioned none of its own binders. The checked Pi now records the exact binder indices mentioned anywhere in the codomain, including nested closures. Constructor application binds only those arguments when evaluating a dependent result. Each checked Pi instance keeps at most four closed results, matched by the identity of the relevant actual values, so reuse preserves their exact type annotations and nominal owner. Unresolved or blocked inputs and results do not enter the cache. A changed closure, environment, or binder vector falls back to full instantiation; the existing independent result path is unchanged. The specialization retains canonical proof checks for arguments on its dependent path. Implicit projection specs were already compiled before this change; no projection compilation claim is made here.

The one-tile exact-ring TinyGEMM checked-source harness ran on Oracle GraalVM 21.0.12 with `java -Xmx2g -ea`, two warmups and three timed samples per seed. API load/check, preparation, output extraction and the host oracle stayed outside `Interpreter.evalApply(run, Vector(prepared))`. Baseline was run from the frozen base worktree, then the candidate from the isolated `codex/call-type-plans` checkout, with no concurrent heavy build or benchmark. These are sequential, unpaired JVM observations; they do not measure the cache hit rate or isolate slicing from memoization.

| Seed | Base samples (s), median | Candidate samples (s), median | Observed median change |
| --- | --- | --- | ---: |
| 17 | 11.491, 11.481, 11.597; **11.491** | 9.624, 9.563, 9.545; **9.563** | −16.8% |
| 83 | 11.517, 11.513, 11.496; **11.513** | 9.545, 9.572, 9.590; **9.572** | −16.9% |

Every warmup and timed run passed the complete 16,384-cell output oracle and expected counters: 1,251 warp steps, 88 async completions, 98,304 TMA bytes, 1,048,576 scalar multiplies and adds each, four MMA instructions, 64 tensor-memory loads and 16 stores. `sbt validate` passed 967 tests. Raw baseline (`target/performance/call-type-plans/jvm-baseline.log`), candidate (`target/performance/call-type-plans/jvm-candidate.log`), and validation (`target/performance/call-type-plans/validate.log`) logs are preserved in ignored `target/performance`; their hashes and the measured source hashes are in provenance (`target/performance/call-type-plans/provenance.txt`). Native performance is unmeasured for this isolated change.

## Soundness integration on `soundness_performance`

This snapshot layers the reviewed 22-file performance delta from `438be1281f7fbaa7aa34ee4ce2b1bdc306f3ad08` to `fbee3bf469565d17145f050ca2cd696d50d7b850` onto `soundness_improvements` at `acaf536ec836f55fcb2b024e2badc6814521678f`. The soundness branch remains the base: nominal family classifiers, proposition/data separation, checked refutations, Prelude proofs, and soundness tests are retained. Two small compatibility edits accompany the merge: the soundness helper now closes an empty-capture environment through `Env.closeForEval(Set.empty)`, and a hand-built data-valued `VPi` test supplies the current `isPropValued = false` field. The measured source and test diff against `acaf536` has SHA-256 `4e7da421a5241242716604d9d24043cd0d8dd1603653c3ba2839e0292eed1e1d`.

The baseline executable was built from `acaf536` and is preserved as `raccoon-soundness-acaf536` (`target/performance/raccoon-soundness-acaf536`) (SHA-256 `2c688b1888f58c754bfc57a96192a5f1df36943452f6261b41305152ebb1d054`). The candidate was built from the matching measured working tree based on `acaf536` plus the source/test delta above, and is preserved as `raccoon-soundness-performance` (`target/performance/raccoon-soundness-performance`) (SHA-256 `b103ede6429e5f8d481c88111dd800d7ab420db72e3eec42601d342d466de39e`). Both used Oracle GraalVM 21.0.12, Native Image O2, Serial GC, `--parallelism=4 -J-Xmx3g`, and default-enabled assertions. The benchmark ran three alternating baseline/candidate pairs per example with `--raw`; no other heavy job ran concurrently. All nine pairs produced byte-identical stdout.

| Example | acaf536 median wall / CPU / peak RSS → candidate median wall / CPU / peak RSS | Output bytes and SHA-256 |
| --- | --- | --- |
| `attention` | 20.648 / 20.190 / 762,232,832 B → 5.480 / 5.230 / 176,586,752 B | 455,703; `9de220cd1563838ff01034fa38a57dbbb236d1cb4b11db974ddc16758c4d5ba8` |
| `attention_pingpong` | 32.577 / 32.540 / 1,249,263,616 B → 8.866 / 8.840 / 160,628,736 B | 696,817; `c7799ca4d1ac07a8190a78d829b12d205f4fc013cf3547bff4f48b6df7feeb0a` |
| `attention_a3b` | 33.860 / 33.820 / 1,344,356,352 B → 9.007 / 8.990 / 169,984,000 B | 758,235; `912cec153aeddf13c6cf23ab300af4bafbdcb5fb614cf7a87feba91ad962f2c7` |

The integrated candidate passed `sbt scalafmtAll` and `sbt validate` with 952 tests, no failures or errors; the unchanged `acaf536` baseline passed 928 tests. `gpu/check.sh` passed all 189 checks with no skips using the `raccoon-cuda:12.9` container (`nvcc` 12.9.86, `ptxas` 12.9). The attention, ping-pong, and A3b kernels and their causal variants met their register budgets with no spills. The baseline build log (`target/performance/soundness-baseline-build.log`), baseline validation log (`target/performance/soundness-baseline-validate.log`), candidate build log (`target/performance/soundness-performance-build.log`), candidate validation log (`target/performance/soundness-performance-validate-final.log`), raw benchmark JSON (`target/performance/soundness-performance-native-results.json`), benchmark console log (`target/performance/soundness-performance-native-results.log`), and GPU gate log (`target/performance/soundness-performance-gpu-check.log`) preserve the run evidence. Additional source and binary hashes are recorded in the integration provenance file (`target/performance/soundness-performance-provenance.txt`).

## Historical capture-only snapshot on `codex/interpreter-performance`

The following measurements are from the earlier interpreter-performance branch, before soundness integration. They are preserved as historical evidence and do not describe the `soundness_performance` snapshot above.

This follow-up records the final integrated source after the capture-only `Env` change. The measured source tree was later committed as `4495b852aa70057356093f6a1dc545402b2f1e06`, based on the earlier integrated snapshot `38016598849535b7bd42b1f4930acb2d0c231c51`. The executable was built and benchmarked from matching working-tree bytes at `0e8ff1d8faa4ad7daa470ce6075a82a0e4dfda87`, with the reviewed `Env.scala` replacement still uncommitted. The final source fingerprint is `aca1ac01c74c42cea577208012902a4fe93800e32a92e4bf2e24191646e3799a` for `git diff 3801659 -- src`; the `Env.scala`-only difference is `710a977b263aed400ffddfba90c5d019a03a71e12223ff2f2874c49084cf1c84`. These fingerprints establish that the committed source and measured working tree match. The built candidate SHA-256 is `25ee2ad1f9aa3cbca7386bb113cc85209d3f0b9a24b09edcaa46b60384474247`; later documentation-only commits do not change it.

The comparison uses the preserved 380 executable (`target/performance/raccoon-before-cleanup`) (SHA-256 `80963f53b538e88db59f365cb153f609201eb8c211ede054ad3bbb548e185320`) and the final candidate (`target/performance/raccoon-env-capture-only`) (SHA-256 `25ee2ad1f9aa3cbca7386bb113cc85209d3f0b9a24b09edcaa46b60384474247`). Both were built with Oracle GraalVM 21.0.12, Native Image O2, Serial GC, and assertions enabled. The benchmark ran seven alternating baseline/candidate pairs per example with `--raw`, without concurrent builds or tests. All 42 stdout results matched byte-for-byte.

| Example | 380 median wall / CPU / peak RSS → final median wall / CPU / peak RSS | Output bytes and SHA-256 |
| --- | --- | --- |
| `attention` | 5.333 / 5.320 / 115,556,352 B → 5.296 / 5.280 / 164,970,496 B | 455,703; `9de220cd1563838ff01034fa38a57dbbb236d1cb4b11db974ddc16758c4d5ba8` |
| `attention_pingpong` | 9.082 / 9.070 / 178,782,208 B → 9.071 / 9.050 / 166,313,984 B | 696,817; `c7799ca4d1ac07a8190a78d829b12d205f4fc013cf3547bff4f48b6df7feeb0a` |
| `attention_a3b` | 9.245 / 9.220 / 162,889,728 B → 9.240 / 9.220 / 172,376,064 B | 758,235; `912cec153aeddf13c6cf23ab300af4bafbdcb5fb614cf7a87feba91ad962f2c7` |

The paired CPU deltas below are final minus 380. They show no material consistent slowdown: attention improved in every non-tied pair; ping-pong and A3b had mixed signs and near-zero medians.

| Example | Seven paired CPU deltas, seconds | Median delta | Positive pairs |
| --- | --- | ---: | ---: |
| `attention` | −.010, −.040, −.040, .000, −.040, −.010, −.070 | −.040 | 0 / 7 |
| `attention_pingpong` | +.030, −.030, +.010, −.030, +.040, −.030, +.010 | +.010 | 4 / 7 |
| `attention_a3b` | +.060, +.050, .000, −.040, −.020, −.010, +.050 | .000 | 3 / 7 |

The paired wall-delta medians were −.033 s for attention, +.008 s for ping-pong and +.002 s for A3b. RSS varied between processes; the per-binary medians are shown above and are not treated as a stable memory result. Raw measurements and run ordering are in the final JSON (`target/performance/env-capture-native-results.json`) and console log (`target/performance/env-capture-native-results.log`); the native build log (`target/performance/env-capture-native-build.log`) and source provenance (`target/performance/env-capture-provenance.txt`) are also retained.

The accepted Env change only routes `localValueOption` through the existing `runtimeValueOrNull` lookup. `apply(ref)` and `containsLocal` retain their original implementations from 380, preserving the measured hot paths. The string append implementation retains a Boolean packed-suffix marker and the constructor-prefix length; the prefix length determines the packed suffix boundary without storing a second offset. The validated native append path, output key semantics and source-shaped printing remain covered by the existing semantic tests. Constructor-result caching remains enabled with the checked-independent-codomain guard and per-`VPi` result ownership; the isolated cache ablation below supports retaining it.

The final source passed `sbt scalafmtAll` without formatting changes and `sbt validate` with 930 tests, 0 failures and 0 errors. The full `gpu/check.sh` gate passed 189 checks with no skips or failures against the final candidate. It used the `raccoon-cuda:12.9` container (`nvcc` 12.9.86 and `ptxas` 12.9); generated attention kernels met their register budgets with no spills. See the validation log (`target/performance/env-capture-validate.log`), GPU gate log (`target/performance/env-capture-gpu-check.log`) and formatting log (`target/performance/env-capture-scalafmt.log`).

### Follow-up design measurements

The final capture-only Env shape follows two rejected consolidation trials. A full shared `localValueOrNull` helper changed `apply`, membership and capture lookup; in six rotated ping-pong rounds it cost a median +.105 s CPU versus the string-only snapshot, with all six paired deltas positive. A partial shared-helper integration trial that still kept specialized membership was +.12 s paired median CPU on A3b over three pairs versus 380 (individual deltas +.10, +.12 and +.20 s). That trial included the other integrated changes and does not isolate the helper's causal contribution. The final version avoids both helper variants on the hot `apply` and membership paths. The string-only snapshot itself had mixed/flat A3b CPU deltas across seven pairs (median −.01 s) and noisy attention deltas across three pairs (median +.10 s); its ping-pong comparison was also mixed (median −.03 s). These are not evidence of a consistent string-only regression. The retained six-round comparison is here (`target/performance/cleanup-attribution/string-cleanup-attribution.json`), with A3b attribution (`target/performance/cleanup-attribution/env-attribution-a3b.json`), attention attribution (`target/performance/cleanup-attribution/env-attribution-attention.json`) and the partial trial's exact benchmark here (`target/performance/env-partial-native-results.json`).

The constructor cache was compared against an otherwise unchanged build where `VPi.constructorResultType` always computed `codomain(instantiatedEnv)`. The ablation retained `CheckedPiCodomain`, syntax eligibility analysis, hash loops and determining/evidence indices, so it tests the combined benefit of skipping argument-environment binding and memoizing the independent result. It made two temporary lazy-val visibility widenings solely to satisfy unused-field compiler warnings; those visibility edits are not in the shipped source. Cache-off CPU cost increased by +.410 s on ping-pong, +.270 s on attention and +.340 s on A3b by median paired deltas; all 13 pairs were positive, and all 26 outputs matched byte-for-byte. RSS was noisy. This supports keeping the guarded per-instance cache, but does not separate the binding and memoization savings. The ablation provenance (`target/performance/cache-study/cache-study-provenance.txt`), temporary patch (`target/performance/cache-study/cache-study-ablation.patch`), ping-pong data (`target/performance/cache-study/cache-study-pingpong-results.json`) and attention/A3b data (`target/performance/cache-study/cache-study-attention-results.json`) are preserved.

## Historical 380 checkpoint measurements and analysis

The sections below retain the earlier report for the 380 checkpoint source and executable. They provide historical comparison, isolated redesign gates, native phase budgets and JVM profile guidance; they do not measure the capture-only source snapshot above.

### Integrated native results at the 380 checkpoint

At the 380 checkpoint, the then-final integrated interpreter was measured on 2026-10-02 on macOS arm64
with Oracle GraalVM 21.0.12 Native Image, optimization level 2 and its
configured Serial GC. The candidate is the reviewed `codex/interpreter-performance`
source on top of `dc29a918792928245bda2df5aa578346fbc3cd13`. Its implementation
fingerprint over main sources, tests and `docs/kernel.md` is
`65944b5e6c4c81f198a56a559fe2f68d7ba2da60e0cbe6f28885e8d879f42b07`; the
built executable SHA-256 is
`80963f53b538e88db59f365cb153f609201eb8c211ede054ad3bbb548e185320`.

Two preserved native binaries provide distinct comparisons. The original
`lemur_gpu` binary was built from `438be1281f7fbaa7aa34ee4ce2b1bdc306f3ad08`
(SHA-256 `c570bc5ec75840754f635f8af304dbf254b614a09b662c2010a24bff370ede19`).
The immediately preceding `dc29a91` binary is the lower-level Env and
call-path optimization checkpoint (SHA-256
`b728a8703d3ad7e853a2fa15264e2b8708be6c55996921ff881daaba711934ef`). The
three redesigns measured here are slot-backed runtime frames, validated
packed string concatenation, and constructor/call metadata specialization;
the `dc29a91` comparison isolates their combined change from that earlier
checkpoint. The original comparison measures the complete progression from
`lemur_gpu`.

Each launcher ran three times per example in separate processes, alternating
baseline/candidate order. No build, test, GPU check, or other benchmark ran
alongside a comparison. The command used `--raw`; `raccoon.envAssertions`
was left at its default `true`, so proof and environment assertions remained
enabled. The helper compares exact stdout bytes and records wall time, process
CPU time and peak RSS. Values below are medians; RSS is in bytes.

| Example | `dc29a91` wall / CPU / RSS → integrated wall / CPU / RSS | Output bytes and SHA-256 |
| --- | --- | --- |
| `attention` | 15.928 / 15.62 / 745,177,088 → 5.530 / 5.49 / 115,785,728 | 455,703; `9de220cd1563838ff01034fa38a57dbbb236d1cb4b11db974ddc16758c4d5ba8` |
| `attention_pingpong` | 26.127 / 25.89 / 1,206,992,896 → 9.630 / 9.57 / 186,630,144 | 696,817; `c7799ca4d1ac07a8190a78d829b12d205f4fc013cf3547bff4f48b6df7feeb0a` |
| `attention_a3b` | 27.037 / 26.89 / 1,291,272,192 → 9.766 / 9.72 / 216,301,568 | 758,235; `912cec153aeddf13c6cf23ab300af4bafbdcb5fb614cf7a87feba91ad962f2c7` |

| Example | Original `lemur_gpu` wall / CPU / RSS → integrated wall / CPU / RSS | Wall / CPU speedup |
| --- | --- | --- |
| `attention` | 21.330 / 21.17 / 768,753,664 → 5.616 / 5.58 / 156,205,056 | 3.80x / 3.79x |
| `attention_pingpong` | 34.547 / 34.42 / 1,247,166,464 → 9.602 / 9.50 / 146,063,360 | 3.60x / 3.62x |
| `attention_a3b` | 35.521 / 35.36 / 1,342,111,744 → 9.672 / 9.60 / 284,704,768 | 3.67x / 3.68x |

Every run against both binaries produced the exact output hash and byte count
shown above. The candidate native build log is
`integration-native-build.log` (`target/performance/integration-native-build.log`);
raw alternating results are in
`integration-vs-dc29a91.json` (`target/performance/integration-vs-dc29a91.json`)
and `integration-vs-original.json` (`target/performance/integration-vs-original.json`),
with their console logs beside them. The original and `dc29a91` executables
were preserved as `target/performance/raccoon-baseline` and
`target/performance/raccoon-dc29a91` before building the candidate.

### Standalone redesign gates

These were separate three-repeat native gates against the same `dc29a91`
binary. They establish each change's measured value at its own source
snapshot; their savings overlap and must not be added. The integrated
tables above are the end-to-end result.

| Gate snapshot | `attention_pingpong` median wall / CPU / RSS, baseline → candidate | Snapshot fingerprint and candidate binary |
| --- | --- | --- |
| Runtime slots, `030b3cb45b8f20bb4538d12ccc703e1e0eac0ec1` | 24.454 / 24.390 / 1,198,243,840 → 21.653 / 21.270 / 1,119,010,816 (−11.5% wall, −12.8% CPU) | Source diff `80616f9daf772e2cc73a75db45ca0a4bd567f44c024cb57095ec09a44b604de0`; binary `bacf2d7f25eee14700c1a1a4d3ef9c358252ba45f9626bed1ebc6baefe133d1b` |
| Constructor/call metadata, `d518055a50d91d0ed0efa40ae02806f275a38fa1` | 25.275 / 25.200 / 1,201,979,392 → 24.517 / 24.390 / 1,143,488,512 (−3.0% wall, −3.2% CPU) | Source diff `2ff1d4f8e5775226bb5e9de59bde78d7b3572164bbb2aa86f5bcc10d31338b89`; binary `ba1e1f362f3b85969fe9e41479c2927d384f0303ad5da9958c6460e78d2700b1` |

The isolated packed-string gate (`efaae035ec80369bc9553f7a55f2c6ceec29fead`,
source diff `c12b26c0de176ca4f4bc9131ae60aeb10805049b100471116a325f01edf4709a`,
binary `0c83b9ce3757d35ce4ea9762a882de0c0816d5e643c439522b4153f00ffb16e2`)
covered all three examples:

| Example | Baseline → candidate wall / CPU / RSS | Output bytes and SHA-256 |
| --- | --- | --- |
| `attention` | 15.689 / 15.630 / 752,402,432 → 6.339 / 6.300 / 268,468,224 | 455,703; `9de220cd1563838ff01034fa38a57dbbb236d1cb4b11db974ddc16758c4d5ba8` |
| `attention_pingpong` | 25.193 / 25.060 / 1,205,190,656 → 10.833 / 10.750 / 173,031,424 | 696,817; `c7799ca4d1ac07a8190a78d829b12d205f4fc013cf3547bff4f48b6df7feeb0a` |
| `attention_a3b` | 25.851 / 25.760 / 1,265,680,384 → 11.133 / 11.030 / 236,371,968 | 758,235; `912cec153aeddf13c6cf23ab300af4bafbdcb5fb614cf7a87feba91ad962f2c7` |

On pingpong, these isolated CPU reductions were 3.12 s for slots, 14.31 s
for strings, and 0.81 s for metadata. They overlap and are not additive; the
integrated comparison measures their combination directly. All isolated
slot and metadata outputs also matched exactly at 696,817 bytes with SHA-256
`c7799ca4d1ac07a8190a78d829b12d205f4fc013cf3547bff4f48b6df7feeb0a`.

The integrated code also includes reviewed follow-ups `fde2cdd48d8dbf3bdd4ff1422ee8a310e696d8e7`
(runtime-frame capture tests and cleanup) and
`7e743d563dfdb3416a205b74a89c188be66b69e5` (exact `String.data` selector
validation and direct packed extraction). Those follow-ups were not measured
as separate gates; their final combination is covered by the integrated
comparison.

### What changed and what remained checked

- Runtime argument, recursive-peer and pattern bindings use immutable slot
  frames with resolved-local offsets. Persistent checker environments remain
  intact. Ordered locals and immutable snapshots are materialized for closure
  capture, escaping neutral thunks and compatibility paths; proof
  canonicalization and environment assertions still run on every binding.
- Native `String.append` attaches only after validating the checked source
  equations and exact `String.data` selector layout. The fast path also accepts
  ordinary `List.cons` spines containing concrete Unicode characters produced
  by the validated `Char.ofNat` equation, including packed `CharList` tails.
  It then creates the same checked `String.mk` application. Generic
  `List.append`, unrecognized equations, neutral operands and nonliteral
  characters retain source evaluation. Concatenation currently copies flat
  scalar vectors, so a rope is a separate future design.
- Only a validated append result may use the private delayed-key `VApp`
  subclass. Its pending key is the ordinary `ValueKey.application` result,
  memoized on first demand; all generic application keys remain eager. A
  previous flat-vector prototype kept eager keys and rehashed every growing
  suffix. It took 23.784 s wall / 23.700 s CPU on `attention` versus 14.897 /
  14.860 s for its baseline, and 55.589 / 55.250 s for its first pingpong
  pair versus 24.687 / 24.580 s. It was rejected despite byte-identical output.
- Constructor metadata caches exact determining argument positions and
  argument-independent codomain eligibility from checked immutable syntax.
  Result-type caches are per `VPi` instance, copies with changed binders or
  codomain fall back, and the evaluator-created closure checks its owner
  binders before taking the fast path. Manual/native closures conservatively
  fall back. Key mixing and CharList scalar hashing preserve their exact
  algorithms.

The adaptive capture-selection trial added a cached-ref filter and local
count/lookup APIs. It was effectively flat against the slot snapshot: median
wall 22.169 → 22.152 s, CPU 21.88 → 22.00 s, RSS 1.129 → 1.169 GB. The trial
was removed; the final source retains the frame implementation and capture
semantics tests. Its raw results are in
`capture-followup-pair.json` (`target/performance/isolated-gates/capture-followup-pair.json`)
and the decision is documented in
`capture-followup-rejected-report.txt` (`target/performance/isolated-gates/capture-followup-rejected-report.txt`).

### Validation

The integrated source snapshot received independent clean code review, and
passed `sbt scalafmtAll` and `sbt validate` with 930 tests, 0 failures and 0
errors. Source review was clean; independent report review is a commit gate.
The final validation log is
`integration-validate-after-name-resolution.log` (`target/performance/integration-validate-after-name-resolution.log`).
The full `gpu/check.sh` run passed 189 checks with no skips. It ran against
the integrated candidate with the `raccoon-cuda:12.9` toolkit container:
`nvcc` and `ptxas` 12.9.86 compiled the generated kernels and passed register
budgets with zero spill bytes. The check log is
`integration-gpu-check.log` (`target/performance/integration-gpu-check.log`).

### Remaining native time budgets

These three-round phase runs used the integrated native binary on
`attention_pingpong.rac`, `--json`, and five source variants with rotated
execution order. Every run returned exactly `[]\n` (3 bytes; SHA-256
`37517e5f3dc66819f61f5a7bb8ace1921282415f10551d2defa5c3eb0985b570`).
The rows are medians of native process CPU time. Each increment is a measured
ceiling for that phase's work, not a promised saving. The separate
imports-only source is a subset of the declarations run, not an extra phase
to add to it.

| Phase | Cumulative CPU | Increment over previous row |
| --- | ---: | ---: |
| Prelude, checked imports and example declarations | 4.55 s | 4.55 s |
| Also construct both `Core.Program` values | 4.83 s | 0.28 s |
| Also discharge both `Core.WellFormed` proofs | 8.09 s | 3.26 s |
| Also render and concatenate both kernels | 9.33 s | 1.24 s |
| Separate prelude and imports-only source | 2.01 s | not additive |

The raw phase data is in
`integration-phase-results.json` (`target/performance/attribution/integration-phase-results.json`)
and `integration-phase-results.log` (`target/performance/attribution/integration-phase-results.log`);
the historical phase files and results remain unchanged. These measurements
move the next priorities: a warm batch runner can target the roughly 2.01 s
imports-only cost; broader checked-module reuse has a 4.55 s whole-frontend
ceiling that already includes those imports; proof evaluation and typed
construction have a 3.26 s incremental phase; renderer-only changes have at
most 1.24 s of rendering budget on this example. None of these ceilings
predicts what a redesign will save.

A static resolved-local-to-offset execution plan can affect binding and
lookup across checking/evaluation, but a narrow JVM profile observed only
18/218 leaf samples (8.3%) in `Env.runtimeValueOrNull` and
`Env.containsLocal`. A broader local binding/capture bucket also includes
mandatory proof checks and frame construction; those samples are not all
removable by replacing a lookup with a load. The packed-vector path still
copies on append, but the measured remaining render stage makes a rope a lower
priority than imports, declaration reuse and targeted proof-stage work.

### JVM profile guidance

One cold single-process JVM recording used `-Xmx2g`, JFR `settings=profile`,
stack traces exported to 128 frames, and the integrated source. Its raw CUDA
was 696,817 bytes with the same SHA-256 as the native pingpong output. It
contained 218 `raccoon-check` execution samples, so use these small-sample
shares as hotspot guidance, not precise projections of native CPU time.

| Inclusive region | Samples / share |
| --- | ---: |
| Local Env bind, lookup and capture (excluding global `apply(String)`) | 88 / 40.4% |
| Value, key, dependency and representation metadata | 93 / 42.7% |
| Samples in both regions | 38 / 17.4% |

The two inclusive shares overlap; there are 50 local-only and 55
metadata-only samples. In the local bucket, the direct lookup/membership
leaves `runtimeValueOrNull` (10 samples) and `containsLocal` (8) are a narrower
8.3% target. `bindRuntimeLocals` is 19 leaf samples (8.7%). Proof
canonicalization is also prominent: `Value.canonicalizeProof` has 19 leaf
samples (8.7%) and `Env.assertCanonicalProof` 7 (3.2%); a frame plan must keep
those checks. The metadata bucket includes `VApp`, `ValueKey`, `DepSet`,
`Sorts`, `StructEta`, codomain/determining-argument metadata and proof
canonicalization. It is broad and contains necessary typed work, not all
reducible overhead.

Top sampled leaves were `Value.canonicalizeProof` (19),
`Env.bindRuntimeLocals` (19), `Env.runtimeValueOrNull` (10),
`Interpreter.step` (9), `Env.containsLocal` (8), and `Interpreter.applyStep`
(7). The recording, 128-frame export, and bucket summary are retained as
`integration-jvm-pingpong.jfr` (`target/performance/attribution/integration-jvm-pingpong.jfr`),
`integration-jvm-execution.json` (`target/performance/attribution/integration-jvm-execution.json`),
and `integration-jvm-buckets.json` (`target/performance/attribution/integration-jvm-buckets.json`).
JVM sampled shares are not native subsystem times and are not added to the
native phase budgets.

### Gate evidence and reproduction

The standalone gate raw files were recorded at these ignored local paths:
slots results and summary (`target/performance/isolated-gates/slots-pingpong-native-results.json`),
metadata results and summary (`target/performance/isolated-gates/metadata-final-pingpong-results.json`),
string results (`target/performance/isolated-gates/string-delayed-key-benchmark.json`),
and eager-key prototype results (`target/performance/isolated-gates/string-eager-key-results.json`).
The original gate summaries, build logs and source commits were retained in
implementer worktrees; the integrated gate copies and raw final comparisons
were stored under `target/performance`, outside version control.

The original comparison used the following commands in the old combined
compiler/library checkout. They are historical instructions: this repository
no longer contains `scripts/benchmark-interpreter.py` or the GPU workload files.

```sh
scripts/build-graal-native.sh --parallelism=4 -J-Xmx3g
python3 scripts/benchmark-interpreter.py \
  --baseline target/performance/raccoon-dc29a91 \
  --candidate target/graalvm/raccoon \
  --repeats 3 --examples attention attention_pingpong attention_a3b \
  --mode raw --output target/performance/native-results.json
```

That run could substitute `target/performance/raccoon-baseline` for the
baseline. Its external GPU proof/compiler checks used `RACCOON="$PWD/target/graalvm/raccoon" gpu/check.sh`; the script reports
when the CUDA toolkit is unavailable rather than silently running its
register checks.
