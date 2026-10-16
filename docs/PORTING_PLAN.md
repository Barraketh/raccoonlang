# Ports onto the dependent type theory core

The starting point is `cleanup` at `2a4d7d8`. The donor is
`codex/library-safety-native-buffer` at `2295cdd`. Port semantic rules and
regressions onto the smaller implementation; do not restore deleted language
features to make a donor patch apply. The soundness checkpoint `acaf536` is a
useful reference, with later source-only corrections where applicable.

## Implementation order

- [x] **Remove opaque definitions first** (`4ed5e73`). Remove the modifier,
  AST flag, elaborator checks, and symbolic publication path. Every definition
  computes. Keep axioms as explicit assumptions in ordinary modules. Replace
  tests that need neutral values with parameters or axioms; delete tests of
  opacity itself. Reject `opaque def` and allow `opaque` as an identifier.
- [x] **Separate propositions from data universes** (`01f9817`). Give `Prop`
  its own sort tag. `Type` means data universe zero; `Type { level = u }`
  ranges only over data universes. Remove `Sort`, `imax`, conditional
  proposition classification, and level-collapse machinery. Preserve
  impredicative proposition-valued functions, proof irrelevance, reconstruction,
  and restricted elimination. Migrate the prelude, tests, examples, diagnostics,
  and documentation. Add proposition-valued eliminators such as `False.elimP`
  and `Eq.substP` where needed.
- [x] **Restrict family inversion and check family argument sizes**
  (`0c67487`). Only the root constructor-result versus scrutinee-type equation
  may invert a proposition family; structural descent clears that permission.
  Retain existing data-family injectivity (N1). Check parameter and index
  argument sizes as well as constructor fields, using the donor's elementwise
  universe bound. Do not add the stronger N2/N3 type-generativity principles.
- [x] **Repair constructor apartness and deferred equations** (`921fa3f`).
  A constructor clash requires one family at convertible common parameters.
  Heterogeneous constructor equations remain stuck. Retry a postponed equation
  only if a variable it reaches acquired a link; retain successful retries
  after later arguments establish the needed links.
- [x] **Require checked refutations before excluding constructors**
  (`acaf536`, with source-only corrections from `5f1eb15`). Build the private
  equality, empty proposition, and transport independently of the source
  prelude. Check local refutations in the original context, without speculative
  substitution links. Use the same certified reachability for coverage,
  unreachable-case diagnostics, known-constructor shortcuts, and empty-fiber
  large elimination. Disable certificate discharge while checking a
  certificate. Support constructor no-confusion and restricted existing N1;
  do not introduce N2/N3. Failed synthesis, checking, or quotation retains the
  case with an empty fallback store. Try independently usable index equations
  even when another coordinate cannot be quoted. Successful refinement links
  remain part of the trusted implementation.
- [x] **Bound repeated work on shared values** (`b2c6e74`). Add identity-based
  visited tracking to `Value.varsIn` and memoize completed materialization
  within one root invocation and one immutable equation store. Preserve
  traversal order and lazy classifier behavior; never share a memo across
  stores.
- [x] **Memoize declaration-time occurrence and positivity scans**
  (the source-only part of `12b7f86`). Keep `Absent`, `Positive`, and `Uniform`
  results local to a declaration/target/context, with conservative cycle
  handling. Do not restore the earlier per-value summary architecture. Validate
  shared closure graphs and negative positivity/uniformity cases; make no
  performance claim without measuring it.
- [x] **Port focused source conveniences** (`4281a80`, `9d58d35`,
  `6062c76`). Use an accumulator for linear-time `List.reverse`; accept blank
  and comment lines consistently inside lists of declarations, statements,
  constructors, and match cases; allow multiline `decreases`; improve missing
  qualified-name and arity diagnostics. Pin nested-match layout with tests.
- [x] **Remove avoidable host-stack limits** (source-only parts of
  `aa136d4`, `8b774b9`, `dcd501a`, `1899f70`). Use iterative printing, compute
  value metadata without recursively walking deep value chains, and evaluate
  tail positions in a loop. Report remaining evaluation stack exhaustion as
  `EvaluationTooDeep`, and allow CLI stack configuration. Keep one evaluator
  and the existing simple environment representation.

## Required validation

Completed on 2026-10-16: `sbt scalafmtAll validate` passed all 607 tests,
both bundled examples ran successfully, and the original Russell,
polymorphic-elimination, and standalone no-prelude contradiction reproducers
were rejected after migrating their sort syntax. A separate CLI probe verified
source-located `EvaluationTooDeep` JSON output with `--stack 2m`.

Regression tests must reject the axiom-free Russell contradiction, the
polymorphic proposition-constructor clash, and the proposition-to-data
elimination contradiction, including the standalone no-prelude proof. Positive
tests must preserve root proposition-index refinement and legitimate data-family
refinement. Certificate tests must exercise invalid proposals/proofs, unsupported
quotation, dependent coordinates, and operation without a source prelude.

Run focused suites while integrating each semantic stage, then `sbt validate`
and both bundled examples. Regenerate diagnostic snapshots only after reviewing
why their diagnostics changed. Shared-graph and deep-value tests should assert
behavior or bounded work rather than fragile wall-clock thresholds.

## Deliberately excluded

Packed/native representations, native buffers, GPU machinery, scope/lifetime/
linearity/sealing rules, prelude inventories and capability validations remain
removed. Evidence automation, new pair/destructuring/wildcard syntax, named
match equations, reflected typing, and Wire are outside this port. Defer stronger
N2/N3 type generativity, the broad `CoreEvaluator`/runtime-slot rewrite, and its
constructor caches until separately justified. None is needed for the repairs
above.

Checked exclusions do not turn this implementation into an independent small
kernel: conversion, successful refinement links, and the restricted nominal N1
premises remain trusted. The donor's nominal model is an informal relative
consistency argument, not a proof of either implementation.
