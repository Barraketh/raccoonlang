# Documentation guide

The [language reference](language.md) describes accepted source syntax and
semantics. The [kernel reference](kernel.md) describes checking, conversion,
proofs, termination, and the trusted prelude. These are the current language
references; the [repository README](../README.md) covers running and building it.

Other maintained references are:

- [Finite native buffer programs](buffer-program.md): the checked source
  builders, linear ownership rules, and generic native executor.
- [Nominal model](nominal-model.md): the informal relative-consistency argument
  behind nominal Type families, with its assumptions and implementation limits.

## Design records and proposals

Files in [implemented](implemented/) record feature designs and their original
implementation decisions. Their status notes distinguish current rules from
superseded details. Descriptions of the state before a change, old test counts,
and benchmark measurements are historical evidence, not current guarantees.
Use the language and kernel references when a design record differs.

The former [lifetime design](implemented/LEMUR_ON_RACCOON.md) and
[scope-containment design](implemented/SCOPE_CONTAINMENT.md) are historical.
The current language has `Level` and `Kind` parameters, closure kinds, ordinary
type brands, and linear tokens. It has no `Lifetime` parameter, sort or closure
scope field, or `scope` term. Lexical namespaces, local bindings, and `open`
still have their ordinary scopes.

Files in [proposals](proposals/) describe unimplemented work. Named implicit
arguments, packed predecessor contexts and step summaries, interned word values,
bytecode evaluation, lazy type programs, and reflected typing are proposals.
Compact Nat successor prefixes and declaration-time positivity are already
implemented; they do not imply those broader proposals have been implemented.
Proposals that use the retired lifetime syntax are marked historical.

The [interpreter performance report](interpreter-performance.md) records older
measurements. It is not a benchmark of the current checkout. Its original
revision IDs and binary hashes identify those measurements; some revisions
belong to earlier histories. Its raw logs and binaries were local build
artifacts and are not distributed with this repository.

GPU library paths in design records refer to the external
[Lemur Raccoon repository](https://github.com/Barraketh/lemur-raccoon).
Compiler validation in this repository is `sbt validate`; external GPU gates
are separate library validation.
