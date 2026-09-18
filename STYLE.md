# Raccoon code style

These are project-specific engineering rules. They take precedence over
generic style advice.

## Design for the clean end state

Start by asking what the correct, simplest design is. Optimize for a clean and
obviously correct codebase, not for the smallest patch or compatibility with
old internal behavior. There is one current implementation and one current
rule; do not preserve parallel paths solely for backwards compatibility.

## Prefer locality

A function called from only one place should usually remain at that call site.
Extract a helper when it does at least one of the following:

- hides a representation detail behind a stable boundary;
- names a domain concept used in more than one place;
- removes actual duplication;
- makes complex logic materially easier to read;
- enables focused testing of otherwise inaccessible behavior.

A single-call helper is appropriate when it enforces a boundary or invariant.
Otherwise, wait for a second use or a clearer abstraction.

## Prefer explicitness

Avoid default parameters. Callers should make meaningful choices visible.

Keep one authoritative implementation of each semantic rule. Shared
structural traversals, classification tables, and validation rules should not
be copied into consumers that can drift independently.

## Formatting

Do not add vertical space that does not improve readability. Keep parameters,
constructor arguments, and short pattern-match bodies on one line when they
fit; Scalafmt enforces the line limit. Long method chains may be split one call
per line when that makes the sequence easier to scan.

Run `sbt validate` before considering a change complete.
