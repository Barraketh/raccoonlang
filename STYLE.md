# Raccoon Code Style Guide

This guide records local engineering preferences for future maintainers and
coding-agent sessions. Prefer these rules over generic style advice when they
conflict.

## NO HACKS

I cannot emphasize this enough. Start every change with the question "what is the perfect design". Then implement the
perfect design. Do not worry about backwards compatibility - only correctness and code cleanliness. The objective is
not "smallest change possible for this specific change" - the objective is "the cleanest possible codebase"

## Prefer Locality

Functions that are only called from one place are a code smell and should
usually be inlined.

Extract a helper only when it earns its name by doing at least one of these:

- hides a real representation detail behind a stable boundary;
- names a domain concept that appears in more than one place;
- removes duplication across multiple call sites;
- isolates complex logic enough that the caller becomes materially easier to
  read;
- supports focused tests for behavior that would otherwise be hard to exercise.

Single-call helpers are acceptable when they are enforcing a boundary or
protecting an invariant. Otherwise, keep the logic at the call site until
another call site or a clearer abstraction appears.

## Never preserve two different ways to do the same thing for backwards compatibility

I am the only user of this project. The goals are correctness, simplicity and clean code. If you
change a behavior that breaks tests, simply fix the tests.

## Prefer explicitness

Avoid default parameters - they make caller code harder to reason about

## Do not add extra newlines unless necessary for clarity

Keep function parameters / class args on the same line. Same with pattern match bodies if fits on single line.
Scalafmt will make sure the lines don't get too long.  The only exception is chained methods - if we have a long chain
of a.foo().bar().baz(), those I often like on separate lines unless the method names are very short 

## NO HACKS

I cannot emphasize this enough. Start every change with the question "what is the perfect design". Then implement the
perfect design. Do not worry about backwards compatibility - only correctness and code cleanliness. The objective is
not "smallest change possible for this specific change" - the objective is "the cleanest possible codebase"
