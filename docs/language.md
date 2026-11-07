# Language conveniences

Surface features that cost the kernel nothing: each is checked by turning it into terms or messages the checker
already knows. [kernel.md](kernel.md) has the kernel's rules.

## Type mismatches

A mismatch names the expected type as the source writes it, where the checker has that, the actual type, and the first
pair of subterms where the two differ:

```text
Type mismatch: expected type: Eq(Bool, Machine.Build.isGroup(Machine.Lists.get(C, 3)), Bool.true), actual: Eq(Bool, Bool.true, Bool.true); first difference: expected Bool.false, actual Bool.true; the expected type evaluates to Eq(Bool, Bool.false, Bool.true)
```

- **Expected type as written.** For a term checked against a stated type (a `let` 's, a definition's or a lambda's
  result, a match's `returning`), that type. For an argument, its parameter's type, with the earlier parameters shown
  as the call's arguments and the signature's captures as their values; an argument or value longer than 40 characters
  shows as the parameter's or capture's own name. Otherwise, the expected type's value.
- **Actual type**, as a value.
- **First difference.** The first pair of subterms that do not convert: through applications of one head, the first
  argument pair; through kernel lists, the first element pair, or what follows the elements they share; through
  function types and local lambdas of as many binders, their codomains or bodies on shared variables; through
  projections of one field, their bases; through stuck matches of one code, the first pair of captured values. Two
  short values, such as numerals, that are arguments of an application, are shown with it. Omitted when the whole
  types are the pair.
- **The expected type as it evaluates**, when it prints differently from the written one.

A value prints whole up to 240 characters. A longer one prints along the path to the difference: every other argument
longer than 72 characters as `…`, a list's three elements before the one that differs and none after it, and the
differing part in outline; every part is clipped at 600 characters. So a mismatch in a large type stays a few hundred
characters, where printing the normal forms whole took tens of kilobytes. Messages are computed when read, so a
mismatch that the checker catches and recovers from costs nothing to describe.
