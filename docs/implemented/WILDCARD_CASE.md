# A wildcard case

Status: **implemented** (2026-10-01). A quality-of-life feature: `gpu/proofs/NOTES.md` F5's most repeated cost.

## 1. The feature

A match's last case may be `| _ => e`. It stands for one case for each reachable constructor that the earlier cases
do not name. Each such case binds its constructor's fields anonymously, and `e` is checked in each of them, under that
constructor's own refinement.

```raccoon
match s returning Fold.Empty(found) with
| Stmt.error message => False.elimP(Fold.consNotEmpty(message, found, h), Fold.Empty(found))
| _ => h
```

This replaces a 14-arm match whose arms are all `h` but one, which `gpu/proofs/` has more than twenty times. Library
code gains the same, for example a function on `Group` that cares about one constructor.

## 2. The rules

- **Last only.** A wildcard case is the last case of its match. Elsewhere, or twice, it is a parse error.
- **It stands for something.** It stands for the reachable constructors not yet named:
  - reachability is shared with coverage: apartness or a known-constructor
    clash proposes exclusion, but omission requires a checked local refutation
    of the constructor hypotheses. Otherwise the constructor remains reachable
    and the wildcard stands for it;
  - a wildcard that would stand for none is `RedundantCase`, located at it.
- **Each constructor checked separately.** `e` is checked once per constructor the wildcard stands for, in that
  case's environment and refinement, exactly as if the case had been written out with `_` for every field. So a
  wildcard over a constructor with a linear field is `LinearUnused` at the wildcard, as a written `_` would be.
- **The residual is the expansion.** The checked match has one case per constructor, each with the wildcard's body.
  Evaluation, conversion, the ledger and the termination checker see only written-out cases. Each expanded case's
  body is a fresh copy of `e`, with fresh node identities and locals, so every
  nested term in it is separate in each case, as in the written-out match.
- **Diagnostics name the constructor.** A failure inside an expanded case says which constructor it was checked for.

## 3. Why it is safe

The expansion is fixed by the scrutinee's family and the earlier cases. Each expanded case is checked by the existing
rules, so the wildcard adds no judgement. It saves only writing the cases. Coverage is the existing coverage check
applied to the expansion.

## 4. Implementation

- **Parser:** a case head `_` with no fields.
- **Surface and elaborated Core ASTs:** a separate optional final wildcard
  case. Checked residual matches contain only the expanded ordinary cases.
- **`MatchChecker`:** after resolving the family, replace the wildcard by one case per remaining reachable constructor,
  with fresh anonymous pattern variables, before checking the cases. `RedundantCase` is new.
- **Printing:** a residual prints the expansion.

## 5. Tests

- A wildcard over the rest: accepted, and it evaluates as the written-out match.
- A wildcard after every constructor: `RedundantCase`.
- A wildcard not last: a parse error.
- A wildcard in an indexed family, where some remaining constructor is apart from the scrutinee: it does not stand for
  that one.
- A wildcard under a refinement that differs per constructor: `e` must check in each.
- A wildcard over a constructor with a linear field: `LinearUnused`.
- A failure in one expansion: the diagnostic names the constructor.
- Rewriting one `gpu/proofs/` lemma (`Errors.keeps`) with a wildcard checks as before.

## 6. Decisions

1. **Last case only, and at most one**, rather than wildcards anywhere with first-match semantics: cases stay
   independent of their order.
2. **A redundant wildcard is an error.** One way to write a match.
3. **No nested patterns.** The wildcard covers whole constructors, not fields of a named one.
