# Historical scope-containment design

This design describes Raccoon's removed `Lifetime` and lifetime-scope feature.
Its syntax, rules, examples, and safety claims are historical; current Raccoon
has no lifetime type, sort-scope field, or `scope` term. See the
[language reference](../language.md) and [kernel reference](../kernel.md) for
the current language.

The full historical document is retained in the compiler repository's Git
history at baseline `81759785`. In a clone containing that commit, view it with:

```sh
git show 81759785:docs/implemented/SCOPE_CONTAINMENT.md
```
