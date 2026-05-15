# Namespaces

Namespaces give declarations dotted canonical names and provide scoped `open`.

```raccoon
namespace Data {
  inductive Tree : Type
   | leaf : Tree
   | node (left: Tree)(right: Tree) : Tree
}
```

This creates the globals:

- `Data.Tree`
- `Data.Tree.leaf`
- `Data.Tree.node`

Inductive constructors always live under the inductive head. A top-level `Nat` inductive therefore creates `Nat`,
`Nat.zero`, and `Nat.succ`.

## Name Resolution

Dotted names are resolved by the first segment.

- Locals win first. If `Nat` is a local, `Nat.zero` is a projection from that local.
- Otherwise, the current namespace is searched from most-specific to root.
- Then open aliases are searched.
- `_root_` bypasses locals, the current namespace, and opens.

Once the first segment resolves, the rest of the path is resolved inside that object. There is no backtracking across
opens. If `Tree` resolves to the current namespace's `Tree`, then `Tree.leaf` means child `leaf` of that object; it does
not fall back to another opened `Tree`.

## Opens

`open` exposes existing children of a namespace in the current open scope.

```raccoon
open Nat
open Nat.{zero, succ}
open Nat.{zero as z, succ as s}
open Nat.{*, -succ, succ as nsucc}
open _root_.Nat
```

Rules:

- `open Nat` is equivalent to `open Nat.{*}`.
- Opens are snapshots. Names added later to the namespace are not exposed by an earlier open.
- Open aliases can be used as prefixes when the opened object has children, so `open Data.{Tree as DTree}` allows
  `DTree.leaf`.
- Conflicting aliases in the same open scope are rejected at open time.
- `open _root_.Nat` bypasses current-namespace shadowing.
- Empty namespace blocks are only scopes. They do not create openable namespace objects until a declaration exists under
  them.

Open scopes are lexical. Command blocks and namespace blocks scope opens, but declarations made inside those blocks keep
their canonical names.

## Match Cases

Match case heads use normal global resolution:

```raccoon
match n with
| Nat.zero => Nat.zero
| Nat.succ p => p
```

To match by constructor short name from the scrutinee type, prefix the case head with `.`:

```raccoon
match n with
| .zero => Nat.zero
| .succ p => p
```

Opened aliases are globals for this purpose:

```raccoon
open Nat.{zero as z, succ as s}

match n with
| z => Nat.zero
| s p => p
```

Imports use dotted paths and are parsed, but module loading is not implemented yet, so imports are rejected during
elaboration.
