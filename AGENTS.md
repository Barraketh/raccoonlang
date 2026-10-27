# Engineering workflow

Own the discovery and resolution of unnecessary complexity during design,
implementation, and review. Do not wait for the user to identify redundant checks,
parameters, state, or work. Passing tests alone does not establish design quality.

## Contracts beside the code

- Keep semantic contracts beside the representation or function that owns them.
  Record non-obvious preconditions, guarantees, and relevant effects or resource
  obligations. Put shared representation invariants on the representation rather
  than repeating them on every function.
- Explain non-obvious reasons a caller satisfies a callee's requirements at the
  call site. Recover actual caller relationships from the code; do not maintain
  handwritten caller lists or a separate authoritative contract map.
- Treat comments as claims to verify against construction paths and callers.
  Existing contracts are a starting point, not a ceiling on guarantees that review
  may discover. Do not turn assumptions into guarantees merely by documenting them.

## While designing and writing code

- Before changing a function, inspect its contract, callers, and relevant consumers.
  Establish where inputs become trusted, which operations preserve their invariants,
  and which operations can invalidate them.
- Reuse guarantees and information already established by construction or callers.
  Validate new inputs at the appropriate boundary, and check resource growth where
  it occurs. Verify that inherited guarantees still apply in the current context.
- Give each consistency obligation a clear owner. Derive metadata where the result
  is constructed when practical; justify redundant inputs or cached state by a
  concrete need, including performance where relevant.
- Update contracts and implementation together. When requirements or guarantees
  change, revisit affected callers and consumers.

## Required per-function review

Explicitly review every new or materially changed function, including nested
helpers, plus existing functions whose assumptions the change affects. Keep a
lightweight inventory for the task so functions are not skipped. For each function:

1. Trace actual callers, including indirect uses and callbacks where applicable.
   Determine which invariants and information each caller establishes, where they
   are established, and which hold at every call site.
2. Look beyond the documented contract. Identify guarantees the callers establish
   that the function unnecessarily revalidates, re-derives, reconstructs, or computes
   again. Identify already available information that could eliminate work.
3. Examine every parameter and stored field. Determine whether it is needed, can be
   derived without meaningful extra cost, or makes callers maintain redundant
   bookkeeping or coordinate values that belong inside the operation.
4. Examine output guarantees and consumers. Determine whether stronger guarantees
   established here can simplify downstream code, and whether the function still
   serves a useful purpose after simplification.
5. Record a concrete finding or a brief reason to retain the design. Support any
   removed validation with an argument covering the reachable call paths; preserve
   checks that establish new guarantees or enforce the current operation's limits.

## Required cross-function review

Perform a separate review of complete affected flows, including relevant unchanged
code. Per-function review does not replace this pass.

- Find repeated validation, derivation, bookkeeping, traversal, conversion, and
  reconstruction across functions.
- Look for invariants or useful information that should be established at a shared
  entry or construction boundary, then preserved and reused below it.
- Examine whether responsibility is split across callers and callees unnecessarily,
  and whether multiple implementations of one operation have necessary differences.
- Propose coherent changes across the affected code. Moving a check or extracting a
  helper is useful only when the resulting responsibilities and callers are simpler.

## Completion

- Resolve routine engineering findings without delegating their discovery or cleanup
  decisions to the user. Raise substantive semantic or architectural choices when
  needed.
- Review the resulting design, not only whether each individual fix preserves
  behavior. Revisit affected per-function reviews after interface changes and repeat
  the cross-function review where responsibilities move. Remove obsolete caller
  bookkeeping and update contracts in the same change.
- Run appropriate behavioral checks and performance checks when the change affects
  relevant costs. Keep review coverage and finding dispositions available for the
  task; summarize substantive changes, evidence, and remaining choices at handoff.
