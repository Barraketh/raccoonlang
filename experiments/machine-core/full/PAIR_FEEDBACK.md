# Pair GEMM client feedback

The machine-carrying API does successfully make the fixed state travel with its emitter and prevents a client from supplying `Fixed` evidence. The allocation callbacks are also close to the original lifetime structure, and `forPairTiles`, `forOwnedPairTiles`, and `forHalfChunks` keep the ownership and coordinate evidence local without asking the client to reconstruct a `Fixed` witness.

The main ergonomic cost is explicit state framing around operations that act on one side of a product. Each transition that touches just the consumer or accumulator has to use `focusLeft` or `focusRight`, and combining independently acquired consumer/producer states takes `park`, `pairTickets`, and `use`. Finishing both halves also needs explicit unit dropping. `focusLeftValue` helps for data-returning loads, but one focused state/value operation does not cover the simple state transitions. A scoped pair map with callbacks for both halves, plus focused value and unit-collapsing operations, would keep client code closer to its domain logic without exposing `Fixed`.

`leaderIssue` keeping the leader proof and resource sides confined to the selected CTA is a useful boundary. The nested election in the issuer is needed to select the issuing lane after the leader branch has selected the CTA.
