# Machine cursors for the full client tests

`Machine.rac` is a second API experiment for A3b attention and persistent pair
GEMM. It imports the shared checked lowering engine in `encoding.Lowering`.
`encoding.Core` is now a facade over that engine. Its namespace remains `Core`,
so existing clients and the new API share the sealed native types and one
implementation of CUDA instructions, allocations and their safety conditions.
This is an alternative client interface, not an independent CUDA backend.

Open `Core` and `Cuda` for their types and pure value arithmetic, then selectively
open `GpuMachine.{Machine, Ticket}`. Use qualified cursor operations, optionally
with `open _root_.{GpuMachine as M}` for `M.loadRow(...)` and similar calls.
Opening both complete namespaces is ambiguous. `Machine(l, g, S)` owns an emitter in block
`l`, a resource state `S`, and the native evidence that `S` is fixed. It is linear
and includes both lifetimes. Values and registers retain their original scope
and grain types. An operation consumes the cursor and returns the next cursor;
an operation that produces data returns `(cursor, value)`.

For example, a row progresses through `RowsAt`, `Scored`, `Loaded`, `Probs`,
then back to `RowsAt`. `loadRow(awaitScores(row, buffer), buffer)` returns the
loaded cursor and actual row registers. Arithmetic such as `get(row, maximum)`
preserves that cursor's resource state. `mapRow` and `writeProbs` call the
client's arithmetic on every chunk. The callback receives a cursor with unit
state while the library preserves or consumes the surrounding row authority.

`focusLeft` and `focusRight` act on one component of a product state. For more
involved dependencies, `park(cursor)` returns an empty cursor and a linear
`Ticket(S)`; `use(empty, ticket)` resumes that state. `join(cursorA, ticketB)`
forms a product cursor; `split` reverses it. `pairTickets` and `splitTicket`
assemble or disassemble parked products. A ticket owns a resource state and
contains no emitter, so parking cannot duplicate emission authority.

`repeat`, `repeatFrom`, `when`, persistent tile loops and half-chunk loops
obtain fixed-state evidence from the cursor. `peeled` still needs an explicit
result state type, but obtains its witness from the first callback's result.
The generator runs that first callback once, then generates the remaining
loop with the resulting witness. The cursor itself is never asserted fixed.

Allocation builders retain the original scoped callback structure and consume
all endpoints before close. They replace `Ctx` with a cursor with unit state;
allocation callbacks still return `(cursor, X)`, including reclaimed tensor
memory authority. Role and election callbacks return only the cursor.
`leaderIssue` accepts the pair ring's consumer and the pair accumulator ring's
producer. Its callback runs only on the leader, cannot capture another linear
endpoint, and receives scoped `Leader` authority. The native implementation
continues to reject writes to outer registers in that branch.

The tests must compare every generated kernel and launcher with the real Core
client, exercise invalid protocol orders, resource identities, ownership,
scopes, grain and leader restrictions, and compile the generated CUDA. Successful
ports do not by themselves establish better ergonomics or easier proofs. Luna's
feedback and the resulting client code are part of the result.
