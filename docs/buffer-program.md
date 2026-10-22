# Finite native buffer programs

`buffer/Program.rac` is an ordinary Raccoon library for building finite programs over byte buffers. It is independent of
GPU modules. A checked program is immutable; `Buffer.run` validates and executes its generic numeric instruction stream
through one small trusted builtin. Each invocation allocates private buffers and register banks and returns immutable
`Buffer.Result` values. It does not expose host arrays, handles, callbacks, or mutable state to the evaluator.

The public builder uses `Buffer.build`, `withInput`, `withScratch`, and `withOutput`. `Buffer.build` creates a fresh
root brand and a linear access token. A context carries that token together with the current control-flow frame, so
only the builder can emit instructions or move access into a child frame. Branch and repeat callbacks receive a fresh
frame token and a `BufferAccess.View` describing its ancestry. A parent scalar can be copied into a child frame with
`Buffer.lift32` or `Buffer.lift64`; nested views compose with `BufferAccess.compose`. Scalar operands must match both
the builder root and the context frame, so a child snapshot cannot be used with its parent context or another builder.

Each buffer allocation has a separate abstract brand, a sealed handle, and, when writable, a matching linear owner.
All buffers are statically allocated for the whole invocation, including allocations described from inside a loop
builder. Loads and stores require the matching owner for mutable buffers; output export consumes its owner, while
scratch release consumes its owner. Extent getters return only immutable size metadata, so a closure that reads an
extent may outlive its owner. It carries no authority to load or store. `Fixed` lets an `ifThenElse` or
`repeat32`/`repeat64` body thread fieldless owners through both arms or every iteration. Mutable `Reg32`/`Reg64` values
are program-global slots tied to the builder root and can be captured as program state. They are not `Fixed` state.
`getReg32` and `getReg64` produce immutable snapshots tagged with the current frame. Read-only `inputBytes`,
`scratchBytes`, and `outputBytes` expose extents without exposing buffer IDs or storage.

Buffers are allocated in builder order and outputs are returned in that same order. Buffer storage and scalar banks are
zero-initialized once per run. Allocations described from inside a loop builder still describe one static allocation
for the whole run; the loop does not reallocate or clear them on each trip. Input byte lists must match the declared
input extents and contain values from 0 through 255. A later run cannot mutate its inputs or an earlier result.

The instruction set provides unsigned 32- and 64-bit loads/stores, wrapping add/subtract/multiply and bit operations,
unsigned division/remainder, comparisons, U32-to-U64 extension, conditional blocks, and fixed-on-entry repeats. Buffer
offsets are byte offsets. Byte and 16-bit stores reject values that do not fit; wider stores write their low-order
bytes. Repeat counts are read once when the repeat begins, and the loop index is read-only to the body. Control flow is
structured and finite: there are no arbitrary jumps or unstructured control-flow edges, user fuel values, or hidden
instruction-count limit.
Malformed programs, invalid arithmetic, out-of-bounds access, invalid input, and implementation resource limits return
a `Buffer.Result.failure` code instead of exposing partially mutable storage.

The current bounded implementation limits a program to 1,000,000 encoded words and 200,000 instructions, each scalar
register bank to 65,536 entries, 256 buffers, 64 MiB per buffer, and 256 MiB total private storage. Combined input and
output wire bytes are limited to 16 MiB; converting output bytes to nested ordinary Raccoon lists has a stricter 256 KiB
limit to avoid constructing millions of `Nat` and `List.cons` values. These limits are independent of loop termination.

[`buffer/TokenProbe.rac`](../buffer/TokenProbe.rac) is a small client using only the default Prelude and this library.
It builds one immutable increment program, runs it on two inputs, then reuses it on the first input. The test checks
the concrete results `42`, `10`, and `42`; [`buffer/ReductionProbe.rac`](../buffer/ReductionProbe.rac) demonstrates
loop-carried reduction state and a zero-trip branch. The source-facing bridge and native executor are covered by
`BufferProgramSourceTests`, `NativeBufferProgramTests`, and `NativeBufferBuiltinsTests`.

The trusted surface added for this library is only `Buffer.Native.executeEncoded`, which takes generic encoded words
and byte lists and returns a status plus output lists. The type, compiler, linear ownership API, and higher-level
combinators remain ordinary checked Raccoon code. The current source result representation uses nested lists rather
than a packed immutable-byte codec, hence the separate source-output marshalling limit.
