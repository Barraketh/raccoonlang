# A3b attention client authoring feedback

`AttentionClient.rac` is a complete independent A3b client. It authors score masking and softmax arithmetic, the first-block correction and conditional rescaling, Q/K/V production, both score/PV issuer paths and their overlap schedule, the nested ring and tensor-memory allocations, role assembly, and the kernel builder. It does not import `encoding.Attention` or call its role/kernel helpers. The module has no evaluation body.

## What the API made clear

The cursor groups the emitter and linear resource state while arithmetic can preserve that state and return ordinary values. That fit the row pipeline: `loadRow` gives the client a real row value, callbacks choose the score/exponential arithmetic, and the cursor operations mark the transitions between loading, publishing, and storing. The correction role similarly spells out the zero-first-block path and the later vote/conditional-rescale path. The shared formulas remain visible in the client.

## Friction and remaining cost

The main cost is managing several simultaneous linear protocols. The issuer explicitly parks consumers and MMA sides, splits tickets to take one ring or buffer through an operation, then rebuilds the nested checkpoint state. The producer uses nested focus operations over query and K/V product states. These parts are much longer and harder to scan than Core's direct context/state threading; the machine interface provides a more uniform boundary but does not make the multi-resource schedule shorter or more readable here.

`open Core` and `open GpuMachine` collide on `Key`, so this client qualifies all machine operations. That is predictable and safe, though verbose. The client also had to learn that `loadRow` returns `(Machine Loaded, Row)` directly instead of Core's nested context/result shape. A porting example should call out this difference.

The role owner lifetime must remain distinct from each loop body's fresh cursor lifetime: correction states use `CorrectAt(x, m, ...)` across bodies parameterized by `n`. The first version used the fresh emitter lifetime for the token owner and failed to check. Keeping the original owner fixed resolved that error.

Raw CUDA comparison caught a substantive assembly-order mistake that typechecking alone did not: the first version finished producer resources in V/K/Q1/Q0 order and the MMA sides in S1/S0 order. Those finishers emit waits, so the generated output differed. Reordering cleanup to Q0/Q1/K/V and S0/S1 restored byte-for-byte output. This makes raw comparison valuable alongside the type and state checks.

## Comparison and verification

Core's `Corrected.kernel` is more concise and easier to read around multi-resource handoffs. The machine client makes each transition and arithmetic choice explicit, but the park/split/rebuild ceremony obscures the schedule enough that I would not call this client more ergonomic overall. The exact kernel-and-launcher AST comparisons passed for all four causal/output-type combinations. Independent raw rendering also matched the Core output byte-for-byte for all four: non-causal f32, causal bf16, causal f32, and non-causal bf16.

The fixture/static/comparison phases in `full/run.py` passed: 35 files checked (9 accepted, 26 intentionally rejected), followed by four A3b and four pair-GEMM matrix equality cases. The API designer handles retaining the generated artifacts, lowering mutations and repository validation; their results are recorded in `RESULTS.md`.
