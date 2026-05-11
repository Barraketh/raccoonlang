# Typeclass Benchmarks

This document records the current typeclass-resolution high-watermark sweep for RaccoonJVM versus Lean no-prelude.

## Setup

Sampled on May 7, 2026 from branch `cur_main`, commit `3838a97`, on macOS 15.5 arm64.

- RaccoonJVM: Oracle GraalVM/OpenJDK 21.0.11, `JAVA_TOOL_OPTIONS=-Xss64m`
- Lean: `4.31.0-nightly-2026-05-07`, no-prelude generated files whose first command is `prelude`
- Repetitions: 1 per row
- Timeout: 120s per process
- Timing: process wall-clock time; RaccoonJVM rows include JVM startup
- Lean search budget: generated files set `maxHeartbeats = 0`, `synthInstance.maxHeartbeats = 0`, and `synthInstance.maxSize = 2000000000`

The benchmark generator follows the current Raccoon model where ordinary source applications provide every argument positionally, and instance search is requested explicitly with `derive[Goal]`. Generic Raccoon instances recover parameters through type-pattern captures in instance dependencies, such as `[inner: TC($A)]: TC(Wrap(A))`. The `implicit-arity` scenario uses a `Carrier($A0, ...)` dependency to keep the benchmark valid under that invariant.

## Results

### Width

| instances | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 30,000 | 2.509s | stack overflow (20.549s) |
| 40,000 | 3.020s | stack overflow (20.560s) |
| 50,000 | 3.322s | stack overflow (16.117s) |
| 60,000 | 3.804s | stack overflow (15.353s) |

### Fanout

| dependencies | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 10,000 | 3.811s | 53.561s |
| 15,000 | 4.542s | timeout (120.211s) |
| 20,000 | 5.674s | timeout (120.142s) |
| 25,000 | 6.432s | timeout (120.291s) |

### Chain

| depth | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 24 | 0.301s | 0.317s |
| 32 | 0.300s | 0.402s |
| 48 | 0.318s | 0.344s |
| 64 | 0.316s | 0.361s |

### Failures

| failing candidates | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 30,000 | 6.324s | stack overflow (33.294s) |
| 40,000 | 7.284s | stack overflow (27.438s) |
| 50,000 | 8.380s | stack overflow (27.904s) |
| 60,000 | 9.773s | stack overflow (27.263s) |

### Branching

| failing candidates per level | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 30,000 | 9.520s | stack overflow (33.787s) |
| 40,000 | 11.688s | stack overflow (28.061s) |
| 50,000 | 12.726s | stack overflow (28.587s) |
| 60,000 | 14.365s | stack overflow (29.017s) |

### Implicit Arity

| type parameters | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 512 | 2.131s | 1.420s |
| 768 | 3.736s | 2.750s |
| 1,024 | 6.207s | 4.893s |
| 1,536 | parser stack overflow (0.318s) | 11.954s |
| 2,048 | parser stack overflow (0.330s) | 24.764s |
| 4,096 | parser stack overflow (0.388s) | timeout (120.045s) |

### Explicit Control

| type parameters | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 512 | 1.414s | 1.001s |
| 768 | 2.189s | 1.821s |
| 1,024 | 3.248s | 3.363s |
| 1,536 | parser stack overflow (0.311s) | 8.596s |
| 2,048 | parser stack overflow (0.318s) | 18.314s |

### Repeat Query

Lean no-prelude timed out at 2,500 repeated queries, so larger Lean repeat-query rows were not rerun.

| repeated queries | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 1,000 | 0.501s | 11.962s |
| 1,500 | 0.416s | 39.801s |
| 2,000 | 0.454s | 90.841s |
| 2,500 | 0.480s | timeout (120.008s) |
| 5,000 | 0.623s | not run |
| 7,500 | 0.751s | not run |
| 10,000 | 0.861s | not run |

### Diamond

| layers | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 12 | 0.384s | 0.529s |
| 16 | 0.397s | 0.373s |
| 20 | 0.440s | 0.370s |
| 24 | 0.494s | 0.416s |
| 28 | 0.547s | 0.398s |

### Overlap

| overlapping candidates | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 30,000 | 8.244s | stack overflow (40.772s) |
| 40,000 | 9.980s | stack overflow (30.392s) |
| 50,000 | 11.093s | stack overflow (28.773s) |
| 60,000 | 12.370s | stack overflow (28.649s) |

### Local Instances

| global decoys | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 30,000 | 2.494s | stack overflow (22.412s) |
| 40,000 | 2.987s | stack overflow (17.856s) |
| 50,000 | 3.381s | stack overflow (15.952s) |
| 60,000 | 3.715s | stack overflow (16.131s) |

### Defeq

| alias depth | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 1,024 | 1.211s | 0.683s |
| 1,280 | 1.488s | 2.272s |
| 1,536 | 1.671s | 0.813s |
| 1,792 | interpreter stack overflow (1.985s) | 0.875s |
| 2,048 | interpreter stack overflow (2.375s) | 0.948s |

### Shared Fanout

| shared dependencies | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 5,000 | 3.150s | 16.270s |
| 10,000 | 4.575s | 60.573s |
| 12,500 | 5.218s | 92.115s |
| 15,000 | 5.855s | timeout (120.167s) |

### Instance Body

| body nodes | RaccoonJVM | Lean no-prelude |
|---:|---:|---:|
| 800 | 0.339s | 0.532s |
| 1,000 | 0.345s | 0.432s |
| 1,200 | 0.350s | 0.444s |
| 1,600 | parser stack overflow (0.241s) | 0.457s |
