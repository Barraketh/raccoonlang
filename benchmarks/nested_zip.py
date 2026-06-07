#!/usr/bin/env python3
"""Generate and run the nested dependent Vec.zip benchmark.

The benchmark builds a chain

    z1 := zip(v, v)
    z2 := zip(v, z1)
    ...
    zN := zip(v, zN-1)
    consume(zN)

The final consume(...) keeps the full nested indexed-vector type live, so the
program stresses parsing, elaboration, type-pattern inference, and dependent
typechecking without spending time constructing a runtime vector value.
"""

from __future__ import annotations

import argparse
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SCALA_VERSION = "2.13.18"
ROARING_BITMAP_VERSION = "1.3.0"
DEFAULT_RACCOON_SIZES = [0, 100, 400, 800, 1600, 6400, 12800, 51200]
DEFAULT_LEAN_SIZES = [0, 100, 400, 800, 1600, 3200, 6400]


def parse_sizes(value: str) -> list[int]:
    try:
        sizes = [int(part.strip()) for part in value.split(",") if part.strip()]
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"invalid size list: {value}") from exc
    if any(size < 0 for size in sizes):
        raise argparse.ArgumentTypeError("sizes must be non-negative")
    return sizes


def parse_kinds(value: str) -> list[str]:
    return [part.strip() for part in value.split(",") if part.strip()]


def raccoon_source(size: int, transparent_zip: bool) -> str:
    unfold = "def" if transparent_zip else "opaque def"
    lets = []
    previous = "v"
    for idx in range(1, size + 1):
        lets.append(f"  let z{idx} := zip(v, {previous})")
        previous = f"z{idx}"

    return f"""inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(Level.max(Level.one, u))
 | nil {{A: Sort($u)}} : Vec(A, Nat.zero)
 | cons {{A: Sort($u)}} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))

inductive Pair (A: Sort($u1))(B: Sort($u2)): Sort(Level.max(u1, u2))
 | mk(a: $A in Sort($u1))(b: $B in Sort($u2)): Pair(A, B)

{unfold} zip(va: Vec($A, $n))(vb: Vec($B, n)): Vec(Pair(A, B), n) decreases measure(n) := {{
  let ResType := Vec(Pair(A, B), n)
  match va returning ResType with
  | Vec.nil => Vec.nil(Pair(A, B))
  | Vec.cons va0 a => {{
    match vb returning ResType with
    | Vec.cons vb0 b => Vec.cons(Pair(A, B), zip(va0, vb0), Pair.mk(a, b))
  }}
}}

def consume (w: Vec($A, $n)): Nat := Nat.zero

def bench (n: Nat)(v: Vec(Nat, n)): Nat := {{
{chr(10).join(lets)}
  consume({previous})
}}
"""


def lean_source(size: int, raised_limits: bool) -> str:
    lets = []
    previous = "v"
    for idx in range(1, size + 1):
        lets.append(f"  let z{idx} := zip v {previous}")
        previous = f"z{idx}"

    options = ""
    if raised_limits:
        options = "set_option maxRecDepth 10000\nset_option maxHeartbeats 0\n\n"

    # Lean uses Type u rather than Sort u here because this universe-polymorphic
    # inductive is rejected when the result universe may be Prop.
    return options + f"""universe u v

inductive Vec (A : Type u) : Nat -> Type u where
  | nil : Vec A 0
  | cons : Vec A n -> A -> Vec A (Nat.succ n)

inductive Pair (A : Type u) (B : Type v) : Type (max u v) where
  | mk : A -> B -> Pair A B

def zip {{A : Type u}} {{B : Type v}} {{n : Nat}} : Vec A n -> Vec B n -> Vec (Pair A B) n
  | .nil, .nil => .nil
  | .cons xs a, .cons ys b => .cons (zip xs ys) (.mk a b)

opaque consume {{A : Type u}} {{n : Nat}} (_w : Vec A n) : Nat := 0

def bench (n : Nat) (v : Vec Nat n) : Nat :=
{chr(10).join(lets)}
  consume {previous}
"""


def write_file(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents)


def generate_raccoon(out_dir: Path, sizes: Iterable[int]) -> None:
    for size in sizes:
        write_file(out_dir / f"nested_zip_opaque_{size}.rac", raccoon_source(size, transparent_zip=False))
        write_file(out_dir / f"nested_zip_transparent_{size}.rac", raccoon_source(size, transparent_zip=True))


def generate_lean(out_dir: Path, sizes: Iterable[int]) -> None:
    for size in sizes:
        write_file(out_dir / f"nested_zip_default_{size}.lean", lean_source(size, raised_limits=False))
        write_file(out_dir / f"nested_zip_raised_{size}.lean", lean_source(size, raised_limits=True))


def find_dependency_jar(group_path: str, artifact: str, version: str) -> Path:
    home = Path.home()
    filename = f"{artifact}-{version}.jar"
    ivy_group = group_path.replace("/", ".")
    candidates = [
        home
        / "Library/Caches/Coursier/v1/https/repo1.maven.org/maven2"
        / group_path
        / artifact
        / version
        / filename,
        home
        / ".cache/coursier/v1/https/repo1.maven.org/maven2"
        / group_path
        / artifact
        / version
        / filename,
        home
        / ".ivy2/cache"
        / ivy_group
        / artifact
        / "jars"
        / filename,
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate

    search_roots = [home / "Library/Caches/Coursier/v1", home / ".cache/coursier/v1", home / ".ivy2/cache"]
    for root in search_roots:
        if not root.exists():
            continue
        matches = list(root.glob(f"**/{filename}"))
        if matches:
            return matches[0]

    raise FileNotFoundError(f"could not find {filename}; run `sbt -no-colors compile` or pass --classpath")


def find_scala_library() -> Path:
    return find_dependency_jar("org/scala-lang", "scala-library", SCALA_VERSION)


def find_roaring_bitmap() -> Path:
    return find_dependency_jar("org/roaringbitmap", "RoaringBitmap", ROARING_BITMAP_VERSION)


def default_classpath() -> str:
    classes = REPO_ROOT / "target/scala-2.13/classes"
    if not classes.exists():
        raise FileNotFoundError("missing target/scala-2.13/classes; run `sbt -no-colors compile` first")
    jars = [str(find_scala_library()), str(find_roaring_bitmap())]
    return ":".join([str(classes), *jars])


@dataclass
class RunSummary:
    name: str
    size: int
    status: str
    median: float | None
    minimum: float
    maximum: float
    reps: int
    stderr_tail: str


def run_once(command: list[str], timeout: float | None) -> tuple[int, float, str]:
    start = time.perf_counter()
    try:
        result = subprocess.run(
            command,
            cwd=REPO_ROOT,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            timeout=timeout,
        )
        elapsed = time.perf_counter() - start
        return result.returncode, elapsed, result.stderr.decode(errors="replace")
    except subprocess.TimeoutExpired as exc:
        elapsed = time.perf_counter() - start
        stderr = ""
        if exc.stderr:
            stderr = exc.stderr.decode(errors="replace")
        return 124, elapsed, stderr + f"\ntimeout after {timeout}s"


def benchmark_command(name: str, size: int, command: list[str], reps: int, timeout: float | None) -> RunSummary:
    timings: list[float] = []
    stderr_tail = ""
    for rep in range(reps):
        code, elapsed, stderr = run_once(command, timeout)
        stderr_tail = "\n".join(line for line in stderr.strip().splitlines()[-4:] if line.strip())
        if code != 0:
            return RunSummary(name, size, f"exit {code}", None, elapsed, elapsed, rep + 1, stderr_tail)
        timings.append(elapsed)

    return RunSummary(
        name=name,
        size=size,
        status="ok",
        median=statistics.median(timings),
        minimum=min(timings),
        maximum=max(timings),
        reps=reps,
        stderr_tail=stderr_tail,
    )


def reps_for_size(size: int, small_reps: int, large_reps: int, large_threshold: int) -> int:
    return large_reps if size >= large_threshold else small_reps


def print_summary(summary: RunSummary) -> None:
    if summary.median is None:
        extra = f" stderr={summary.stderr_tail!r}" if summary.stderr_tail else ""
        print(f"{summary.name:22s} {summary.size:6d} {summary.status:8s} time={summary.minimum:.4f}s{extra}")
    else:
        print(
            f"{summary.name:22s} {summary.size:6d} ok       "
            f"median={summary.median:.4f}s min={summary.minimum:.4f}s max={summary.maximum:.4f}s reps={summary.reps}"
        )


def run_raccoon_jvm(args: argparse.Namespace, out_dir: Path) -> None:
    classpath = args.classpath or default_classpath()
    for kind in args.raccoon_kinds:
        for size in args.raccoon_sizes:
            reps = reps_for_size(size, args.reps, args.large_reps, args.large_threshold)
            path = out_dir / f"nested_zip_{kind}_{size}.rac"
            command = [args.java, "-cp", classpath, "com.raccoonlang.Main", "--prelude", args.prelude, str(path)]
            print_summary(benchmark_command(f"raccoon-jvm-{kind}", size, command, reps, args.timeout))


def run_raccoon_native(args: argparse.Namespace, out_dir: Path) -> None:
    native_bin = Path(args.native_bin)
    if not native_bin.exists():
        raise FileNotFoundError(f"native binary not found: {native_bin}")
    for kind in args.raccoon_kinds:
        for size in args.raccoon_sizes:
            reps = reps_for_size(size, args.reps, args.large_reps, args.large_threshold)
            path = out_dir / f"nested_zip_{kind}_{size}.rac"
            command = [str(native_bin), str(path)]
            print_summary(benchmark_command(f"raccoon-native-{kind}", size, command, reps, args.timeout))


def run_lean(args: argparse.Namespace, out_dir: Path, raised_limits: bool) -> None:
    mode = "raised" if raised_limits else "default"
    for size in args.lean_sizes:
        reps = reps_for_size(size, args.reps, args.large_reps, args.large_threshold)
        path = out_dir / f"nested_zip_{mode}_{size}.lean"
        command = [args.lean, str(path)]
        print_summary(benchmark_command(f"lean-{mode}", size, command, reps, args.timeout))


def expand_runners(runners: list[str]) -> list[str]:
    if "all" not in runners:
        return runners
    return ["jvm", "native", "lean-default", "lean-raised"]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--runner",
        action="append",
        choices=["generate", "jvm", "native", "lean-default", "lean-raised", "all"],
        default=[],
        help="benchmark runner to execute; may be repeated",
    )
    parser.add_argument("--out-dir", type=Path, default=Path("/tmp/raccoonlang-benchmarks/nested-zip"))
    parser.add_argument("--raccoon-sizes", type=parse_sizes, default=DEFAULT_RACCOON_SIZES)
    parser.add_argument("--lean-sizes", type=parse_sizes, default=DEFAULT_LEAN_SIZES)
    parser.add_argument("--raccoon-kinds", type=parse_kinds, default=["opaque", "transparent"])
    parser.add_argument("--reps", type=int, default=5, help="repetitions for sizes below --large-threshold")
    parser.add_argument("--large-reps", type=int, default=3)
    parser.add_argument("--large-threshold", type=int, default=51200)
    parser.add_argument("--timeout", type=float, default=180.0)
    parser.add_argument("--java", default="java")
    parser.add_argument("--classpath", help="JVM classpath for com.raccoonlang.Main")
    parser.add_argument("--prelude", default=str(REPO_ROOT / "src/main/resources/Init/TestPrelude.rac"))
    parser.add_argument("--native-bin", default=str(REPO_ROOT / "native/target/scala-2.13/raccoon-release-full"))
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()

    runners = expand_runners(args.runner or ["generate"])
    invalid_kinds = sorted(set(args.raccoon_kinds) - {"opaque", "transparent"})
    if invalid_kinds:
        raise ValueError(f"unknown raccoon kind(s): {', '.join(invalid_kinds)}")

    args.out_dir.mkdir(parents=True, exist_ok=True)
    if any(runner in runners for runner in ["generate", "jvm", "native"]):
        generate_raccoon(args.out_dir, args.raccoon_sizes)
    if any(runner in runners for runner in ["generate", "lean-default", "lean-raised"]):
        generate_lean(args.out_dir, args.lean_sizes)

    if runners == ["generate"]:
        print(f"generated benchmark sources in {args.out_dir}")
        return 0

    for runner in runners:
        if runner == "generate":
            continue
        if runner == "jvm":
            run_raccoon_jvm(args, args.out_dir)
        elif runner == "native":
            run_raccoon_native(args, args.out_dir)
        elif runner == "lean-default":
            run_lean(args, args.out_dir, raised_limits=False)
        elif runner == "lean-raised":
            run_lean(args, args.out_dir, raised_limits=True)
        else:
            raise ValueError(f"unknown runner: {runner}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (FileNotFoundError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
