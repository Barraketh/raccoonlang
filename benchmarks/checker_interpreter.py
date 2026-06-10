#!/usr/bin/env python3
"""Generate and run generic typechecker/interpreter benchmarks.

This suite complements typeclass_resolution.py. The scenarios stress conversion,
local contexts, dependent match refinement, type-pattern capture, universe levels,
projection, and transparent evaluation. Lean files are generated for the same
stress shape and are intended to be run with the active Lean nightly toolchain.
"""

from __future__ import annotations

import argparse
import csv
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SCALA_VERSION = "2.13.18"
ROARING_BITMAP_VERSION = "1.3.0"

ALL_SCENARIOS = (
    "alias-defeq",
    "let-context",
    "app-spine",
    "lambda-binders",
    "match-width",
    "dependent-match",
    "pattern-capture",
    "projection-chain",
    "transparent-chain",
    "universe-max",
)

DEFAULT_SIZES = {
    "alias-defeq": [0, 128, 512, 1024],
    "let-context": [0, 1000, 5000, 10000],
    "app-spine": [0, 1000, 5000, 10000],
    "lambda-binders": [0, 128, 512, 1024],
    "match-width": [0, 128, 512, 1024],
    "dependent-match": [0, 100, 500, 1000],
    "pattern-capture": [0, 16, 64, 128, 256],
    "projection-chain": [0, 128, 512, 1024],
    "transparent-chain": [0, 1000, 5000, 10000],
    "universe-max": [0, 16, 64, 128, 256],
}

SCENARIO_DESCRIPTIONS = {
    "alias-defeq": "definitional equality through transparent aliases",
    "let-context": "large local environments and checked let bodies",
    "app-spine": "repeated checked applications under a growing body",
    "lambda-binders": "large Pi/lambda binders and full application",
    "match-width": "wide neutral match exhaustiveness and branch checking",
    "dependent-match": "dependent equality-style match refinement",
    "pattern-capture": "Raccoon type-pattern capture / Lean implicit parameter recovery",
    "projection-chain": "nested structure projections and selector typing",
    "transparent-chain": "transparent top-level unfolding and runtime evaluation",
    "universe-max": "large universe-parameter and Level.max terms",
}


def parse_sizes(value: str) -> list[int]:
    try:
        sizes = [int(part.strip()) for part in value.split(",") if part.strip()]
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"invalid size list: {value}") from exc
    if any(size < 0 for size in sizes):
        raise argparse.ArgumentTypeError("sizes must be non-negative")
    return sizes


def raccoon_header() -> str:
    return """inductive BenchUnit : Type
 | unit : BenchUnit

"""


def raccoon_nat() -> str:
    return """inductive BenchNat : Type
 | zero : BenchNat
 | succ (_: BenchNat) : BenchNat

"""


def raccoon_base() -> str:
    return """inductive Base : Type
 | mk : Base

"""


def raccoon_wrap() -> str:
    return """inductive Wrap (A: Type) : Type
 | mk (x: $A of Type) : Wrap(A)

"""


def raccoon_box() -> str:
    return """struct Box (A: Type) : Type
 | mk (value: $A of Type) : Box(A)

"""


def raccoon_program_body(expr: str) -> str:
    return f"""{{
  {expr}
}}
"""


def raccoon_let_body(lets: Iterable[str], result: str) -> str:
    body_lines = [f"  {line}" for line in lets]
    body_lines.append(f"  {result}")
    return "{\n" + "\n".join(body_lines) + "\n}"


def raccoon_level_max(levels: list[str]) -> str:
    cur = "Level.one"
    for level in reversed(levels):
        cur = f"Level.max({level}, {cur})"
    return cur


def lean_header() -> str:
    return """set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

inductive BenchUnit : Type where
  | unit : BenchUnit

"""


def lean_nat() -> str:
    return """inductive BenchNat : Type where
  | zero : BenchNat
  | succ : BenchNat -> BenchNat

"""


def lean_base() -> str:
    return """inductive Base : Type where
  | mk : Base

"""


def lean_wrap() -> str:
    return """inductive Wrap (A : Type) : Type where
  | mk : A -> Wrap A

"""


def lean_box() -> str:
    return """structure Box (A : Type) : Type where
  value : A

"""


def lean_reduce(expr: str) -> str:
    return f"#reduce {expr}\n"


def lean_let_body(lets: Iterable[str], result: str) -> str:
    body_lines = [f"  {line}" for line in lets]
    body_lines.append(f"  {result}")
    return "\n".join(body_lines)


def lean_max(levels: list[str]) -> str:
    if not levels:
        return "0"
    cur = levels[-1]
    for level in reversed(levels[:-1]):
        cur = f"max {level} ({cur})"
    return cur


def raccoon_alias_defeq(size: int) -> str:
    aliases = []
    for idx in range(size):
        body = "Wrap(A)" if idx == 0 else f"Alias{idx - 1}(A)"
        aliases.append(f"def Alias{idx} (A: Type): Type := {body}\n\n")
    target = "Wrap(Base)" if size == 0 else f"Alias{size - 1}(Base)"
    return (
        raccoon_header()
        + raccoon_base()
        + raccoon_wrap()
        + "".join(aliases)
        + "def consumeWrap (x: Wrap(Base)): BenchUnit := BenchUnit.unit\n\n"
        + f"def bench : BenchUnit := {raccoon_let_body([f'let x : {target} := Wrap.mk(Base.mk)'], 'consumeWrap(x)')}\n\n"
        + raccoon_program_body("bench")
    )


def lean_alias_defeq(size: int) -> str:
    aliases = []
    for idx in range(size):
        body = "Wrap A" if idx == 0 else f"Alias{idx - 1} A"
        aliases.append(f"abbrev Alias{idx} (A : Type) : Type := {body}\n\n")
    target = "Wrap Base" if size == 0 else f"Alias{size - 1} Base"
    return (
        lean_header()
        + lean_base()
        + lean_wrap()
        + "".join(aliases)
        + "def consumeWrap (_x : Wrap Base) : BenchUnit := BenchUnit.unit\n\n"
        + f"def bench : BenchUnit :=\n  let x : {target} := Wrap.mk Base.mk\n  consumeWrap x\n\n"
        + lean_reduce("bench")
    )


def raccoon_let_context(size: int) -> str:
    lets = ["let x0 := BenchNat.zero"]
    for idx in range(1, size + 1):
        lets.append(f"let x{idx} := BenchNat.succ(x{idx - 1})")
    return (
        raccoon_header()
        + raccoon_nat()
        + "def consumeNat (n: BenchNat): BenchUnit := BenchUnit.unit\n\n"
        + f"def bench : BenchUnit := {raccoon_let_body(lets, f'consumeNat(x{size})')}\n\n"
        + raccoon_program_body("bench")
    )


def lean_let_context(size: int) -> str:
    lets = ["let x0 := BenchNat.zero"]
    for idx in range(1, size + 1):
        lets.append(f"let x{idx} := BenchNat.succ x{idx - 1}")
    return (
        lean_header()
        + lean_nat()
        + "def consumeNat (_n : BenchNat) : BenchUnit := BenchUnit.unit\n\n"
        + f"def bench : BenchUnit :=\n{lean_let_body(lets, f'consumeNat x{size}')}\n\n"
        + lean_reduce("bench")
    )


def raccoon_app_spine(size: int) -> str:
    lets = ["let x0 := Base.mk"]
    for idx in range(1, size + 1):
        lets.append(f"let x{idx} := benchId(Base, x{idx - 1})")
    return (
        raccoon_header()
        + raccoon_base()
        + "def benchId (A: Type)(x: A): A := x\n"
        + "def consumeBase (x: Base): BenchUnit := BenchUnit.unit\n\n"
        + f"def bench : BenchUnit := {raccoon_let_body(lets, f'consumeBase(x{size})')}\n\n"
        + raccoon_program_body("bench")
    )


def lean_app_spine(size: int) -> str:
    lets = ["let x0 := Base.mk"]
    for idx in range(1, size + 1):
        lets.append(f"let x{idx} := benchId Base x{idx - 1}")
    return (
        lean_header()
        + lean_base()
        + "def benchId (A : Type) (x : A) : A := x\n"
        + "def consumeBase (_x : Base) : BenchUnit := BenchUnit.unit\n\n"
        + f"def bench : BenchUnit :=\n{lean_let_body(lets, f'consumeBase x{size}')}\n\n"
        + lean_reduce("bench")
    )


def raccoon_lambda_binders(size: int) -> str:
    if size == 0:
        bench = "def bench : BenchUnit := BenchUnit.unit\n\n"
        call = "bench"
    else:
        params = "".join(f"(x{idx}: BenchNat)" for idx in range(size))
        args = ", ".join("BenchNat.zero" for _ in range(size))
        bench = f"def bench {params}: BenchUnit := consumeNat(x{size - 1})\n\n"
        call = f"bench({args})"
    return raccoon_header() + raccoon_nat() + "def consumeNat (n: BenchNat): BenchUnit := BenchUnit.unit\n\n" + bench + raccoon_program_body(call)


def lean_lambda_binders(size: int) -> str:
    if size == 0:
        bench = "def bench : BenchUnit := BenchUnit.unit\n\n"
        call = "bench"
    else:
        params = " ".join(f"(x{idx} : BenchNat)" for idx in range(size))
        args = " ".join("BenchNat.zero" for _ in range(size))
        bench = f"def bench {params} : BenchUnit := consumeNat x{size - 1}\n\n"
        call = f"bench {args}"
    return lean_header() + lean_nat() + "def consumeNat (_n : BenchNat) : BenchUnit := BenchUnit.unit\n\n" + bench + lean_reduce(call)


def raccoon_match_width(size: int) -> str:
    ctor_count = max(1, size)
    ctors = "\n".join(f" | c{idx} : Choice" for idx in range(ctor_count))
    cases = "\n".join(f"  | Choice.c{idx} => BenchUnit.unit" for idx in range(ctor_count))
    return (
        raccoon_header()
        + f"inductive Choice : Type\n{ctors}\n\n"
        + f"def bench (c: Choice): BenchUnit := {{\n  match c returning BenchUnit with\n{cases}\n}}\n\n"
        + raccoon_program_body("bench(Choice.c0)")
    )


def lean_match_width(size: int) -> str:
    ctor_count = max(1, size)
    ctors = "\n".join(f"  | c{idx} : Choice" for idx in range(ctor_count))
    cases = "\n".join(f"  | .c{idx} => BenchUnit.unit" for idx in range(ctor_count))
    return (
        lean_header()
        + f"inductive Choice : Type where\n{ctors}\n\n"
        + f"def bench (c : Choice) : BenchUnit :=\n  match c with\n{cases}\n\n"
        + lean_reduce("bench Choice.c0")
    )


def raccoon_dependent_match(size: int) -> str:
    defs = []
    for idx in range(size):
        defs.append(
            f"""def symm{idx} (a: BenchNat)(b: BenchNat)(p: EqBench(BenchNat, a, b)): EqBench(BenchNat, b, a) := {{
  match p returning EqBench(BenchNat, b, a) with
  | EqBench.refl x => EqBench.refl(x)
}}

"""
        )
    return (
        raccoon_header()
        + raccoon_nat()
        + """inductive EqBench (A: Sort($u)) indices (x: A)(y: A) : Prop
 | refl (x: $A of Sort($u)) : EqBench(A, x, x)

"""
        + "".join(defs)
        + "def bench : BenchUnit := BenchUnit.unit\n\n"
        + raccoon_program_body("bench")
    )


def lean_dependent_match(size: int) -> str:
    defs = []
    for idx in range(size):
        defs.append(
            f"""def symm{idx} (a : BenchNat) (b : BenchNat) (p : EqBench BenchNat a b) : EqBench BenchNat b a :=
  match p with
  | EqBench.refl _ => EqBench.refl a

"""
        )
    return (
        lean_header()
        + lean_nat()
        + """inductive EqBench.{u} (A : Sort u) : A -> A -> Prop where
  | refl (x : A) : EqBench A x x

"""
        + "".join(defs)
        + "def bench : BenchUnit := BenchUnit.unit\n\n"
        + lean_reduce("bench")
    )


def raccoon_pattern_capture(size: int) -> str:
    params = [f"A{idx}" for idx in range(size)]
    targets = [f"T{idx}" for idx in range(size)]
    param_binders = "".join(f" ({param}: Sort($u{idx}))" for idx, param in enumerate(params))
    ctor_binders = "".join(f" {{{param}: Sort($u{idx})}}" for idx, param in enumerate(params))
    args = ", ".join(params)
    target_args = ", ".join(targets)
    pack_ty = f"Pack({args})" if args else "Pack"
    target_ty = f"Pack({target_args})" if target_args else "Pack"
    sort = "Type" if not params else f"Sort({raccoon_level_max([f'u{idx}' for idx in range(size)])})"
    type_decls = "".join(f"inductive {target} : Type\n | mk : {target}\n\n" for target in targets)
    mk_args = [*targets, "BenchUnit.unit"]
    if size == 0:
        capture = "def capture (p: Pack): BenchUnit := BenchUnit.unit\n\n"
    else:
        capture_args = ", ".join(f"${param}" for param in params)
        capture = f"def capture (p: Pack({capture_args})): BenchUnit := BenchUnit.unit\n\n"
    return (
        raccoon_header()
        + f"struct Pack{param_binders} : {sort}\n | mk{ctor_binders} (val: BenchUnit) : {pack_ty}\n\n"
        + type_decls
        + f"def value : {target_ty} := Pack.mk({', '.join(mk_args)})\n"
        + capture
        + "def bench : BenchUnit := capture(value)\n\n"
        + raccoon_program_body("bench")
    )


def lean_pattern_capture(size: int) -> str:
    params = [f"A{idx}" for idx in range(size)]
    targets = [f"T{idx}" for idx in range(size)]
    universes = f"universe {' '.join(f'u{idx}' for idx in range(size))}\n\n" if size else ""
    param_binders = " ".join(f"({param} : Type u{idx})" for idx, param in enumerate(params))
    args = " ".join(params)
    target_args = " ".join(targets)
    pack_ty = f"Pack {args}" if args else "Pack"
    target_ty = f"Pack {target_args}" if target_args else "Pack"
    level = lean_max([f"u{idx}" for idx in range(size)])
    sort = "Type" if size == 0 else f"Type ({level})"
    type_decls = "".join(f"inductive {target} : Type where\n  | mk : {target}\n\n" for target in targets)
    value_args = " ".join(targets)
    consume_binders = " ".join(f"{{{param} : Type u{idx}}}" for idx, param in enumerate(params))
    return (
        lean_header()
        + universes
        + f"structure Pack {param_binders} : {sort} where\n  val : BenchUnit\n\n"
        + type_decls
        + f"def value : {target_ty} := Pack.mk BenchUnit.unit\n"
        + f"def capture {consume_binders} (_p : {pack_ty}) : BenchUnit := BenchUnit.unit\n"
        + f"def bench : BenchUnit := capture value\n\n"
        + lean_reduce("bench")
    )


def raccoon_projection_chain(size: int) -> str:
    lets = []
    prev = "x"
    for idx in range(size):
        lets.append(f"let b{idx} := Box.mk({prev})")
        prev = f"b{idx}"
    projection = prev + ".value" * size if size else "x"
    return (
        raccoon_header()
        + raccoon_base()
        + raccoon_box()
        + "def consumeBase (x: Base): BenchUnit := BenchUnit.unit\n\n"
        + f"def bench (x: Base): BenchUnit := {raccoon_let_body(lets, f'consumeBase({projection})')}\n\n"
        + raccoon_program_body("bench(Base.mk)")
    )


def lean_projection_chain(size: int) -> str:
    lets = []
    prev = "x"
    for idx in range(size):
        lets.append(f"let b{idx} := Box.mk {prev}")
        prev = f"b{idx}"
    projection = prev + ".value" * size if size else "x"
    return (
        lean_header()
        + lean_base()
        + lean_box()
        + "def consumeBase (_x : Base) : BenchUnit := BenchUnit.unit\n\n"
        + f"def bench (x : Base) : BenchUnit :=\n{lean_let_body(lets, f'consumeBase {projection}')}\n\n"
        + lean_reduce("bench Base.mk")
    )


def raccoon_transparent_chain(size: int) -> str:
    defs = ["def f0 (x: Base): Base := x\n"]
    for idx in range(1, size + 1):
        defs.append(f"def f{idx} (x: Base): Base := f{idx - 1}(x)\n")
    return (
        raccoon_header()
        + raccoon_base()
        + "".join(defs)
        + "def consumeBase (x: Base): BenchUnit := BenchUnit.unit\n\n"
        + f"def bench : BenchUnit := consumeBase(f{size}(Base.mk))\n\n"
        + raccoon_program_body("bench")
    )


def lean_transparent_chain(size: int) -> str:
    defs = ["def f0 (x : Base) : Base := x\n"]
    for idx in range(1, size + 1):
        defs.append(f"def f{idx} (x : Base) : Base := f{idx - 1} x\n")
    return (
        lean_header()
        + lean_base()
        + "".join(defs)
        + "def consumeBase (_x : Base) : BenchUnit := BenchUnit.unit\n\n"
        + f"def bench : BenchUnit := consumeBase (f{size} Base.mk)\n\n"
        + lean_reduce("bench")
    )


def raccoon_universe_max(size: int) -> str:
    params = [f"A{idx}" for idx in range(size)]
    targets = [f"T{idx}" for idx in range(size)]
    param_binders = "".join(f" ({param}: Sort($u{idx}))" for idx, param in enumerate(params))
    ctor_binders = "".join(f" {{{param}: Sort($u{idx})}}" for idx, param in enumerate(params))
    args = ", ".join(params)
    target_args = ", ".join(targets)
    u_ty = f"U({args})" if args else "U"
    target_ty = f"U({target_args})" if target_args else "U"
    sort = "Type" if not params else f"Sort({raccoon_level_max([f'u{idx}' for idx in range(size)])})"
    type_decls = "".join(f"inductive {target} : Type\n | mk : {target}\n\n" for target in targets)
    mk_args = [*targets, "BenchUnit.unit"]
    return (
        raccoon_header()
        + f"struct U{param_binders} : {sort}\n | mk{ctor_binders} (val: BenchUnit) : {u_ty}\n\n"
        + type_decls
        + f"def consume (u: {target_ty}): BenchUnit := BenchUnit.unit\n"
        + f"def bench : BenchUnit := consume(U.mk({', '.join(mk_args)}))\n\n"
        + raccoon_program_body("bench")
    )


def lean_universe_max(size: int) -> str:
    params = [f"A{idx}" for idx in range(size)]
    targets = [f"T{idx}" for idx in range(size)]
    universes = f"universe {' '.join(f'u{idx}' for idx in range(size))}\n\n" if size else ""
    param_binders = " ".join(f"({param} : Type u{idx})" for idx, param in enumerate(params))
    target_args = " ".join(targets)
    target_ty = f"U {target_args}" if target_args else "U"
    level = lean_max([f"u{idx}" for idx in range(size)])
    sort = "Type" if size == 0 else f"Type ({level})"
    type_decls = "".join(f"inductive {target} : Type where\n  | mk : {target}\n\n" for target in targets)
    return (
        lean_header()
        + universes
        + f"structure U {param_binders} : {sort} where\n  val : BenchUnit\n\n"
        + type_decls
        + f"def consume (_u : {target_ty}) : BenchUnit := BenchUnit.unit\n"
        + f"def bench : BenchUnit := consume (U.mk BenchUnit.unit)\n\n"
        + lean_reduce("bench")
    )


RACCOON_GENERATORS: dict[str, Callable[[int], str]] = {
    "alias-defeq": raccoon_alias_defeq,
    "let-context": raccoon_let_context,
    "app-spine": raccoon_app_spine,
    "lambda-binders": raccoon_lambda_binders,
    "match-width": raccoon_match_width,
    "dependent-match": raccoon_dependent_match,
    "pattern-capture": raccoon_pattern_capture,
    "projection-chain": raccoon_projection_chain,
    "transparent-chain": raccoon_transparent_chain,
    "universe-max": raccoon_universe_max,
}

LEAN_GENERATORS: dict[str, Callable[[int], str]] = {
    "alias-defeq": lean_alias_defeq,
    "let-context": lean_let_context,
    "app-spine": lean_app_spine,
    "lambda-binders": lean_lambda_binders,
    "match-width": lean_match_width,
    "dependent-match": lean_dependent_match,
    "pattern-capture": lean_pattern_capture,
    "projection-chain": lean_projection_chain,
    "transparent-chain": lean_transparent_chain,
    "universe-max": lean_universe_max,
}


def write_file(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents)


def scenario_sizes(args: argparse.Namespace, scenario: str) -> list[int]:
    if args.sizes is not None:
        return args.sizes
    return DEFAULT_SIZES[scenario]


def generate_raccoon(out_dir: Path, scenarios: Iterable[str], args: argparse.Namespace) -> None:
    for scenario in scenarios:
        generator = RACCOON_GENERATORS[scenario]
        for size in scenario_sizes(args, scenario):
            write_file(out_dir / f"checker_{scenario}_{size}.rac", generator(size))


def generate_lean(out_dir: Path, scenarios: Iterable[str], args: argparse.Namespace) -> None:
    for scenario in scenarios:
        generator = LEAN_GENERATORS[scenario]
        for size in scenario_sizes(args, scenario):
            write_file(out_dir / f"checker_{scenario}_{size}.lean", generator(size))


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
    runner: str
    scenario: str
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


def benchmark_command(
    runner: str,
    scenario: str,
    size: int,
    command: list[str],
    reps: int,
    timeout: float | None,
) -> RunSummary:
    timings: list[float] = []
    stderr_tail = ""
    for rep in range(reps):
        code, elapsed, stderr = run_once(command, timeout)
        stderr_tail = "\n".join(line for line in stderr.strip().splitlines()[-4:] if line.strip())
        if code != 0:
            return RunSummary(runner, scenario, size, f"exit {code}", None, elapsed, elapsed, rep + 1, stderr_tail)
        timings.append(elapsed)

    return RunSummary(
        runner=runner,
        scenario=scenario,
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
    label = f"{summary.runner}:{summary.scenario}"
    if summary.median is None:
        extra = f" stderr={summary.stderr_tail!r}" if summary.stderr_tail else ""
        print(f"{label:36s} {summary.size:6d} {summary.status:8s} time={summary.minimum:.4f}s{extra}")
    else:
        print(
            f"{label:36s} {summary.size:6d} ok       "
            f"median={summary.median:.4f}s min={summary.minimum:.4f}s max={summary.maximum:.4f}s reps={summary.reps}"
        )


def append_csv(path: Path, summary: RunSummary) -> None:
    exists = path.exists()
    with path.open("a", newline="") as f:
        writer = csv.writer(f)
        if not exists:
            writer.writerow(["runner", "scenario", "size", "status", "median", "min", "max", "reps", "stderr_tail"])
        writer.writerow(
            [
                summary.runner,
                summary.scenario,
                summary.size,
                summary.status,
                "" if summary.median is None else f"{summary.median:.6f}",
                f"{summary.minimum:.6f}",
                f"{summary.maximum:.6f}",
                summary.reps,
                summary.stderr_tail,
            ]
        )


def run_raccoon_jvm(args: argparse.Namespace, out_dir: Path, scenarios: Iterable[str]) -> None:
    classpath = args.classpath or default_classpath()
    for scenario in scenarios:
        for size in scenario_sizes(args, scenario):
            reps = reps_for_size(size, args.reps, args.large_reps, args.large_threshold)
            path = out_dir / f"checker_{scenario}_{size}.rac"
            command = [args.java, "-cp", classpath, "com.raccoonlang.Main", "--prelude", args.prelude, str(path)]
            summary = benchmark_command("raccoon-jvm", scenario, size, command, reps, args.timeout)
            print_summary(summary)
            if args.csv is not None:
                append_csv(args.csv, summary)


def run_lean(args: argparse.Namespace, out_dir: Path, scenarios: Iterable[str]) -> None:
    for scenario in scenarios:
        for size in scenario_sizes(args, scenario):
            reps = reps_for_size(size, args.reps, args.large_reps, args.large_threshold)
            path = out_dir / f"checker_{scenario}_{size}.lean"
            summary = benchmark_command("lean-nightly", scenario, size, [args.lean, str(path)], reps, args.timeout)
            print_summary(summary)
            if args.csv is not None:
                append_csv(args.csv, summary)


def expand_runners(runners: list[str]) -> list[str]:
    if "all" not in runners:
        return runners
    return ["generate", "jvm", "lean"]


def expand_scenarios(scenarios: list[str]) -> list[str]:
    if not scenarios or "all" in scenarios:
        return list(ALL_SCENARIOS)
    unknown = sorted(set(scenarios) - set(ALL_SCENARIOS))
    if unknown:
        raise ValueError(f"unknown scenario(s): {', '.join(unknown)}")
    return scenarios


def print_scenarios() -> None:
    for scenario in ALL_SCENARIOS:
        sizes = ",".join(str(size) for size in DEFAULT_SIZES[scenario])
        print(f"{scenario:18s} {sizes:26s} {SCENARIO_DESCRIPTIONS[scenario]}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--runner",
        action="append",
        choices=["generate", "jvm", "lean", "all"],
        default=[],
        help="benchmark runner to execute; may be repeated",
    )
    parser.add_argument("--scenario", action="append", choices=[*ALL_SCENARIOS, "all"], default=[])
    parser.add_argument("--list", action="store_true", help="list scenarios and default sizes")
    parser.add_argument("--out-dir", type=Path, default=Path("/tmp/raccoonlang-benchmarks/checker-interpreter"))
    parser.add_argument("--sizes", type=parse_sizes)
    parser.add_argument("--reps", type=int, default=5, help="repetitions for sizes below --large-threshold")
    parser.add_argument("--large-reps", type=int, default=3)
    parser.add_argument("--large-threshold", type=int, default=10000)
    parser.add_argument("--timeout", type=float, default=180.0)
    parser.add_argument("--java", default="java")
    parser.add_argument("--classpath", help="JVM classpath for com.raccoonlang.Main")
    parser.add_argument("--prelude", default=str(REPO_ROOT / "src/main/resources/Init/TestPrelude.rac"))
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--csv", type=Path, help="append machine-readable results to this CSV")
    args = parser.parse_args()

    if args.list:
        print_scenarios()
        return 0

    runners = expand_runners(args.runner or ["generate"])
    scenarios = expand_scenarios(args.scenario)
    args.out_dir.mkdir(parents=True, exist_ok=True)

    if any(runner in runners for runner in ["generate", "jvm"]):
        generate_raccoon(args.out_dir, scenarios, args)
    if any(runner in runners for runner in ["generate", "lean"]):
        generate_lean(args.out_dir, scenarios, args)

    if runners == ["generate"]:
        print(f"generated benchmark sources in {args.out_dir}")
        return 0

    for runner in runners:
        if runner == "generate":
            continue
        if runner == "jvm":
            run_raccoon_jvm(args, args.out_dir, scenarios)
        elif runner == "lean":
            run_lean(args, args.out_dir, scenarios)
        else:
            raise ValueError(f"unknown runner: {runner}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (FileNotFoundError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
