#!/usr/bin/env python3
"""Generate and run typeclass-resolution benchmarks for raccoon and Lean.

The benchmark suite is intentionally split into several scenarios because
typeclass search cost is affected by different dimensions:

* width: number of same-class global instances
* fanout: number of instance dependencies on one successful candidate
* chain: recursive instance depth
* failures: number of failing candidates before a success
* branching: failing alternatives at each recursive level
* implicit-arity: many parameters recovered from a captured instance dependency
* explicit-control: explicit instance/value construction without search
* repeat-query: repeated identical queries in one file
* diamond: repeated shared-subgoal reuse through a layered hierarchy
* overlap: near-applicable overlapping candidates before success
* local-instances: a local instance in scope plus many global decoys
* defeq: targets hidden behind reducible aliases
* shared-fanout: one successful candidate with repeated identical dependencies
* instance-body: fixed search with a growing successful instance body

Generated classes and reusable instances are universe-polymorphic. Raccoon uses
Sort($uN) binders; Lean uses Type uN binders with declared universe levels.

Lean sources can be generated with the usual Lean startup environment or with a
first-line `prelude` command. The no-prelude mode avoids importing Lean's `Init`
environment, which keeps unrelated global instances out of the comparison.
"""

from __future__ import annotations

import argparse
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
    "width",
    "fanout",
    "chain",
    "failures",
    "branching",
    "implicit-arity",
    "explicit-control",
    "repeat-query",
    "diamond",
    "overlap",
    "local-instances",
    "defeq",
    "shared-fanout",
    "instance-body",
)
DEFAULT_SCENARIOS = ("width", "fanout", "failures", "branching", "implicit-arity")
DEFAULT_SIZES = {
    "width": [0, 1000, 5000, 10000, 20000, 40000],
    "fanout": [0, 1000, 5000, 10000, 20000],
    "chain": [0, 12, 16, 20, 22, 24],
    "failures": [0, 1000, 5000, 10000, 20000, 40000],
    "branching": [0, 1000, 5000, 10000, 20000, 40000],
    "implicit-arity": [0, 8, 12, 16, 20, 22, 24, 128, 512, 1024, 2048, 4096],
    "explicit-control": [0, 128, 512, 1024],
    "repeat-query": [0, 100, 1000, 5000],
    "diamond": [0, 4, 8, 12, 14, 16],
    "overlap": [0, 1000, 5000, 10000, 20000, 40000],
    "local-instances": [0, 1000, 5000, 10000, 20000, 40000],
    "defeq": [0, 512, 1024, 1280, 1536],
    "shared-fanout": [0, 100, 1000, 2000, 5000, 10000],
    "instance-body": [0, 100, 500, 800, 1000],
}


def parse_sizes(value: str) -> list[int]:
    try:
        sizes = [int(part.strip()) for part in value.split(",") if part.strip()]
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"invalid size list: {value}") from exc
    if any(size < 0 for size in sizes):
        raise argparse.ArgumentTypeError("sizes must be non-negative")
    return sizes


def raccoon_prelude() -> str:
    return """inductive BenchUnit : Type
 | unit : BenchUnit

"""


def raccoon_struct(name: str, params: Iterable[str] = ()) -> str:
    param_list = list(params)
    param_str = "".join(f" ({param}: Sort($u{idx}))" for idx, param in enumerate(param_list))
    args = ", ".join(param_list)
    result = f"{name}({args})" if args else name
    return f"""struct {name}{param_str} : {raccoon_sort(param_list)}
 | mk (val: BenchUnit) : {result}

"""


def raccoon_sort(params: Iterable[str]) -> str:
    levels = [f"u{idx}" for idx, _ in enumerate(params)]
    if not levels:
        return "Type"
    if len(levels) == 1:
        return f"Sort({levels[0]})"

    level = levels[-1]
    for cur in reversed(levels[:-1]):
        level = f"Level.max({cur}, {level})"
    return f"Sort({level})"


def raccoon_type_binders(params: Iterable[str]) -> str:
    return "".join(f"({param}: Sort($u{idx}))" for idx, param in enumerate(params))


def raccoon_instance_binder(name: str, ty: str) -> str:
    return f"[{name}: {ty}]"


def raccoon_derive(goal: str) -> str:
    return f"derive[{goal}]"


def raccoon_mk(name: str, args: Iterable[str] = ()) -> str:
    all_args = [*args, "BenchUnit.unit"]
    return f"{name}.mk({', '.join(all_args)})"


def raccoon_type_decl(name: str) -> str:
    return f"""inductive {name} : Type
 | mk : {name}

"""


def raccoon_wrap_type(depth: int) -> str:
    ty = "Base"
    for _ in range(depth):
        ty = f"Wrap({ty})"
    return ty


def raccoon_bench(expressions: list[str]) -> str:
    if not expressions:
        expressions = ["BenchUnit.unit"]

    lets = [f"  let q{idx} := {expr}" for idx, expr in enumerate(expressions[:-1])]
    body_lines = lets + [f"  {expressions[-1]}"]
    return f"""def bench (seed: BenchUnit): BenchUnit := {{
{chr(10).join(body_lines)}
}}
"""


def raccoon_payload_chain(size: int) -> str:
    expr = "Payload.leaf"
    for _ in range(size):
        expr = f"Payload.node({expr}, Payload.leaf)"
    return expr


def lean_universe_name(idx: int) -> str:
    return f"u{idx}"


def lean_universe_decl(count: int) -> str:
    if count <= 0:
        return ""
    return f"universe {' '.join(lean_universe_name(idx) for idx in range(count))}\n\n"


def lean_sort(params: Iterable[str]) -> str:
    levels = [lean_universe_name(idx) for idx, _ in enumerate(params)]
    if not levels:
        return "Type"
    if len(levels) == 1:
        return f"Type {levels[0]}"

    level = f"max {levels[-2]} {levels[-1]}"
    for cur in reversed(levels[:-2]):
        level = f"max {cur} ({level})"
    return f"Type ({level})"


def lean_type_binders(params: Iterable[str], implicit: bool = False) -> str:
    left, right = ("{", "}") if implicit else ("(", ")")
    return "".join(f" {left}{param} : Type {lean_universe_name(idx)}{right}" for idx, param in enumerate(params))


def lean_header(no_prelude: bool, universe_count: int = 1) -> str:
    prefix = "prelude\n" if no_prelude else ""
    return (
        prefix
        + """set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option synthInstance.maxSize 2000000000

"""
        + lean_universe_decl(universe_count)
    )


def lean_unit_decl() -> str:
    return """inductive BenchUnit : Type where
  | unit : BenchUnit

"""


def lean_class(name: str, params: Iterable[str] = ()) -> str:
    param_list = list(params)
    param_str = lean_type_binders(param_list)
    result_sort = lean_sort(param_list)
    return f"""class {name}{param_str} : {result_sort} where
  val : BenchUnit

"""


def lean_type_decl(name: str) -> str:
    return f"""inductive {name} : Type where
  | mk : {name}

"""


def lean_wrap_type(depth: int) -> str:
    ty = "Base"
    for _ in range(depth):
        ty = f"Wrap ({ty})"
    return ty


def lean_bench(expressions: list[str]) -> str:
    if not expressions:
        expressions = ["BenchUnit.unit"]

    lets = [f"  let q{idx} := {expr}" for idx, expr in enumerate(expressions[:-1])]
    body_lines = lets + [f"  {expressions[-1]}"]
    return f"""noncomputable def bench (_seed : BenchUnit) : BenchUnit :=
{chr(10).join(body_lines)}
"""


def lean_payload_chain(size: int) -> str:
    expr = "Payload.leaf"
    for _ in range(size):
        expr = f"Payload.node ({expr}) Payload.leaf"
    return expr


def raccoon_width(size: int, calls: int, _branch_depth: int) -> str:
    decoys = [f"WidthDecoy{i}" for i in range(size)]
    targets = [f"WidthTarget{i}" for i in range(calls)]
    decls = [raccoon_prelude(), raccoon_struct("TC", ["A"])]
    decls.extend(raccoon_type_decl(name) for name in decoys + targets)
    decls.extend(f"def instance inst{name} : TC({name}) := {raccoon_mk('TC', [name])}\n\n" for name in decoys + targets)
    decls.append("def consume (A: Sort($u0))[tc: TC(A)]: BenchUnit := BenchUnit.unit\n\n")
    decls.append(raccoon_bench([f"consume({target}, {raccoon_derive(f'TC({target})')})" for target in targets]))
    return "".join(decls)


def lean_width(size: int, calls: int, _branch_depth: int, no_prelude: bool) -> str:
    decoys = [f"WidthDecoy{i}" for i in range(size)]
    targets = [f"WidthTarget{i}" for i in range(calls)]
    decls = [lean_header(no_prelude), lean_unit_decl(), lean_class("TC", ["A"])]
    decls.extend(lean_type_decl(name) for name in decoys + targets)
    decls.extend(f"noncomputable instance inst{name} : TC {name} where\n  val := BenchUnit.unit\n\n" for name in decoys + targets)
    decls.append("axiom consume {A : Type u0} [TC A] : BenchUnit\n\n")
    decls.append(lean_bench([f"consume (A := {target})" for target in targets]))
    return "".join(decls)


def raccoon_fanout(size: int, _calls: int, _branch_depth: int) -> str:
    dep_names = [f"Dep{i}" for i in range(size)]
    decls = [raccoon_prelude(), raccoon_struct("Need", ["A"])]
    decls.extend(raccoon_struct(dep, ["A"]) for dep in dep_names)
    decls.append(raccoon_type_decl("FanoutTarget"))
    decls.extend(
        f"def instance inst{dep}Target : {dep}(FanoutTarget) := {raccoon_mk(dep, ['FanoutTarget'])}\n\n"
        for dep in dep_names
    )
    if dep_names:
        binders = "".join(
            raccoon_instance_binder(f"d{i}", f"{dep}({'$A' if i == 0 else 'A'})")
            for i, dep in enumerate(dep_names)
        )
        decls.append(f"def instance needInst {binders}: Need(A) := {raccoon_mk('Need', ['A'])}\n\n")
    else:
        decls.append(f"def instance needInst : Need(FanoutTarget) := {raccoon_mk('Need', ['FanoutTarget'])}\n\n")
    decls.append("def consume (A: Sort($u0))[need: Need(A)]: BenchUnit := BenchUnit.unit\n\n")
    decls.append(raccoon_bench([f"consume(FanoutTarget, {raccoon_derive('Need(FanoutTarget)')})"]))
    return "".join(decls)


def lean_fanout(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    dep_names = [f"Dep{i}" for i in range(size)]
    deps = "".join(f" [{dep} A]" for dep in dep_names)
    decls = [lean_header(no_prelude), lean_unit_decl(), lean_class("Need", ["A"])]
    decls.extend(lean_class(dep, ["A"]) for dep in dep_names)
    decls.append(lean_type_decl("FanoutTarget"))
    decls.extend(f"noncomputable instance inst{dep}Target : {dep} FanoutTarget where\n  val := BenchUnit.unit\n\n" for dep in dep_names)
    decls.append(f"noncomputable instance needInst {{A : Type u0}}{deps} : Need A where\n  val := BenchUnit.unit\n\n")
    decls.append("axiom consume {A : Type u0} [Need A] : BenchUnit\n\n")
    decls.append(lean_bench(["consume (A := FanoutTarget)"]))
    return "".join(decls)


def raccoon_chain(size: int, _calls: int, _branch_depth: int) -> str:
    target = raccoon_wrap_type(size)
    decls = [
        raccoon_prelude(),
        raccoon_struct("TC", ["A"]),
        raccoon_type_decl("Base"),
        """inductive Wrap (A: Sort($u0)) : Sort(u0)
 | mk : Wrap(A)

""",
        f"def instance baseTC : TC(Base) := {raccoon_mk('TC', ['Base'])}\n\n",
        f"def instance wrapTC [inner: TC($A)]: TC(Wrap(A)) := {raccoon_mk('TC', ['Wrap(A)'])}\n\n",
        "def consume (A: Sort($u0))[tc: TC(A)]: BenchUnit := BenchUnit.unit\n\n",
        raccoon_bench([f"consume({target}, {raccoon_derive(f'TC({target})')})"]),
    ]
    return "".join(decls)


def lean_chain(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    target = lean_wrap_type(size)
    return (
        lean_header(no_prelude)
        + lean_unit_decl()
        + lean_class("TC", ["A"])
        + lean_type_decl("Base")
        + """inductive Wrap (A : Type u0) : Type u0 where
  | mk : Wrap A

noncomputable instance baseTC : TC Base where
  val := BenchUnit.unit

noncomputable instance wrapTC {A : Type u0} [TC A] : TC (Wrap A) where
  val := BenchUnit.unit

axiom consume {A : Type u0} [TC A] : BenchUnit

"""
        + lean_bench([f"consume (A := {target})"])
    )


def raccoon_failures(size: int, _calls: int, _branch_depth: int) -> str:
    missing = [f"Missing{i}" for i in range(size)]
    decls = [raccoon_prelude(), raccoon_struct("Goal", ["A"])]
    decls.extend(raccoon_struct(name, ["A"]) for name in missing)
    decls.append(raccoon_type_decl("FailureTarget"))
    for name in missing:
        decls.append(
            f"def instance bad{name} [m: {name}(FailureTarget)]: Goal(FailureTarget) := {raccoon_mk('Goal', ['FailureTarget'])}\n\n"
        )
    decls.append(f"def instance goodGoal : Goal(FailureTarget) := {raccoon_mk('Goal', ['FailureTarget'])}\n\n")
    decls.append("def consume (A: Sort($u0))[goal: Goal(A)]: BenchUnit := BenchUnit.unit\n\n")
    decls.append(raccoon_bench([f"consume(FailureTarget, {raccoon_derive('Goal(FailureTarget)')})"]))
    return "".join(decls)


def lean_failures(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    missing = [f"Missing{i}" for i in range(size)]
    decls = [lean_header(no_prelude), lean_unit_decl(), lean_class("Goal", ["A"])]
    decls.extend(lean_class(name, ["A"]) for name in missing)
    decls.append(lean_type_decl("FailureTarget"))
    for name in missing:
        decls.append(
            f"noncomputable instance (priority := 1000) bad{name} [{name} FailureTarget] : Goal FailureTarget where\n"
            "  val := BenchUnit.unit\n\n"
        )
    decls.append("noncomputable instance (priority := 500) goodGoal : Goal FailureTarget where\n  val := BenchUnit.unit\n\n")
    decls.append("axiom consume {A : Type u0} [Goal A] : BenchUnit\n\n")
    decls.append(lean_bench(["consume (A := FailureTarget)"]))
    return "".join(decls)


def raccoon_branching(size: int, _calls: int, branch_depth: int) -> str:
    missing = [f"Missing{i}" for i in range(size)]
    target = raccoon_wrap_type(branch_depth)
    decls = [
        raccoon_prelude(),
        raccoon_struct("TC", ["A"]),
    ]
    decls.extend(raccoon_struct(name, ["A"]) for name in missing)
    decls.extend(
        [
            raccoon_type_decl("Base"),
            """inductive Wrap (A: Sort($u0)) : Sort(u0)
 | mk : Wrap(A)

""",
        ]
    )
    for name in missing:
        decls.append(
            f"def instance bad{name} [m: {name}($A)]: TC(Wrap(A)) := {raccoon_mk('TC', ['Wrap(A)'])}\n\n"
        )
    decls.append(f"def instance wrapTC [inner: TC($A)]: TC(Wrap(A)) := {raccoon_mk('TC', ['Wrap(A)'])}\n\n")
    decls.append(f"def instance baseTC : TC(Base) := {raccoon_mk('TC', ['Base'])}\n\n")
    decls.append("def consume (A: Sort($u0))[tc: TC(A)]: BenchUnit := BenchUnit.unit\n\n")
    decls.append(raccoon_bench([f"consume({target}, {raccoon_derive(f'TC({target})')})"]))
    return "".join(decls)


def lean_branching(size: int, _calls: int, branch_depth: int, no_prelude: bool) -> str:
    missing = [f"Missing{i}" for i in range(size)]
    target = lean_wrap_type(branch_depth)
    decls = [lean_header(no_prelude), lean_unit_decl(), lean_class("TC", ["A"])]
    decls.extend(lean_class(name, ["A"]) for name in missing)
    decls.extend(
        [
            lean_type_decl("Base"),
            """inductive Wrap (A : Type u0) : Type u0 where
  | mk : Wrap A

""",
        ]
    )
    for name in missing:
        decls.append(
            f"noncomputable instance (priority := 1000) bad{name} {{A : Type u0}} [{name} A] : TC (Wrap A) where\n"
            "  val := BenchUnit.unit\n\n"
        )
    decls.append("noncomputable instance (priority := 500) wrapTC {A : Type u0} [TC A] : TC (Wrap A) where\n  val := BenchUnit.unit\n\n")
    decls.append("noncomputable instance (priority := 100) baseTC : TC Base where\n  val := BenchUnit.unit\n\n")
    decls.append("axiom consume {A : Type u0} [TC A] : BenchUnit\n\n")
    decls.append(lean_bench([f"consume (A := {target})"]))
    return "".join(decls)


def raccoon_implicit_arity(size: int, _calls: int, _branch_depth: int) -> str:
    params = [f"A{i}" for i in range(size)]
    targets = [f"ImplicitTarget{i}" for i in range(size)]
    args = ", ".join(params)
    target_args = ", ".join(targets)
    rel_type = f"Rel({args})" if args else "Rel"
    target_rel = f"Rel({target_args})" if target_args else "Rel"
    consume_call = f"consume({raccoon_derive(target_rel)})"
    decls = [raccoon_prelude()]
    decls.append(raccoon_struct("Rel", params))
    if params:
        decls.append(raccoon_struct("Carrier", params))
    decls.extend(raccoon_type_decl(target) for target in targets)
    if params:
        capture_args = ", ".join(f"${param}" for param in params)
        decls.append(f"def instance carrierTarget : Carrier({target_args}) := {raccoon_mk('Carrier', targets)}\n\n")
        decls.append(
            f"def instance relInst [carrier: Carrier({capture_args})]: {rel_type} := {raccoon_mk('Rel', params)}\n\n"
        )
    else:
        decls.append(f"def instance relInst : {rel_type} := {raccoon_mk('Rel', params)}\n\n")
    decls.append(f"def consume [rel: {target_rel}]: BenchUnit := BenchUnit.unit\n\n")
    decls.append(raccoon_bench([consume_call]))
    return "".join(decls)


def lean_implicit_arity(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    params = [f"A{i}" for i in range(size)]
    targets = [f"ImplicitTarget{i}" for i in range(size)]
    param_str = lean_type_binders(params, implicit=True)
    target_rel = "Rel" + (" " + " ".join(targets) if targets else "")
    decls = [lean_header(no_prelude, len(params)), lean_unit_decl(), lean_class("Rel", params)]
    if params:
        decls.append(lean_class("Carrier", params))
    decls.extend(lean_type_decl(target) for target in targets)
    if params:
        decls.append(f"noncomputable instance carrierTarget : Carrier {target_rel[len('Rel '):]} where\n  val := BenchUnit.unit\n\n")
        decls.append(
            f"noncomputable instance relInst{param_str} [Carrier{(' ' + ' '.join(params))}] : "
            f"Rel{(' ' + ' '.join(params))} where\n  val := BenchUnit.unit\n\n"
        )
    else:
        decls.append("noncomputable instance relInst : Rel where\n  val := BenchUnit.unit\n\n")
    decls.append(f"axiom consume [{target_rel}] : BenchUnit\n\n")
    decls.append(lean_bench(["consume"]))
    return "".join(decls)


def raccoon_explicit_control(size: int, _calls: int, _branch_depth: int) -> str:
    params = [f"A{i}" for i in range(size)]
    targets = [f"ExplicitTarget{i}" for i in range(size)]
    args = ", ".join(params)
    target_args = ", ".join(targets)
    rel_type = f"Rel({args})" if args else "Rel"
    target_rel = f"Rel({target_args})" if target_args else "Rel"
    rel_call = f"relValue({target_args})" if target_args else "relValue"
    decls = [raccoon_prelude(), raccoon_struct("Rel", params)]
    decls.extend(raccoon_type_decl(target) for target in targets)
    decls.append(f"def relValue {raccoon_type_binders(params)}: {rel_type} := {raccoon_mk('Rel', params)}\n\n")
    decls.append(f"def consume (rel: {target_rel}): BenchUnit := BenchUnit.unit\n\n")
    decls.append(raccoon_bench([f"consume({rel_call})"]))
    return "".join(decls)


def lean_explicit_control(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    params = [f"A{i}" for i in range(size)]
    targets = [f"ExplicitTarget{i}" for i in range(size)]
    rel_type = "Rel" + (" " + " ".join(params) if params else "")
    target_rel = "Rel" + (" " + " ".join(targets) if targets else "")
    rel_call = "relValue" + (" " + " ".join(targets) if targets else "")
    decls = [lean_header(no_prelude, len(params)), lean_unit_decl(), lean_class("Rel", params)]
    decls.extend(lean_type_decl(target) for target in targets)
    decls.append(f"noncomputable def relValue{lean_type_binders(params)} : {rel_type} where\n  val := BenchUnit.unit\n\n")
    decls.append(f"axiom consume (_rel : {target_rel}) : BenchUnit\n\n")
    consume_call = f"consume ({rel_call})" if targets else "consume relValue"
    decls.append(lean_bench([consume_call]))
    return "".join(decls)


def raccoon_repeat_query(size: int, _calls: int, _branch_depth: int) -> str:
    decls = [raccoon_prelude(), raccoon_struct("TC", ["A"]), raccoon_type_decl("RepeatTarget")]
    decls.append(f"def instance repeatTC : TC(RepeatTarget) := {raccoon_mk('TC', ['RepeatTarget'])}\n\n")
    decls.append("def consume (A: Sort($u0))[tc: TC(A)]: BenchUnit := BenchUnit.unit\n\n")
    decls.append(raccoon_bench([f"consume(RepeatTarget, {raccoon_derive('TC(RepeatTarget)')})" for _ in range(size)]))
    return "".join(decls)


def lean_repeat_query(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    decls = [lean_header(no_prelude), lean_unit_decl(), lean_class("TC", ["A"]), lean_type_decl("RepeatTarget")]
    decls.append("noncomputable instance repeatTC : TC RepeatTarget where\n  val := BenchUnit.unit\n\n")
    decls.append("axiom consume {A : Type u0} [TC A] : BenchUnit\n\n")
    decls.append(lean_bench(["consume (A := RepeatTarget)" for _ in range(size)]))
    return "".join(decls)


def raccoon_diamond(size: int, _calls: int, _branch_depth: int) -> str:
    need = lambda idx: f"Need{idx}"
    left = lambda idx: f"Left{idx}"
    right = lambda idx: f"Right{idx}"
    decls = [raccoon_prelude(), raccoon_struct(need(0), ["A"])]
    for idx in range(1, size + 1):
        decls.append(raccoon_struct(need(idx), ["A"]))
        decls.append(raccoon_struct(left(idx), ["A"]))
        decls.append(raccoon_struct(right(idx), ["A"]))
    decls.append(raccoon_type_decl("DiamondTarget"))
    decls.append(f"def instance base{need(0)} : {need(0)}(DiamondTarget) := {raccoon_mk(need(0), ['DiamondTarget'])}\n\n")
    for idx in range(1, size + 1):
        decls.append(
            f"def instance inst{left(idx)} [inner: {need(idx - 1)}($A)]: {left(idx)}(A) := "
            f"{raccoon_mk(left(idx), ['A'])}\n\n"
        )
        decls.append(
            f"def instance inst{right(idx)} [inner: {need(idx - 1)}($A)]: {right(idx)}(A) := "
            f"{raccoon_mk(right(idx), ['A'])}\n\n"
        )
        decls.append(
            f"def instance inst{need(idx)} [l: {left(idx)}($A)][r: {right(idx)}(A)]: "
            f"{need(idx)}(A) := {raccoon_mk(need(idx), ['A'])}\n\n"
        )
    decls.append(
        f"def consume (A: Sort($u0))[need: {need(size)}(A)]: BenchUnit := BenchUnit.unit\n\n"
    )
    decls.append(raccoon_bench([f"consume(DiamondTarget, {raccoon_derive(f'{need(size)}(DiamondTarget)')})"]))
    return "".join(decls)


def lean_diamond(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    need = lambda idx: f"Need{idx}"
    left = lambda idx: f"Left{idx}"
    right = lambda idx: f"Right{idx}"
    decls = [lean_header(no_prelude), lean_unit_decl(), lean_class(need(0), ["A"])]
    for idx in range(1, size + 1):
        decls.append(lean_class(need(idx), ["A"]))
        decls.append(lean_class(left(idx), ["A"]))
        decls.append(lean_class(right(idx), ["A"]))
    decls.append(lean_type_decl("DiamondTarget"))
    decls.append(f"noncomputable instance base{need(0)} : {need(0)} DiamondTarget where\n  val := BenchUnit.unit\n\n")
    for idx in range(1, size + 1):
        decls.append(
            f"noncomputable instance inst{left(idx)} {{A : Type u0}} [{need(idx - 1)} A] : {left(idx)} A where\n"
            "  val := BenchUnit.unit\n\n"
        )
        decls.append(
            f"noncomputable instance inst{right(idx)} {{A : Type u0}} [{need(idx - 1)} A] : {right(idx)} A where\n"
            "  val := BenchUnit.unit\n\n"
        )
        decls.append(
            f"noncomputable instance inst{need(idx)} {{A : Type u0}} [{left(idx)} A] [{right(idx)} A] : {need(idx)} A where\n"
            "  val := BenchUnit.unit\n\n"
        )
    decls.append(f"axiom consume {{A : Type u0}} [{need(size)} A] : BenchUnit\n\n")
    decls.append(lean_bench(["consume (A := DiamondTarget)"]))
    return "".join(decls)


def raccoon_overlap(size: int, _calls: int, _branch_depth: int) -> str:
    missing = [f"OverlapMissing{i}" for i in range(size)]
    decls = [raccoon_prelude(), raccoon_struct("Goal", ["A"])]
    decls.extend(raccoon_struct(name, ["A"]) for name in missing)
    decls.extend(
        [
            raccoon_type_decl("Base"),
            """inductive Wrap (A: Sort($u0)) : Sort(u0)
 | mk : Wrap(A)

""",
        ]
    )
    for name in missing:
        decls.append(
            f"def instance bad{name} [m: {name}(Wrap($A))]: Goal(Wrap(A)) := "
            f"{raccoon_mk('Goal', ['Wrap(A)'])}\n\n"
        )
    decls.append(
        f"def instance wrapGoal [inner: Goal($A)]: Goal(Wrap(A)) := "
        f"{raccoon_mk('Goal', ['Wrap(A)'])}\n\n"
    )
    decls.append(f"def instance baseGoal : Goal(Base) := {raccoon_mk('Goal', ['Base'])}\n\n")
    decls.append("def consume (A: Sort($u0))[goal: Goal(A)]: BenchUnit := BenchUnit.unit\n\n")
    decls.append(raccoon_bench([f"consume(Wrap(Base), {raccoon_derive('Goal(Wrap(Base))')})"]))
    return "".join(decls)


def lean_overlap(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    missing = [f"OverlapMissing{i}" for i in range(size)]
    decls = [lean_header(no_prelude), lean_unit_decl(), lean_class("Goal", ["A"])]
    decls.extend(lean_class(name, ["A"]) for name in missing)
    decls.extend(
        [
            lean_type_decl("Base"),
            """inductive Wrap (A : Type u0) : Type u0 where
  | mk : Wrap A

""",
        ]
    )
    for name in missing:
        decls.append(
            f"noncomputable instance (priority := 1000) bad{name} {{A : Type u0}} [{name} (Wrap A)] : Goal (Wrap A) where\n"
            "  val := BenchUnit.unit\n\n"
        )
    decls.append(
        "noncomputable instance (priority := 500) wrapGoal {A : Type u0} [Goal A] : Goal (Wrap A) where\n"
        "  val := BenchUnit.unit\n\n"
    )
    decls.append("noncomputable instance (priority := 100) baseGoal : Goal Base where\n  val := BenchUnit.unit\n\n")
    decls.append("axiom consume {A : Type u0} [Goal A] : BenchUnit\n\n")
    decls.append(lean_bench(["consume (A := Wrap Base)"]))
    return "".join(decls)


def raccoon_local_instances(size: int, _calls: int, _branch_depth: int) -> str:
    decoys = [f"LocalDecoy{i}" for i in range(size)]
    decls = [raccoon_prelude(), raccoon_struct("Goal", ["A"]), raccoon_type_decl("LocalTarget")]
    decls.extend(raccoon_type_decl(name) for name in decoys)
    decls.extend(f"def instance inst{name} : Goal({name}) := {raccoon_mk('Goal', [name])}\n\n" for name in decoys)
    decls.append(f"def localGoal : Goal(LocalTarget) := {raccoon_mk('Goal', ['LocalTarget'])}\n\n")
    decls.append("def consume (A: Sort($u0))[goal: Goal(A)]: BenchUnit := BenchUnit.unit\n\n")
    decls.append(
        f"def withLocal [localInst: Goal(LocalTarget)]: BenchUnit := "
        f"consume(LocalTarget, {raccoon_derive('Goal(LocalTarget)')})\n\n"
    )
    decls.append(raccoon_bench(["withLocal(localGoal)"]))
    return "".join(decls)


def lean_local_instances(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    decoys = [f"LocalDecoy{i}" for i in range(size)]
    decls = [lean_header(no_prelude), lean_unit_decl(), lean_class("Goal", ["A"]), lean_type_decl("LocalTarget")]
    decls.extend(lean_type_decl(name) for name in decoys)
    decls.extend(f"noncomputable instance inst{name} : Goal {name} where\n  val := BenchUnit.unit\n\n" for name in decoys)
    decls.append("noncomputable def localGoal : Goal LocalTarget where\n  val := BenchUnit.unit\n\n")
    decls.append("axiom consume {A : Type u0} [Goal A] : BenchUnit\n\n")
    decls.append(
        """noncomputable def withLocal (_goal : Goal LocalTarget) : BenchUnit :=
  let _ : Goal LocalTarget := _goal
  consume (A := LocalTarget)

"""
    )
    decls.append(lean_bench(["withLocal localGoal"]))
    return "".join(decls)


def raccoon_defeq(size: int, _calls: int, _branch_depth: int) -> str:
    decls = [
        raccoon_prelude(),
        raccoon_struct("TC", ["A"]),
        raccoon_type_decl("Base"),
        """inductive Wrap (A: Sort($u0)) : Sort(u0)
 | mk : Wrap(A)

""",
    ]
    for idx in range(size):
        body = "Wrap(A)" if idx == 0 else f"Alias{idx - 1}(A)"
        decls.append(f"def Alias{idx} (A: Sort($u0)): Sort(u0) := {body}\n\n")
    decls.append(f"def instance baseTC : TC(Base) := {raccoon_mk('TC', ['Base'])}\n\n")
    decls.append(
        f"def instance wrapTC [inner: TC($A)]: TC(Wrap(A)) := {raccoon_mk('TC', ['Wrap(A)'])}\n\n"
    )
    decls.append("def consume (A: Sort($u0))[tc: TC(A)]: BenchUnit := BenchUnit.unit\n\n")
    target = "Wrap(Base)" if size == 0 else f"Alias{size - 1}(Base)"
    decls.append(raccoon_bench([f"consume({target}, {raccoon_derive(f'TC({target})')})"]))
    return "".join(decls)


def lean_defeq(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    decls = [
        lean_header(no_prelude),
        lean_unit_decl(),
        lean_class("TC", ["A"]),
        lean_type_decl("Base"),
        """inductive Wrap (A : Type u0) : Type u0 where
  | mk : Wrap A

""",
    ]
    for idx in range(size):
        body = "Wrap A" if idx == 0 else f"Alias{idx - 1} A"
        decls.append(f"abbrev Alias{idx} (A : Type u0) : Type u0 := {body}\n\n")
    decls.append("noncomputable instance baseTC : TC Base where\n  val := BenchUnit.unit\n\n")
    decls.append("noncomputable instance wrapTC {A : Type u0} [TC A] : TC (Wrap A) where\n  val := BenchUnit.unit\n\n")
    decls.append("axiom consume {A : Type u0} [TC A] : BenchUnit\n\n")
    target = "Wrap Base" if size == 0 else f"Alias{size - 1} Base"
    decls.append(lean_bench([f"consume (A := {target})"]))
    return "".join(decls)


def raccoon_shared_fanout(size: int, _calls: int, _branch_depth: int) -> str:
    dep_names = [f"Dep{i}" for i in range(size)]
    decls = [raccoon_prelude(), raccoon_struct("Need", ["A"]), raccoon_struct("Shared", ["A"])]
    decls.extend(raccoon_struct(dep, ["A"]) for dep in dep_names)
    decls.append(raccoon_type_decl("SharedTarget"))
    decls.append(f"def instance sharedTarget : Shared(SharedTarget) := {raccoon_mk('Shared', ['SharedTarget'])}\n\n")
    decls.extend(
        f"def instance inst{dep} [shared: Shared($A)]: {dep}(A) := {raccoon_mk(dep, ['A'])}\n\n"
        for dep in dep_names
    )
    if dep_names:
        binders = "".join(
            raccoon_instance_binder(f"d{i}", f"{dep}({'$A' if i == 0 else 'A'})")
            for i, dep in enumerate(dep_names)
        )
        decls.append(f"def instance needInst {binders}: Need(A) := {raccoon_mk('Need', ['A'])}\n\n")
    else:
        decls.append(f"def instance needInst : Need(SharedTarget) := {raccoon_mk('Need', ['SharedTarget'])}\n\n")
    decls.append("def consume (A: Sort($u0))[need: Need(A)]: BenchUnit := BenchUnit.unit\n\n")
    decls.append(raccoon_bench([f"consume(SharedTarget, {raccoon_derive('Need(SharedTarget)')})"]))
    return "".join(decls)


def lean_shared_fanout(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    dep_names = [f"Dep{i}" for i in range(size)]
    deps = "".join(f" [{dep} A]" for dep in dep_names)
    decls = [lean_header(no_prelude), lean_unit_decl(), lean_class("Need", ["A"]), lean_class("Shared", ["A"])]
    decls.extend(lean_class(dep, ["A"]) for dep in dep_names)
    decls.append(lean_type_decl("SharedTarget"))
    decls.append("noncomputable instance sharedTarget : Shared SharedTarget where\n  val := BenchUnit.unit\n\n")
    decls.extend(
        f"noncomputable instance inst{dep} {{A : Type u0}} [Shared A] : {dep} A where\n  val := BenchUnit.unit\n\n"
        for dep in dep_names
    )
    decls.append(f"noncomputable instance needInst {{A : Type u0}}{deps} : Need A where\n  val := BenchUnit.unit\n\n")
    decls.append("axiom consume {A : Type u0} [Need A] : BenchUnit\n\n")
    decls.append(lean_bench(["consume (A := SharedTarget)"]))
    return "".join(decls)


def raccoon_instance_body(size: int, _calls: int, _branch_depth: int) -> str:
    payload = raccoon_payload_chain(size)
    return (
        raccoon_prelude()
        + """inductive Payload : Type
 | leaf : Payload
 | node (left: Payload)(right: Payload) : Payload

struct Need (A: Sort($u0)) : Sort(u0)
 | mk (payload: Payload) : Need(A)

"""
        + raccoon_type_decl("BodyTarget")
        + f"def instance needInst : Need(BodyTarget) := Need.mk(BodyTarget, {payload})\n\n"
        + "def consume (A: Sort($u0))[need: Need(A)]: BenchUnit := BenchUnit.unit\n\n"
        + raccoon_bench([f"consume(BodyTarget, {raccoon_derive('Need(BodyTarget)')})"])
    )


def lean_instance_body(size: int, _calls: int, _branch_depth: int, no_prelude: bool) -> str:
    payload = lean_payload_chain(size)
    return (
        lean_header(no_prelude)
        + lean_unit_decl()
        + """inductive Payload : Type where
  | leaf : Payload
  | node (left : Payload) (right : Payload) : Payload

class Need (A : Type u0) : Type u0 where
  payload : Payload

"""
        + lean_type_decl("BodyTarget")
        + f"noncomputable instance needInst : Need BodyTarget where\n  payload := {payload}\n\n"
        + "axiom consume {A : Type u0} [Need A] : BenchUnit\n\n"
        + lean_bench(["consume (A := BodyTarget)"])
    )


RACCOON_GENERATORS: dict[str, Callable[[int, int, int], str]] = {
    "width": raccoon_width,
    "fanout": raccoon_fanout,
    "chain": raccoon_chain,
    "failures": raccoon_failures,
    "branching": raccoon_branching,
    "implicit-arity": raccoon_implicit_arity,
    "explicit-control": raccoon_explicit_control,
    "repeat-query": raccoon_repeat_query,
    "diamond": raccoon_diamond,
    "overlap": raccoon_overlap,
    "local-instances": raccoon_local_instances,
    "defeq": raccoon_defeq,
    "shared-fanout": raccoon_shared_fanout,
    "instance-body": raccoon_instance_body,
}

LEAN_GENERATORS: dict[str, Callable[[int, int, int, bool], str]] = {
    "width": lean_width,
    "fanout": lean_fanout,
    "chain": lean_chain,
    "failures": lean_failures,
    "branching": lean_branching,
    "implicit-arity": lean_implicit_arity,
    "explicit-control": lean_explicit_control,
    "repeat-query": lean_repeat_query,
    "diamond": lean_diamond,
    "overlap": lean_overlap,
    "local-instances": lean_local_instances,
    "defeq": lean_defeq,
    "shared-fanout": lean_shared_fanout,
    "instance-body": lean_instance_body,
}


def write_file(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents)


def scenario_sizes(args: argparse.Namespace, scenario: str) -> list[int]:
    if args.sizes is not None:
        return args.sizes
    specific = getattr(args, f"{scenario.replace('-', '_')}_sizes")
    if specific is not None:
        return specific
    return DEFAULT_SIZES[scenario]


def generate_raccoon(out_dir: Path, scenarios: Iterable[str], args: argparse.Namespace) -> None:
    for scenario in scenarios:
        generator = RACCOON_GENERATORS[scenario]
        for size in scenario_sizes(args, scenario):
            write_file(out_dir / f"typeclass_{scenario}_{size}.rac", generator(size, args.calls, args.branch_depth))


def generate_lean(out_dir: Path, scenarios: Iterable[str], args: argparse.Namespace) -> None:
    for scenario in scenarios:
        generator = LEAN_GENERATORS[scenario]
        for size in scenario_sizes(args, scenario):
            write_file(
                out_dir / f"typeclass_{scenario}_prelude_{size}.lean",
                generator(size, args.calls, args.branch_depth, False),
            )
            write_file(
                out_dir / f"typeclass_{scenario}_no_prelude_{size}.lean",
                generator(size, args.calls, args.branch_depth, True),
            )


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

    raise FileNotFoundError(
        f"could not find {filename}; run `sbt -no-colors compile` or pass --classpath"
    )


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
    name: str,
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
            return RunSummary(name, scenario, size, f"exit {code}", None, elapsed, elapsed, rep + 1, stderr_tail)
        timings.append(elapsed)

    return RunSummary(
        name=name,
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
    label = f"{summary.name}:{summary.scenario}"
    if summary.median is None:
        extra = f" stderr={summary.stderr_tail!r}" if summary.stderr_tail else ""
        print(f"{label:34s} {summary.size:6d} {summary.status:8s} time={summary.minimum:.4f}s{extra}")
    else:
        print(
            f"{label:34s} {summary.size:6d} ok       "
            f"median={summary.median:.4f}s min={summary.minimum:.4f}s max={summary.maximum:.4f}s reps={summary.reps}"
        )


def run_raccoon_jvm(args: argparse.Namespace, out_dir: Path, scenarios: Iterable[str]) -> None:
    classpath = args.classpath or default_classpath()
    for scenario in scenarios:
        for size in scenario_sizes(args, scenario):
            reps = reps_for_size(size, args.reps, args.large_reps, args.large_threshold)
            path = out_dir / f"typeclass_{scenario}_{size}.rac"
            command = [args.java, "-cp", classpath, "com.raccoonlang.Main", str(path)]
            print_summary(benchmark_command("raccoon-jvm", scenario, size, command, reps, args.timeout))


def run_raccoon_native(args: argparse.Namespace, out_dir: Path, scenarios: Iterable[str]) -> None:
    native_bin = Path(args.native_bin)
    if not native_bin.exists():
        raise FileNotFoundError(f"native binary not found: {native_bin}")
    for scenario in scenarios:
        for size in scenario_sizes(args, scenario):
            reps = reps_for_size(size, args.reps, args.large_reps, args.large_threshold)
            path = out_dir / f"typeclass_{scenario}_{size}.rac"
            command = [str(native_bin), str(path)]
            print_summary(benchmark_command("raccoon-native", scenario, size, command, reps, args.timeout))


def run_lean(args: argparse.Namespace, out_dir: Path, scenarios: Iterable[str], no_prelude: bool) -> None:
    mode = "no-prelude" if no_prelude else "prelude"
    file_mode = "no_prelude" if no_prelude else "prelude"
    for scenario in scenarios:
        for size in scenario_sizes(args, scenario):
            reps = reps_for_size(size, args.reps, args.large_reps, args.large_threshold)
            path = out_dir / f"typeclass_{scenario}_{file_mode}_{size}.lean"
            command = [args.lean, str(path)]
            print_summary(benchmark_command(f"lean-{mode}", scenario, size, command, reps, args.timeout))


def expand_runners(runners: list[str]) -> list[str]:
    expanded: list[str] = []
    for runner in runners:
        if runner == "all":
            expanded.extend(["jvm", "native", "lean-prelude", "lean-no-prelude"])
        elif runner == "lean-all":
            expanded.extend(["lean-prelude", "lean-no-prelude"])
        else:
            expanded.append(runner)
    return expanded


def expand_scenarios(scenarios: list[str]) -> list[str]:
    if not scenarios or "all" in scenarios:
        return list(DEFAULT_SCENARIOS)
    return scenarios


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--runner",
        action="append",
        choices=["generate", "jvm", "native", "lean-prelude", "lean-no-prelude", "lean-all", "all"],
        default=[],
        help="benchmark runner to execute; may be repeated",
    )
    parser.add_argument(
        "--scenario",
        action="append",
        choices=[*ALL_SCENARIOS, "all"],
        default=[],
        help="scenario to generate or run; may be repeated",
    )
    parser.add_argument("--out-dir", type=Path, default=Path("/tmp/raccoonlang-benchmarks/typeclass-resolution"))
    parser.add_argument("--sizes", type=parse_sizes, help="override sizes for every selected scenario")
    for scenario in ALL_SCENARIOS:
        parser.add_argument(f"--{scenario}-sizes", type=parse_sizes)
    parser.add_argument("--calls", type=int, default=1, help="independent query count for scenarios that support it")
    parser.add_argument("--branch-depth", type=int, default=8, help="recursive depth for the branching scenario")
    parser.add_argument("--reps", type=int, default=1, help="repetitions for sizes below --large-threshold")
    parser.add_argument("--large-reps", type=int, default=1)
    parser.add_argument("--large-threshold", type=int, default=128)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--java", default="java")
    parser.add_argument("--classpath", help="JVM classpath for com.raccoonlang.Main")
    parser.add_argument("--native-bin", default=str(REPO_ROOT / "native/target/scala-2.13/raccoon-release-full"))
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()

    if args.calls < 1:
        raise ValueError("--calls must be at least 1")
    if args.branch_depth < 0:
        raise ValueError("--branch-depth must be non-negative")

    runners = expand_runners(args.runner or ["generate"])
    scenarios = expand_scenarios(args.scenario)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    if any(runner in runners for runner in ["generate", "jvm", "native"]):
        generate_raccoon(args.out_dir, scenarios, args)
    if any(runner in runners for runner in ["generate", "lean-prelude", "lean-no-prelude"]):
        generate_lean(args.out_dir, scenarios, args)

    if runners == ["generate"]:
        print(f"generated benchmark sources in {args.out_dir}")
        return 0

    for runner in runners:
        if runner == "generate":
            continue
        if runner == "jvm":
            run_raccoon_jvm(args, args.out_dir, scenarios)
        elif runner == "native":
            run_raccoon_native(args, args.out_dir, scenarios)
        elif runner == "lean-prelude":
            run_lean(args, args.out_dir, scenarios, no_prelude=False)
        elif runner == "lean-no-prelude":
            run_lean(args, args.out_dir, scenarios, no_prelude=True)
        else:
            raise ValueError(f"unknown runner: {runner}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (FileNotFoundError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
