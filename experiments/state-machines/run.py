#!/usr/bin/env python3
"""Compare explicit certificates and proof-producing transition inference.

The Python renderer is untrusted: it never decides whether a transition is legal.
Raccoon checks both paths against the same inductive Step declarations.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
MODULES = {"registers": "RegisterProtocol", "reads": "ReadProtocol", "actors": "ActorProtocol"}


def rac_list(ty, items):
    result = f"List.nil({ty})"
    for item in reversed(items):
        result = f"List.cons({item}, {result})"
    return result


def render(case, mode):
    module = MODULES[case["protocol"]]
    namespace = "Example" if case.get("example") else "Case"
    declarations = []
    parameter = ""
    if case["protocol"] == "registers":
        kernel, threads, residency = case.get("config", [1, 512, 1])
        declarations.append(f"def cfg: {module}.Config := {module}.Config.mk({kernel}, {threads}, {residency})")
        counts = ", ".join(map(str, case.get("counts", [192, 192, 72, 56])))
        declarations.append(f"def counts: {module}.Counts := {module}.Counts.mk({counts})")
        parameter = namespace + ".cfg"
    elif case["protocol"] == "reads":
        parameter = str(case.get("loan", 7))
    relation = f"{module}.relation" + (f"({parameter})" if parameter else "")

    def state(name):
        args = f"({namespace}.counts)" if name in ("split", "joined", "restoring") else ""
        return f"{module}.State.{name}{args}"

    events, witnesses = [], []
    for source in case["events"]:
        words = source.split()
        name, arguments = words[0], words[1:]
        if case["protocol"] == "registers" and name == "split":
            arguments = [namespace + ".counts"]
        args = ", ".join(arguments)
        events.append(f"{module}.Event.{name}" + (f"({args})" if args else ""))
        proof_args = ([parameter] if parameter else []) + arguments
        if case["protocol"] == "registers":
            if name in ("join", "restore", "barrier"):
                proof_args.append(namespace + ".counts")
            elif name in ("initialize", "split"):
                proof_args.append("Eq.refl(Bool.true)")
        elif case["protocol"] == "reads" and name in ("beginRead", "read", "close"):
            proof_args.append("Eq.refl(Bool.true)")
        witnesses.append(f"{module}.Step.{name}" + (f"({', '.join(proof_args)})" if proof_args else ""))

    states = list(map(state, case["states"]))
    if len(states) != len(events) + 1:
        raise ValueError(f"{case['name']}: annotate one state before and after every event")
    goal = state(case["goal"])
    event_list = rac_list(f"{module}.Event", events)
    command_type = f"Protocol.Command({module}.State, {module}.Event, {relation}, {states[0]}, {goal})"
    declarations.append(f"def events: List({module}.Event) := {event_list}")
    if mode == "inferred":
        chooser = f"fun (s: {module}.State)(event: {module}.Event): {module}.Choice(" + (f"{parameter}, " if parameter else "") + "s, event) => " + f"{module}.choose(" + (f"{parameter}, " if parameter else "") + "s, event)"
        inferred = f"Protocol.infer({relation}, {chooser}, {states[0]}, {namespace}.events)"
        body = f"Protocol.require({inferred}, {goal}, Eq.refl(Option.some({goal})))"
    else:
        proof = f"Protocol.Run.done({relation}, {states[-1]})"
        for index in reversed(range(len(events))):
            proof = f"Protocol.Run.more({states[index]}, {events[index]}, {states[index + 1]}, {witnesses[index]}, {proof})"
        body = f"Protocol.Command.mk({namespace}.events, {proof})"
    declarations.append(f"def command: {command_type} := {body}")
    return f"import Protocol\nimport {module}\n\nnamespace {namespace} {{\n  " + "\n  ".join(declarations) + "\n}\n"


def executable():
    if os.environ.get("RACCOON"):
        return shlex.split(os.environ["RACCOON"])
    classpath_file = ROOT / "target/graalvm/classpath.txt"
    if not classpath_file.exists():
        raise SystemExit("Set RACCOON to the CLI command, or run sbt graalvmNativeImageClasspath first.")
    return ["java", "-cp", classpath_file.read_text().strip(), "com.raccoonlang.Main"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit", type=Path, help="Retain generated .rac fixtures at this path")
    options = parser.parse_args()
    cases = json.loads((HERE / "cases.json").read_text())
    command = executable() + ["--prelude", str(ROOT / "gpu/Prelude.rac"), "--root", str(HERE), "--root", str(ROOT / "gpu"), "--json"]
    with tempfile.TemporaryDirectory(prefix="raccoon-protocol-") as temporary:
        output = options.emit.resolve() if options.emit else Path(temporary)
        output.mkdir(parents=True, exist_ok=True)
        jobs = []
        for case in cases:
            for mode in ("explicit", "inferred"):
                path = output / f"{case['name']}_{mode}.rac"
                path.write_text(render(case, mode))
                jobs.append((case["name"] + "/" + mode, path, case["accept"], {"TypeMismatch"}))
        for path in sorted(HERE.glob("*.rac")):
            jobs.append((path.name, path, True, set()))
        for path in sorted((HERE / "checks").glob("*.rac")):
            expectation = path.read_text().splitlines()[0]
            if not expectation.startswith("// expect: "):
                raise ValueError(f"Missing expectation in {path}")
            kind = expectation.removeprefix("// expect: ")
            jobs.append((path.name, path, kind == "accept", {kind}))

        def check(job):
            name, path, accept, expected_kinds = job
            result = subprocess.run(command + [str(path)], cwd=ROOT, text=True, capture_output=True, timeout=90)
            try:
                diagnostics = json.loads(result.stdout)
                kinds = {diagnostic["kind"] for diagnostic in diagnostics}
            except (ValueError, TypeError, KeyError):
                return name, False, "CLI did not return diagnostic JSON: " + result.stdout + result.stderr
            local = all(Path(diagnostic["path"]).resolve() == path.resolve() for diagnostic in diagnostics)
            fixture = name.endswith("/explicit") or name.endswith("/inferred")
            obligation = not fixture or all("in definition Case.command" in diagnostic["notes"] for diagnostic in diagnostics)
            passed = (result.returncode == 0 and not diagnostics) if accept else (result.returncode == 1 and bool(kinds) and kinds <= expected_kinds and local and obligation)
            return name, passed, result.stdout + result.stderr

        with ThreadPoolExecutor(max_workers=4) as pool:
            results = list(pool.map(check, jobs))
        failures = [(name, detail) for name, passed, detail in results if not passed]
        for name, detail in failures:
            print(f"FAIL {name}\n{detail}")
        accepted = sum(accept for _, _, accept, _ in jobs)
        print(f"{len(jobs) - len(failures)}/{len(jobs)} checks passed ({accepted} accepted; {len(jobs) - accepted} rejected).")
        if failures:
            raise SystemExit(1)


if __name__ == "__main__":
    main()
