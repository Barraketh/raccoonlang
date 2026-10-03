#!/usr/bin/env python3
"""Check compositional contracts, counterexamples, and certified CUDA lowering."""
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def compiler_command(roots):
    if os.environ.get("RACCOON"):
        executable = shlex.split(os.environ["RACCOON"])
    else:
        classpath = ROOT / "target/graalvm/classpath.txt"
        if not classpath.exists():
            raise SystemExit("Set RACCOON or run sbt graalvmNativeImageClasspath first.")
        executable = ["java", "-cp", classpath.read_text().strip(), "com.raccoonlang.Main"]
    command = executable + ["--prelude", str(ROOT / "gpu/Prelude.rac")]
    for path in roots:
        command += ["--root", str(path)]
    return command


def check_experiment(here, roots, smoke):
    command = compiler_command(roots)
    jobs = [(path, "accept") for path in sorted(here.glob("*.rac"))]
    for path in sorted((here / "checks").glob("*.rac")):
        first = path.read_text().splitlines()[0]
        if not first.startswith("// expect: "):
            raise ValueError(f"Missing diagnostic expectation: {path}")
        jobs.append((path, first.removeprefix("// expect: ")))

    def check(job):
        path, expectation = job
        result = subprocess.run(command + ["--json", str(path)], cwd=ROOT,
                                capture_output=True, text=True, timeout=120)
        try:
            diagnostics = json.loads(result.stdout)
            kinds = {item["kind"] for item in diagnostics}
            local = all(Path(item["path"]).resolve() == path.resolve() for item in diagnostics)
            obligation = all("in definition Rejected.bad" in item["notes"] for item in diagnostics)
        except (ValueError, TypeError, KeyError):
            return path, False, result.stdout + result.stderr
        passed = (result.returncode == 0 and not diagnostics) if expectation == "accept" else (
            result.returncode == 1 and kinds == {expectation} and local and obligation)
        return path, passed, result.stdout + result.stderr

    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(check, jobs))
    failures = [(path, detail) for path, passed, detail in results if not passed]
    for path, detail in failures:
        print(f"FAIL {path.name}\n{detail}")
    accepted = sum(expectation == "accept" for _, expectation in jobs)
    print(f"{len(jobs) - len(failures)}/{len(jobs)} checks passed "
          f"({accepted} accepted; {len(jobs) - accepted} rejected).", flush=True)
    if failures:
        raise SystemExit(1)

    rendered = subprocess.run(command + ["--raw", str(here / "Render.rac")], cwd=ROOT,
                              capture_output=True, text=True, timeout=120)
    rendered.check_returncode()
    cuda = rendered.stdout
    smoke(cuda)
    # Retained for inspection; the checked AST and existing Cuda renderer produce it.
    (here / "generated.cu").write_text(cuda)
    compiler = shutil.which("clang++")
    if compiler:
        rewritten = subprocess.run(["python3", str(ROOT / "gpu/stub/asm_calls.py")],
                                   input=cuda, capture_output=True, text=True, check=True)
        subprocess.run([compiler, "-std=c++17", "-fsyntax-only", "-Wall", "-Werror",
                        "-Wno-parentheses-equality", "-I", str(ROOT / "gpu/stub"),
                        "-include", str(ROOT / "gpu/stub/cuda_stub.h"), "-x", "c++", "-"],
                       input=rewritten.stdout, text=True, check=True)
        print("Certified CUDA emitted; host C++ syntax check passed.")
    else:
        print("Certified CUDA emitted; host C++ check skipped (clang++ unavailable).")
