"""Shared process timing and sbt runtime-classpath support for benchmarks."""

from __future__ import annotations

import statistics
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


@dataclass
class TimingSummary:
    status: str
    median: float | None
    minimum: float
    maximum: float
    reps: int
    stderr_tail: str


def load_runtime_classpath(repo_root: Path, override: str | None) -> str:
    if override is not None:
        return override

    classpath_file = repo_root / "target/runtime-classpath.txt"
    if not classpath_file.is_file():
        raise FileNotFoundError(
            f"missing {classpath_file}; run `sbt -no-colors compile runtimeClasspath` or pass --classpath"
        )
    return classpath_file.read_text().strip()


def _run_once(command: list[str], timeout: float | None) -> tuple[int, float, str]:
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


def measure_command(command: list[str], reps: int, timeout: float | None) -> TimingSummary:
    timings: list[float] = []
    stderr_tail = ""
    for rep in range(reps):
        code, elapsed, stderr = _run_once(command, timeout)
        stderr_tail = "\n".join(line for line in stderr.strip().splitlines()[-4:] if line.strip())
        if code != 0:
            return TimingSummary(f"exit {code}", None, elapsed, elapsed, rep + 1, stderr_tail)
        timings.append(elapsed)

    return TimingSummary(
        status="ok",
        median=statistics.median(timings),
        minimum=min(timings),
        maximum=max(timings),
        reps=reps,
        stderr_tail=stderr_tail,
    )
