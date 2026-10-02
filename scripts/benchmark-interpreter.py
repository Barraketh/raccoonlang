#!/usr/bin/env python3
"""Compare two launchers on the GPU attention examples, checking identical output.

Run after building each launcher, with no builds or tests running concurrently:
  python3 scripts/benchmark-interpreter.py --baseline target/performance/raccoon-baseline \
      --candidate target/graalvm/raccoon --repeats 3 --output target/performance/results.json

Launcher arguments (including a JVM classpath) can be supplied as one quoted command.
"""

import argparse
import hashlib
import json
import platform
import re
import shlex
import statistics
import subprocess
import time
from pathlib import Path


def measure(command, example, mode):
    args = shlex.split(command) + [
        "--prelude", "gpu/Prelude.rac", "--root", "gpu", mode,
        f"gpu/encoding/examples/{example}.rac",
    ]
    if platform.system() == "Darwin":
        timed = ["/usr/bin/time", "-l"] + args
    else:
        timed = ["/usr/bin/time", "-f", "BENCH %U %S %M"] + args
    start = time.perf_counter()
    result = subprocess.run(timed, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    elapsed = time.perf_counter() - start
    stderr = result.stderr.decode()
    if platform.system() == "Darwin":
        user, system = re.search(r"([\d.]+) user\s+([\d.]+) sys", stderr).groups()
        rss = int(re.search(r"(\d+)\s+maximum resident set size", stderr)[1])
    else:
        user, system, kb = re.search(r"BENCH ([\d.]+) ([\d.]+) (\d+)", stderr).groups()
        rss = int(kb) * 1024
    return result.stdout, {
        "wall_seconds": round(elapsed, 3),
        "cpu_seconds": round(float(user) + float(system), 3),
        "rss_bytes": rss,
        "output_bytes": len(result.stdout),
        "sha256": hashlib.sha256(result.stdout).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--examples", nargs="+", default=["attention", "attention_pingpong", "attention_a3b"])
    parser.add_argument("--mode", choices=["raw", "json"], default="raw")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    records = []
    document = {"baseline": args.baseline, "candidate": args.candidate, "mode": args.mode, "runs": records}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for example in args.examples:
        expected = None
        for repeat in range(args.repeats):
            # Alternate order to reduce systematic bias from machine load and warming.
            order = ["baseline", "candidate"] if repeat % 2 == 0 else ["candidate", "baseline"]
            for label in order:
                output, metrics = measure(getattr(args, label), example, "--" + args.mode)
                if expected is None:
                    expected = output
                if output != expected:
                    raise RuntimeError(f"Output differs for {example}, {label}, repeat {repeat + 1}")
                record = {"example": example, "launcher": label, "repeat": repeat + 1, **metrics}
                records.append(record)
                args.output.write_text(json.dumps(document, indent=2) + "\n")
                print(json.dumps(record), flush=True)
        medians = {
            label: statistics.median(r["wall_seconds"] for r in records
                                     if r["example"] == example and r["launcher"] == label)
            for label in ["baseline", "candidate"]
        }
        print(f"{example}: {medians['baseline']:.3f}s -> {medians['candidate']:.3f}s "
              f"({medians['baseline'] / medians['candidate']:.2f}x)", flush=True)


if __name__ == "__main__":
    main()
