# The register check (gpu/encoding/REGISTERS.md §5): compiles a file of generated kernels with the CUDA toolkit
# (cuda.sh), as the hardware session does, and judges each kernel's registers by `ptxas -v`, its SASS and its
# `setmaxnreg`s.
#
#   python3 gpu/toolkit/registers.py < kernels.cu
#
# It prints one line per kernel, its registers, budget and spills, and fails when the file has no kernel, when `ptxas`
# warns, or when a kernel
# - uses more registers per thread than its budget: what its `__launch_bounds__(threads, residency)` leave, the rule of
#   `Registers.budget` (gpu/encoding/Registers.rac), ⌊65536 / (threads · residency)⌋ rounded down to 8, at most 255;
# - spills: `ptxas -v` reports spill stores or loads, or its SASS has a local-memory instruction (`STL`, `LDL`). Each
#   such instruction is attributed, by its line in the kernel's source (`-lineinfo`), to the role it lies in: the block
#   that starts with a warpgroup's first `setmaxnreg` (`Core.withShare`);
# - changes counts, and does not enter at its budget (A59), or its `setmaxnreg`s are not splits of the CTA's pool at
#   that budget: in each split, every warpgroup's first change goes from the budget to its count (`.inc` up, `.dec`
#   down), every change back goes from its count to the budget, and the counts fit the pool,
#   threads/4 · Σ counts ≤ threads · budget (`Registers.fits`).
import os, re, subprocess, sys

here = os.path.dirname(os.path.abspath(__file__))
source_name = "/tmp/k.cu"
compile_and_disassemble = (
    f"cd /tmp && cat > {source_name}"
    f" && nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a -c -lineinfo -Xptxas -v {source_name} -o k.o 2>&1"
    " && echo @@sass && cuobjdump -xelf all k.o > /dev/null && nvdisasm -g -c *.cubin")

def budget(threads, residency):
    return min(255, 8 * (65536 // (threads * residency) // 8))

def kernels(lines):
    """Each kernel's name, its bounds, and the lines of the source from its head to the next kernel's."""
    heads = [(i, line) for i, line in enumerate(lines) if "__global__" in line]
    for n, (i, line) in enumerate(heads):
        end = heads[n + 1][0] if n + 1 < len(heads) else len(lines)
        name = re.search(r"__global__ void (?:__\w+__\([^)]*\) )*(\w+)\(", line).group(1)
        bounds = re.search(r"__launch_bounds__\((\d+), (\d+)\)", line)
        yield name, bounds and (int(bounds.group(1)), int(bounds.group(2))), range(i, end)

def changes(lines, span):
    """The `setmaxnreg`s in `span`, in order, as (line index, action, count, warpgroup): a change back sits alone in a
    block guarded by its warpgroup, `warp / 4 == k`, and has that k; a warpgroup's first change has None."""
    out = []
    for i in span:
        m = re.search(r'"setmaxnreg\.(inc|dec)\.sync\.aligned\.u32 (\d+);', lines[i])
        if m:
            back = re.search(r"/ 4u\) == (\d+)u\)\) \{$", lines[i - 1])
            out.append((i, m.group(1), int(m.group(2)), back and int(back.group(1))))
    return out

def splits(found):
    """The changes grouped by split: its first changes, then its changes back."""
    groups = []
    for change in found:
        first = change[3] is None
        if not groups or (first and groups[-1][1]):
            groups.append(([], []))
        groups[-1][0 if first else 1].append(change)
    return groups

def split_faults(groups, threads, limit):
    """What breaks the rule of a split of the CTA's pool at `limit` per thread."""
    faults = []
    for firsts, backs in groups:
        at = firsts[0][0] + 1 if firsts else backs[0][0] + 1
        for i, action, count, k in firsts:
            if (action == "inc") != (count > limit) or count == limit:
                faults.append(f"line {i + 1}: setmaxnreg.{action} {count} does not change from the budget {limit}")
        for i, action, count, k in backs:
            if count != limit:
                faults.append(f"line {i + 1}: a change back to {count}, not to the budget {limit}")
        if len(firsts) != len(backs):
            faults.append(f"the split at line {at}: {len(firsts)} first changes but {len(backs)} changes back")
            continue
        for (_, _, count, _), (i, action, _, _) in zip(firsts, sorted(backs, key=lambda c: c[3])):
            if (action == "inc") != (count < limit):
                faults.append(f"line {i + 1}: setmaxnreg.{action} cannot go back from {count} to {limit}")
        total = sum(count for _, _, count, _ in firsts) + (4 - len(firsts)) * limit
        if threads // 4 * total > threads * limit:
            faults.append(f"the split at line {at}: its counts need {threads // 4 * total} registers of the pool's "
                          f"{threads * limit}")
    return faults

def roles(lines, span):
    """The roles in `span`: each block that starts with a warpgroup's first `setmaxnreg`, as (first line, last line,
    the instruction), 1-based. A block ends before the first line indented less than its first."""
    out = []
    for i, action, count, k in changes(lines, span):
        if k is not None:
            continue
        indent = len(lines[i]) - len(lines[i].lstrip())
        j = i + 1
        while j < span.stop and len(lines[j]) - len(lines[j].lstrip()) >= indent:
            j += 1
        out.append((i + 1, j, f"setmaxnreg.{action} {count}"))
    return out

def ptxas_report(text):
    """Per kernel: registers, spill stores and spill loads, in bytes."""
    report, name = {}, None
    for line in text.splitlines():
        m = re.search(r"Compiling entry function '(\w+)'", line) or re.search(r"Function properties for (\w+)", line)
        if m:
            name = m.group(1)
            report.setdefault(name, {})
        m = re.search(r"(\d+) bytes spill stores, (\d+) bytes spill loads", line)
        if m and name:
            report[name]["stores"], report[name]["loads"] = int(m.group(1)), int(m.group(2))
        m = re.search(r"Used (\d+) registers", line)
        if m and name:
            report[name]["registers"] = int(m.group(1))
    return report

def local_memory(sass):
    """Per kernel: the source line of each local-memory instruction, the last line of the kernel's own source that the
    line info named before it (it also names lines of the CUDA headers, which are skipped)."""
    found, name, line = {}, None, None
    for text in sass.splitlines():
        m = re.match(r"\.text\.(\w+):", text)
        if m:
            name, line = m.group(1), None
        m = re.search(r'//## File "([^"]*)", line (\d+)', text)
        if m and m.group(1) == source_name:
            line = int(m.group(2))
        if name and re.search(r"\b(STL|LDL)(\.\w+)*\s", text):
            found.setdefault(name, []).append(line)
    return found

def main():
    source = sys.stdin.read()
    lines = source.split("\n")
    run = subprocess.run([os.path.join(here, "cuda.sh"), "sh", "-c", compile_and_disassemble], input=source,
                         capture_output=True, text=True)
    if run.returncode != 0 or "@@sass" not in run.stdout:
        print("FAIL ptxas: the kernels do not compile")
        print(run.stdout + run.stderr)
        return 1
    ptxas, sass = run.stdout.split("@@sass", 1)
    report, local = ptxas_report(ptxas), local_memory(sass)
    status = 0
    warnings = [line for line in ptxas.splitlines() if "warning" in line]
    if warnings:
        print("FAIL ptxas: warnings\n" + "\n".join(warnings))
        status = 1
    found = list(kernels(lines))
    if not found:
        print("FAIL ptxas: no kernel")
        return 1
    for name, bounds, span in found:
        r = report.get(name, {})
        if not bounds or "registers" not in r:
            print(f"FAIL ptxas {name}: " + ("no launch bounds" if not bounds else "no report from ptxas"))
            status = 1
            continue
        limit = budget(*bounds)
        line = f"{name}: {r['registers']} registers, budget {limit}, spills {r['stores']} B stored and {r['loads']} B loaded"
        faults = []
        if r["registers"] > limit:
            faults.append("over its budget")
        if r["stores"] or r["loads"]:
            faults.append("it spills")
        groups = splits(changes(lines, span))
        if groups and r["registers"] != limit:
            faults.append(f"it changes counts but enters at {r['registers']}, not its budget")
        faults += split_faults(groups, bounds[0], limit)
        branches = roles(lines, span)
        places = {}
        for at in local.get(name, []):
            where = [f"the role at line {first} ({op})" for first, last, op in branches if at and first <= at <= last]
            place = where[0] if where else "no role"
            places[place] = places.get(place, 0) + 1
        for place, count in places.items():
            faults.append(f"{count} local-memory instructions in {place}")
        if faults:
            print(f"FAIL ptxas {line}: " + "; ".join(faults))
            status = 1
        else:
            print(f"ok   ptxas {line}")
    return status

sys.exit(main())
