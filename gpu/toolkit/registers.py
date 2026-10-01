# The register check (gpu/encoding/REGISTERS.md §5): compiles a file of generated kernels with the CUDA toolkit
# (cuda.sh), as the hardware session does, and judges each kernel's registers by `ptxas -v` and its SASS.
#
#   python3 gpu/toolkit/registers.py < kernels.cu
#
# It prints one line per kernel, its registers, budget and spills, and fails when a kernel
# - uses more registers per thread than its budget: what its `__launch_bounds__(threads, residency)` leave, the rule of
#   `Registers.budget` (gpu/encoding/Registers.rac), ⌊65536 / (threads · residency)⌋ rounded down to 8, at most 255;
# - spills: `ptxas -v` reports spill stores or loads, or its SASS has a local-memory instruction (`STL`, `LDL`). Each
#   such instruction is attributed, by its source line (`-lineinfo`), to the role it lies in: the block that starts
#   with a `setmaxnreg`, which is a warpgroup's branch (`Core.withShare`). A kernel's line info can name a line of
#   another kernel of the file, whose code is the same, so the roles are looked up in the whole file;
# - changes counts and is not given its budget at entry, which every warpgroup's first `setmaxnreg` assumes (A59).
import os, re, subprocess, sys

here = os.path.dirname(os.path.abspath(__file__))
compile_and_disassemble = (
    "cd /tmp && cat > k.cu"
    " && nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a -c -lineinfo -Xptxas -v k.cu -o k.o 2>&1"
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

def roles(lines):
    """Each block that starts with a `setmaxnreg`, as (first line, last line, the instruction), 1-based. A block ends
    before the first line indented less than its first."""
    out = []
    for i in range(len(lines)):
        m = re.search(r'"(setmaxnreg[^;"]*)', lines[i])
        if not m:
            continue
        indent = len(lines[i]) - len(lines[i].lstrip())
        j = i + 1
        while j < len(lines) and len(lines[j]) - len(lines[j].lstrip()) >= indent:
            j += 1
        out.append((i + 1, j, m.group(1)))
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
    """Per kernel: the source line of each local-memory instruction."""
    found, name, line = {}, None, None
    for text in sass.splitlines():
        m = re.match(r"\.text\.(\w+):", text)
        if m:
            name, line = m.group(1), None
        m = re.search(r'//## File ".*", line (\d+)', text)
        if m:
            line = int(m.group(1))
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
    report, local, branches = ptxas_report(ptxas), local_memory(sass), roles(lines)
    status = 0
    for name, bounds, span in kernels(lines):
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
        if any(first - 1 in span for first, last, op in branches) and r["registers"] != limit:
            faults.append(f"it changes counts but enters at {r['registers']}, not its budget")
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
