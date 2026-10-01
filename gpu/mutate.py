# Runs a table of mutations of an example: each mutant replaces one snippet of the example's source and must be
# refused with a given diagnostic kind (whose message, if the mutant says so, mentions a given name).
#
#   python3 gpu/mutate.py [-v] gpu/rejected/tinygemm_mutants.py     (with $RACCOON set, as for check.sh)
#
# -v prints every diagnostic of every mutant.
#
# A table is a Python file defining SOURCE (the example, relative to gpu/) and MUTANTS, a list of dicts with keys
# name, expect, why, old, new, and optionally mentions; a mutant that changes several places gives `edits`, a list of
# (old, new) pairs, in place of old and new. Each `old` must occur exactly once in the source.
#
# A mutant whose `expect` is "Spill" must instead generate, and fail the register check (toolkit/registers.py) with a
# report that mentions its `mentions`. It needs the CUDA toolkit's container, so it runs only when $CUDA_TOOLKIT is set,
# as check.sh sets it when the container is there.
import concurrent.futures, json, os, runpy, shlex, shutil, subprocess, sys, tempfile

here = os.path.dirname(os.path.abspath(__file__))
raccoon = shlex.split(os.environ.get("RACCOON") or sys.exit("set RACCOON to a raccoon launcher"))
verbose = "-v" in sys.argv[1:]
table = runpy.run_path([a for a in sys.argv[1:] if a != "-v"][0])
source = open(os.path.join(here, table["SOURCE"])).read()
stem = os.path.splitext(os.path.basename(table["SOURCE"]))[0]
scratch = tempfile.mkdtemp(prefix="mutants-")

def run(*args):
    return subprocess.run(raccoon + ["--prelude", os.path.join(here, "Prelude.rac"), "--root", here, *args],
                          capture_output=True, text=True)

def check(m):
    label = f"{stem}/{m['name']}"
    mutated = source
    for old, new in m.get("edits", [(m.get("old"), m.get("new"))]):
        if source.count(old) != 1:
            return False, f"FAIL {label}: a snippet occurs {source.count(old)} times in {table['SOURCE']}"
        mutated = mutated.replace(old, new)
    path = os.path.join(scratch, m["name"] + ".rac")
    with open(path, "w") as f:
        f.write(mutated)
    if m["expect"] == "Spill":
        generated = run("--raw", path)
        if "error:" in generated.stdout + generated.stderr:
            return False, f"FAIL {label}: expected a kernel, got:\n{generated.stdout}{generated.stderr}"
        judged = subprocess.run([sys.executable, os.path.join(here, "toolkit", "registers.py")], input=generated.stdout,
                                capture_output=True, text=True)
        if judged.returncode != 0 and m["mentions"] in judged.stdout:
            return True, f"ok   {label} -> Spill"
        return False, f"FAIL {label}: expected a spill mentioning {m['mentions']}, got:\n{judged.stdout}"
    try:
        diags = json.loads(run("--json", path).stdout)
    except json.JSONDecodeError:
        return False, f"FAIL {label}: crashed"
    kinds = " ".join(d["kind"] for d in diags)
    if verbose:
        kinds += "".join(f"\n       L{d['startLine']} {d['kind']}: {d['message']}" for d in diags)
    hit = [d for d in diags if d["kind"] == m["expect"] and m.get("mentions", "") in d["message"]]
    if hit:
        return True, f"ok   {label} -> {kinds}"
    return False, f"FAIL {label}: expected {m['expect']}" + (f" mentioning {m['mentions']}" if "mentions" in m else "") + \
        f", got: " + "; ".join(f"L{d['startLine']} {d['kind']}: {d['message']}" for d in diags)

with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count() or 4) as pool:
    mutants = [m for m in table["MUTANTS"] if m["expect"] != "Spill" or os.environ.get("CUDA_TOOLKIT")]
    results = list(pool.map(check, mutants))
shutil.rmtree(scratch)
for ok, line in results:
    print(line)
sys.exit(0 if all(ok for ok, _ in results) else 1)
