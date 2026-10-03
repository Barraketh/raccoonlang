#!/usr/bin/env python3
"""Kernel-independent safety proofs, counterexamples and semantic mutations."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE.parent))
from check_experiment import check_experiment, compiler_command

ROOTS = [HERE, HERE.parent / "compositional-machines", HERE.parent / "machine-core/full", HERE.parent / "extensible-machines", ROOT / "gpu"]


def check(path, roots):
    result = subprocess.run(compiler_command(roots) + ["--json", str(path)],
                            capture_output=True, text=True, timeout=120)
    try:
        diagnostics = json.loads(result.stdout)
    except ValueError:
        raise AssertionError(result.stdout + result.stderr)
    return result, diagnostics


def smoke(cuda):
    assert "cp.async.bulk.wait_group 0" in cuda
    assert "cp.async.bulk.wait_group.read" not in cuda
    assert "cp.async.bulk.commit_group" in cuda
    assert "for (unsigned v0" in cuda


def representation_probe():
    # Constructor authority exists only in the temporary defining-module copy.
    # Never load/launch this kernel on hardware.
    with tempfile.TemporaryDirectory(prefix="raccoon-representation-") as tmp:
        overlay = Path(tmp)
        target = overlay / "encoding/Lowering.rac"
        target.parent.mkdir()
        target.write_text((ROOT / "gpu/encoding/Lowering.rac").read_text() +
                          (HERE / "probes/Representation.inc").read_text())
        result, diagnostics = check(HERE / "probes/Representation.rac", [overlay] + ROOTS)
        assert result.returncode == 0 and not diagnostics, result.stdout + result.stderr
        rendered = subprocess.run(compiler_command([overlay] + ROOTS) +
                                  ["--raw", str(HERE / "probes/Representation.rac")],
                                  capture_output=True, text=True, timeout=120)
        rendered.check_returncode()
        assert "if ((threadIdx.x == 0u))" in rendered.stdout
        assert "__syncthreads();" in rendered.stdout
        (HERE / "representation-counterexample.cu").write_text(rendered.stdout)
    print("Representation probe: checker accepts a divergent CTA barrier; emitted only, never launched.", flush=True)


def mutations():
    originals = {
        "encoding/Lowering.rac": (ROOT / "gpu/encoding/Lowering.rac").read_text(),
        "encoding/Registers.rac": (ROOT / "gpu/encoding/Registers.rac").read_text(),
        **{name + ".rac": (HERE / (name + ".rac")).read_text() for name in ["Concurrent", "Tensor", "Claims", "Outputs", "Coverage", "HappensBefore", "Coupled"]},
        "Target.rac": (HERE / "Target.rac").read_text(),
        "Retirement.rac": (HERE / "Retirement.rac").read_text(),
    }
    trials = [
        ("read-only wait", "encoding/Lowering.rac",
         "def bulkWait (pending: Nat): Stmt := Stmt.instr(Instr.bulkWait(BulkWait.complete, pending))",
         "def bulkWait (pending: Nat): Stmt := Stmt.instr(Instr.bulkWait(BulkWait.read, pending))",
         "Target.rac", "in definition Target.compile"),
        ("omitted drain", "Target.rac", "Compiled.mk(code, start, Target.drainImplementation, Interprets.drain)",
         "Compiled.mk(code, start, Block.done, Interprets.drain)", "Target.rac", "in definition Target.compile"),
        ("unfinished async work", "Retirement.rac", "Contracts.Outcome.ok(State.mk(Bool.false, 0))",
         "Contracts.Outcome.ok(State.mk(Bool.false, s.pending))", "Retirement.rac", "in definition Retirement.finishSafe"),
        ("early consumer read", "Concurrent.rac",
         "| Slot.full => Outcome.ran(State.mk(Bool.true, s.producer, Endpoint.mk(Phase.held, s.consumer.round), Slot.reading, s.round, s.async))",
         "| Slot.pending => Outcome.ran(State.mk(Bool.true, s.producer, Endpoint.mk(Phase.held, s.consumer.round), Slot.reading, s.round, s.async))",
         "Concurrent.rac", "in definition Concurrent.preserve"),
        ("overwrite before release", "Concurrent.rac",
         "| Slot.empty => Outcome.ran(State.mk(Bool.true, Endpoint.mk(Phase.held, s.producer.round), s.consumer, Slot.writing, s.round, s.async))",
         "| Slot.full => Outcome.ran(State.mk(Bool.true, Endpoint.mk(Phase.held, s.producer.round), s.consumer, Slot.writing, s.round, s.async))",
         "Concurrent.rac", "in definition Concurrent.preserve"),
        ("producer counter not advanced", "Concurrent.rac", "Endpoint.mk(Phase.ready, Nat.succ(s.producer.round))",
         "Endpoint.mk(Phase.ready, s.producer.round)", "Concurrent.rac", "in definition Concurrent.preserve"),
        ("consumer counter not advanced", "Concurrent.rac", "Endpoint.mk(Phase.ready, Nat.succ(s.consumer.round))",
         "Endpoint.mk(Phase.ready, s.consumer.round)", "Concurrent.rac", "in definition Concurrent.preserve"),
        ("allocation permit retained", "Tensor.rac", "State.mk(Phase.live, Tensor.columns(c), Bool.false, Bool.true, s.async)",
         "State.mk(Phase.live, Tensor.columns(c), Bool.true, Bool.true, s.async)", "Tensor.rac", "in definition Tensor.preserve"),
        ("failed CAS overwrites owner", "Claims.rac", "Claims.choose(Claims.equal(s.word, snapshot), State.mk(Word.mk(epoch, owner), List.cons(owner, s.winners)), s)",
         "Claims.choose(Bool.true, State.mk(Word.mk(epoch, owner), List.cons(owner, s.winners)), s)", "Claims.rac", "in definition Claims.preserve"),
        ("permission not consumed", "Outputs.rac", "Erase(address, List.cons(address, rest), rest)",
         "Erase(address, List.cons(address, rest), List.cons(address, rest))", "Outputs.rac", "in definition Outputs.unavailable"),
        ("thread-dependent branch substituted", "Coverage.rac", "Coverage.condition(condition, input, thread)",
         "Coverage.condition(Condition.threadIs(0), input, thread)", "Coverage.rac", "in definition Coverage.everyParticipant"),
        ("synchronization edge omitted", "HappensBefore.rac", "EdgeKind.synchronize(s.owner, to))",
         "EdgeKind.programOrder(s.owner))", "HappensBefore.rac", "in definition HappensBefore.newEdgeValid"),
        ("producer acquisition handoff omitted", "Coupled.rac", "| Action.acquire => HappensBefore.after(HappensBefore.Action.handoff(0), h)",
         "| Action.acquire => h", "Coupled.rac", "in definition Coupled.preserve"),
        ("consumer wait handoff omitted", "Coupled.rac", "| Action.await => HappensBefore.after(HappensBefore.Action.handoff(1), h)",
         "| Action.await => h", "Coupled.rac", "in definition Coupled.preserve"),
        ("async proxy handoff omitted", "Coupled.rac", "| Action.issue => HappensBefore.after(HappensBefore.Action.access(2, Bool.true), HappensBefore.after(HappensBefore.Action.handoff(2), h))",
         "| Action.issue => HappensBefore.after(HappensBefore.Action.access(2, Bool.true), h)", "Coupled.rac", "in definition Coupled.preserve"),
        ("register pool detached from metadata", "encoding/Registers.rac", "Nat.mul(512, perThread)))",
         "65536))", "Budgets.rac", "in definition Budgets.fitsSound"),
    ]
    for name, module, before, after, entry, obligation in trials:
        assert originals[module].count(before) == 1
        with tempfile.TemporaryDirectory(prefix="raccoon-proof-mutation-") as tmp:
            overlay = Path(tmp)
            changed = overlay / module
            changed.parent.mkdir(parents=True, exist_ok=True)
            changed.write_text(originals[module].replace(before, after))
            # Check the changed file itself if it is the proof's entry module.
            path = changed if module == entry else HERE / entry
            result, diagnostics = check(path, [overlay] + ROOTS)
            assert result.returncode == 1 and diagnostics, result.stdout + result.stderr
            assert all(d["kind"] == "TypeMismatch" and Path(d["path"]).name == entry
                       for d in diagnostics), diagnostics
            assert any(obligation in d["notes"] for d in diagnostics), diagnostics
        print(f"Mutation rejected by {obligation.removeprefix('in definition ')}: {name}.", flush=True)


def ring_render():
    rendered = subprocess.run(compiler_command(ROOTS) + ["--raw", str(HERE / "RingClient.rac")],
                              capture_output=True, text=True, timeout=120)
    rendered.check_returncode()
    cuda = rendered.stdout
    assert cuda.count("__syncthreads();") == 2
    assert "mbarrier.arrive.expect_tx" in cuda and '"r"(8192u)' in cuda
    assert "cp.async.bulk.tensor.2d" in cuda
    assert "fence.proxy.async.shared::cta" in cuda
    assert cuda.count("mbarrier.inval") == 2
    assert "dim3(64u)" in cuda and "args, 9216u" in cuda
    (HERE / "ring-generated.cu").write_text(cuda)
    compiler = shutil.which("clang++")
    if compiler:
        rewritten = subprocess.run([sys.executable, str(ROOT / "gpu/stub/asm_calls.py")],
                                   input=cuda, capture_output=True, text=True, check=True)
        # This deliberately restricted client discards the scalar reads. Their
        # unused-variable warnings do not make the emitted C++ ill formed.
        subprocess.run([compiler, "-std=c++17", "-fsyntax-only", "-Wall", "-Werror",
                        "-Wno-parentheses-equality", "-Wno-unused-variable", "-I", str(ROOT / "gpu/stub"),
                        "-include", str(ROOT / "gpu/stub/cuda_stub.h"), "-x", "c++", "-"],
                       input=rewritten.stdout, text=True, check=True)
        print("Primitive-ring CUDA emitted; host C++ syntax check passed (PTX not compiled).", flush=True)
    else:
        print("Primitive-ring CUDA emitted; host C++ syntax check skipped (clang++ unavailable).", flush=True)


def ring_mutations():
    originals = {name: (HERE / name).read_text() for name in ("Mbarrier.rac", "RingPrimitives.rac", "Ring.rac")}
    trials = [
        ("empty phase never bootstrapped", "RingPrimitives.rac",
         "Primitive.empty(Mbarrier.Action.arrive(0)),", "Primitive.empty(Mbarrier.Action.arrive(1)),", "RingProofs.rac"),
        ("phase advances with transaction debt", "Mbarrier.rac",
         "Nat.beq(s.expected, s.completed)", "Nat.beq(s.expected, s.expected)", "RingProofs.rac"),
        ("completion bytes lost", "Mbarrier.rac",
         "Nat.add(s.completed, bytes)", "s.completed", "RingProofs.rac"),
        ("producer waits one phase ahead", "RingPrimitives.rac",
         "| Concurrent.Action.acquire => List.cons(Primitive.empty(Mbarrier.Action.wait(s.producer.round)), List.nil(Primitive))",
         "| Concurrent.Action.acquire => List.cons(Primitive.empty(Mbarrier.Action.wait(Nat.succ(s.producer.round))), List.nil(Primitive))", "RingProofs.rac"),
        ("final CTA join omitted", "RingPrimitives.rac",
         "List.cons(Primitive.join,\n        RingPrimitives.two(Primitive.full(Mbarrier.Action.invalidate), Primitive.empty(Mbarrier.Action.invalidate)))",
         "RingPrimitives.two(Primitive.full(Mbarrier.Action.invalidate), Primitive.empty(Mbarrier.Action.invalidate))", "RingProofs.rac"),
        ("full barrier moved outside its region", "Ring.rac",
         "def fullBar: Expr := Expr.sharedAddr(0)", "def fullBar: Expr := Expr.sharedAddr(16)", "RingBackendProofs.rac"),
        ("native expected bytes detached from map", "Ring.rac",
         "def bytes: Nat := 8192", "def bytes: Nat := 4096", "RingBackendProofs.rac"),
        ("native tensor map box changed", "Ring.rac",
         '"M", "N", 64, 64)', '"M", "N", 64, 32)', "RingBackendProofs.rac"),
        ("native consumer wait uses producer phase", "Ring.rac",
         "| Role.consumer => 1", "| Role.consumer => 0", "RingBackendProofs.rac"),
        ("native phase toggle lost", "Ring.rac",
         "Expr.bin(BinOp.bxor, Expr.var(Ring.parity(role)), Expr.lit(1))", "Expr.var(Ring.parity(role))", "RingBackendProofs.rac"),
        ("native release proxy fence lost", "Ring.rac",
         "| Concurrent.Action.release => Block.seq(Stmt.instr(Instr.fenceProxyAsync),\n        Block.seq(Stmt.instr(Instr.mbarArrive(Window.cta, Ring.emptyBar, Arrival.one)), Block.seq(Ring.flip(role), Block.done)))",
         "| Concurrent.Action.release => Block.seq(Stmt.instr(Instr.mbarArrive(Window.cta, Ring.emptyBar, Arrival.one)), Block.seq(Ring.flip(role), Block.done))", "RingBackendProofs.rac"),
        ("native close join moved after invalidation", "Ring.rac",
         "def close: Block := Block.seq(Stmt.sync, Block.seq(Ring.atThread(0,\n    Block.seq(Stmt.instr(Instr.mbarInval(Ring.fullBar)), Block.seq(Stmt.instr(Instr.mbarInval(Ring.emptyBar)), Block.done))), Block.done))",
         "def close: Block := Block.seq(Ring.atThread(0,\n    Block.seq(Stmt.instr(Instr.mbarInval(Ring.fullBar)), Block.seq(Stmt.instr(Instr.mbarInval(Ring.emptyBar)), Block.done))), Block.seq(Stmt.sync, Block.done))", "RingBackendProofs.rac"),
        ("root selects the wrong consumer thread", "Ring.rac",
         "Ring.atThread(32, consumer.block)", "Ring.atThread(33, consumer.block)", "RingBackendProofs.rac"),
        ("root omits barrier setup", "Ring.rac",
         "Ring.sequence(Ring.setup, Block.seq", "Ring.sequence(Block.done, Block.seq", "RingBackendProofs.rac"),
        ("root omits final close", "Ring.rac",
         "Ring.atThread(32, consumer.block), Ring.close", "Ring.atThread(32, consumer.block), Block.done", "RingBackendProofs.rac"),
        ("root initializes the wrong consumer phase", "Ring.rac",
         "Stmt.declMut(DType.u32, 1, Expr.lit(0))", "Stmt.declMut(DType.u32, 1, Expr.lit(1))", "RingBackendProofs.rac"),
        ("kernel shared extent detached from layout", "Ring.rac",
         'Ring.params, Ring.sharedBytes, Ring.body(p)', 'Ring.params, 8192, Ring.body(p)', "RingBackendProofs.rac"),
    ]
    for name, module, before, after, entry in trials:
        assert originals[module].count(before) == 1, (name, originals[module].count(before))
        with tempfile.TemporaryDirectory(prefix="raccoon-ring-mutation-") as tmp:
            overlay = Path(tmp)
            (overlay / module).write_text(originals[module].replace(before, after))
            result, diagnostics = check(HERE / entry, [overlay] + ROOTS)
            assert result.returncode == 1 and diagnostics, result.stdout + result.stderr
            assert all(d["kind"] == "TypeMismatch" and Path(d["path"]).name == entry for d in diagnostics), diagnostics
            assert any(any(note.startswith("in definition ") for note in d["notes"]) for d in diagnostics), diagnostics
        print(f"Ring mutation rejected by {entry}: {name}.", flush=True)


if __name__ == "__main__":
    check_experiment(HERE, ROOTS, smoke)
    representation_probe()
    mutations()
    ring_render()
    ring_mutations()
