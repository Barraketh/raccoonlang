#!/usr/bin/env python3
"""Validate the independent TinyGEMM library and compare the real Core client."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE.parent))
from check_experiment import check_experiment, compiler_command


def baseline():
    source = (ROOT / "gpu/encoding/examples/tinygemm.rac").read_text()
    source = source.split("\n{ Core.render(Tiny.kernel) }")[0]
    source = source.replace("namespace Tiny {", "namespace CoreTiny {").replace("Tiny.", "CoreTiny.")
    expected = source + "\n"
    assert (HERE / "Baseline.rac").read_text() == expected, "Baseline must be the current real TinyGEMM client."


def smoke(cuda):
    assert "__launch_bounds__(256, 1)" in cuda
    assert "164928" in cuda
    assert "tcgen05.mma.cta_group::1" in cuda
    assert "cp.async.bulk.wait_group.read 1" in cuda
    assert "cp.async.bulk.wait_group 0" in cuda
    assert "CU_TENSOR_MAP_SWIZZLE_128B" in cuda


def comparisons():
    with tempfile.TemporaryDirectory(prefix="raccoon-tiny-comparison-") as directory:
        folder = Path(directory)
        command = compiler_command([folder, HERE, ROOT / "gpu"])
        source = (HERE / "Baseline.rac").read_text()
        for stages, buffers in [(1, 1), (2, 2), (6, 2)]:
            variant = source.replace("RingCfg.mk(4, boxA, boxB)", f"RingCfg.mk({stages}, boxA, boxB)")
            variant = variant.replace("withStaging(e, 2,", f"withStaging(e, {buffers},")
            (folder / "BaselineVariant.rac").write_text(variant)
            proof = ('import Tiny\nimport TinyClient\nimport BaselineVariant\nnamespace Compare {\n'
                     f'  def same: Eq(Cuda.Kernel, Commands.syntax(MachineTiny.build("tinygemm", {stages}, {buffers})), '
                     'Core.kernelSyntax(CoreTiny.kernel)) := Eq.refl(Core.kernelSyntax(CoreTiny.kernel))\n'
                     f'  def clientSame: Eq(Cuda.Kernel, Gpu.syntax(LunaTiny.build("tinygemm", {stages}, {buffers})), '
                     'Core.kernelSyntax(CoreTiny.kernel)) := Eq.refl(Core.kernelSyntax(CoreTiny.kernel))\n}\n')
            path = folder / "Comparison.rac"
            path.write_text(proof)
            result = subprocess.run(command + ["--json", str(path)], capture_output=True, text=True, timeout=120)
            diagnostics = json.loads(result.stdout)
            assert result.returncode == 0 and diagnostics == [], diagnostics
            print(f"Both clients: entire kernel equality checked, {stages} stages, {buffers} staging buffers.", flush=True)

        # Type-level protocol legality alone does not prove the native template
        # is correct. The concrete target fact must detect this change.
        native = (HERE / "Native.rac").read_text()
        native = native.replace('| Op.fenceStage => Emission.mk(Block.seq(Stmt.instr(Instr.fenceProxyAsync), Block.seq(Stmt.syncWarp, Block.done)), start)',
                                '| Op.fenceStage => Emission.mk(Block.seq(Stmt.syncWarp, Block.done), start)')
        assert native != (HERE / "Native.rac").read_text()
        (folder / "Native.rac").write_text(native)
        result = subprocess.run(command + ["--json", str(HERE / "Templates.rac")], capture_output=True, text=True, timeout=120)
        diagnostics = json.loads(result.stdout)
        assert result.returncode == 1 and {d["kind"] for d in diagnostics} == {"TypeMismatch"}, diagnostics
        assert all("in definition Templates.fenceReallyEmitsFence" in d["notes"] for d in diagnostics), diagnostics
        print("Deleting the native proxy fence invalidates its target proof.", flush=True)

        # Tiny's usual instruction order alone would hide a backend that ignored
        # the explicit data argument and guessed it from the fresh-name counter.
        native = (HERE / "Native.rac").read_text()
        guessed = native.replace("Nat.add(values, Nat.mul(4, g))", "Nat.add(Nat.sub(start, 32), Nat.mul(4, g))")
        assert guessed != native
        (folder / "Native.rac").write_text(guessed)
        result = subprocess.run(command + ["--json", str(HERE / "ValueTests.rac")], capture_output=True, text=True, timeout=120)
        diagnostics = json.loads(result.stdout)
        assert result.returncode == 1 and {d["kind"] for d in diagnostics} == {"TypeMismatch"}, diagnostics
        assert all("in definition ValueTests.writesSuppliedValues" in d["notes"] for d in diagnostics), diagnostics
        print("Ignoring the supplied register view invalidates its target proof.", flush=True)


def client_output():
    command = compiler_command([HERE, ROOT / "gpu"])
    result = subprocess.run(command + ["--raw", str(HERE / "ClientRender.rac")], capture_output=True, text=True, timeout=120)
    result.check_returncode()
    assert result.stdout == (HERE / "generated.cu").read_text(), "Luna's client changed the rendered kernel or launcher."
    (HERE / "client-generated.cu").write_text(result.stdout)
    print("Luna's CUDA and launcher are byte-identical to the checked original client.", flush=True)


if __name__ == "__main__":
    baseline()
    check_experiment(HERE, [HERE, ROOT / "gpu"], smoke)
    comparisons()
    client_output()
