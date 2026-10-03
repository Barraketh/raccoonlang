#!/usr/bin/env python3
"""Check actual A3b/pair clients, complete AST equality, invalid clients and target facts."""
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / 'experiments'))
from check_experiment import compiler_command


def check(command, path, expectation='accept', definition=None):
    result = subprocess.run(command + ['--json', str(path)], capture_output=True, text=True, timeout=180)
    try:
        diagnostics = json.loads(result.stdout)
    except ValueError:
        raise AssertionError((path, result.stdout, result.stderr))
    summary = [{**d, 'message': d['message'][:800]} for d in diagnostics]
    if expectation == 'accept':
        assert result.returncode == 0 and diagnostics == [], (path, summary, result.stderr)
    else:
        assert result.returncode == 1 and diagnostics, (path, summary, result.stderr)
        assert {d['kind'] for d in diagnostics} == {expectation}, (path, summary)
        assert all(Path(d['path']).resolve() == path.resolve() for d in diagnostics), (path, summary)
        assert all(f'in definition {definition}' in d['notes'] for d in diagnostics), (path, summary)
    return path


def fixtures():
    a = (ROOT / 'gpu/encoding/examples/attention_a3b.rac').read_text()
    a = a.split('// The non-causal kernel with f32 output, then the causal one with bf16 output.')[0]
    a = a.replace('namespace Corrected {', 'namespace CoreCorrected {')
    assert (HERE / 'BaselineAttention.rac').read_text() == a
    p = (ROOT / 'gpu/encoding/examples/gemm_pair.rac').read_text()
    p = p.split('\n{ Core.render(GemmPair.kernel) }')[0].replace('namespace GemmPair {', 'namespace CoreGemmPair {') + '\n'
    assert (HERE / 'BaselinePair.rac').read_text() == p
    for name in ['AttentionClient.rac', 'PairClient.rac']:
        client = (HERE / name).read_text()
        assert 'import encoding.Core' not in client and 'import encoding.Attention' not in client
        assert 'Ctx(' not in client and 'Fixed(' not in client, name
        assert 'Core.render' not in client  # rendering is verified at the assembly boundary
        assert 'GpuMachine.Key' not in client and 'GpuMachine.Machine.mk' not in client


def comparisons():
    with tempfile.TemporaryDirectory(prefix='raccoon-full-comparison-') as directory:
        folder = Path(directory)
        command = compiler_command([folder, HERE, ROOT / 'gpu'])
        for causal, dtype in [('false', 'f32'), ('true', 'bf16'), ('true', 'f32'), ('false', 'bf16')]:
            name = f'attention_{causal}_{dtype}'
            path = folder / 'CompareAttention.rac'
            path.write_text('import AttentionClient\nimport BaselineAttention\nnamespace Comparison {\n'
                f' def same: Eq(Cuda.Kernel, Core.kernelSyntax(LunaAttention.build("{name}", Bool.{causal}, Cuda.DType.{dtype})), '
                f'Core.kernelSyntax(CoreCorrected.kernel("{name}", Bool.{causal}, Cuda.DType.{dtype}))) := '
                f'Eq.refl(Core.kernelSyntax(CoreCorrected.kernel("{name}", Bool.{causal}, Cuda.DType.{dtype})))\n}}\n')
            check(command, path)
            print(f'A3b full kernel and launcher equality: causal={causal}, output={dtype}.', flush=True)
        source = (HERE / 'BaselinePair.rac').read_text()
        for stages, buffers, band in [(6, 2, 8), (1, 1, 1), (2, 2, 2), (6, 2, 4)]:
            name = f'pair_{stages}_{buffers}_{band}'
            variant = source.replace('RingCfg.mk(6, boxA, boxB)', f'RingCfg.mk({stages}, boxA, boxB)')
            variant = variant.replace('withStaging(e, 2,', f'withStaging(e, {buffers},')
            variant = variant.replace('t, acc, 2, 256,', f't, acc, {buffers}, 256,')
            variant = variant.replace('def band : Nat := 8', f'def band : Nat := {band}')
            variant = variant.replace('pairGemmPersistentKernel("gemm_pair",', f'pairGemmPersistentKernel("{name}",')
            (folder / 'BaselineVariant.rac').write_text(variant)
            path = folder / 'ComparePair.rac'
            path.write_text('import PairClient\nimport BaselineVariant\nnamespace Comparison {\n'
                f' def same: Eq(Cuda.Kernel, Core.kernelSyntax(LunaPair.build("{name}", {stages}, {buffers}, {band})), '
                'Core.kernelSyntax(CoreGemmPair.kernel)) := Eq.refl(Core.kernelSyntax(CoreGemmPair.kernel))\n}\n')
            check(command, path)
            print(f'Pair GEMM full kernel and launcher equality: {stages} stages, {buffers} buffers, band {band}.', flush=True)


def render():
    command = compiler_command([HERE, ROOT / 'gpu'])
    for name, original in [('AttentionRender', 'attention_a3b'), ('PairRender', 'gemm_pair')]:
        output = subprocess.run(command + ['--raw', str(HERE / f'{name}.rac')], capture_output=True, text=True, timeout=180)
        output.check_returncode()
        baseline = subprocess.run(command + ['--raw', str(ROOT / f'gpu/encoding/examples/{original}.rac')], capture_output=True, text=True, timeout=180)
        baseline.check_returncode()
        assert output.stdout == baseline.stdout, f'{name}: rendered kernel/launcher changed'
        (HERE / f'{original}.cu').write_text(output.stdout)
        print(f'{original}: CUDA and launcher are byte-identical to Core.', flush=True)


def target_mutations():
    source = (ROOT / 'gpu/encoding/Lowering.rac').read_text()
    changes = [
        ('publishWaitsBeforeArrival',
         'List.cons(Stmt.syncWarp, List.cons(Core.tmemWaitStore, List.cons(Core.tcFenceBefore, List.cons(Core.mbarArrive(Core.probsFull(buf)), List.nil(Stmt)))))',
         'List.cons(Stmt.syncWarp, List.cons(Core.tcFenceBefore, List.cons(Core.mbarArrive(Core.probsFull(buf)), List.nil(Stmt))))'),
        ('pairCommitReachesBoth', '| CtaGroup.two => Option.some(3)', '| CtaGroup.two => Option.some(1)'),
    ]
    with tempfile.TemporaryDirectory(prefix='raccoon-full-target-mutation-') as directory:
        folder = Path(directory)
        (folder / 'encoding').mkdir()
        command = compiler_command([folder, HERE, ROOT / 'gpu'])
        for definition, old, new in changes:
            assert source.count(old) == 1, old
            (folder / 'encoding/Lowering.rac').write_text(source.replace(old, new))
            check(command, HERE / 'TargetFacts.rac', 'TypeMismatch', f'TargetFacts.{definition}')
            print(f'Changing shared lowering invalidates {definition}.', flush=True)


def static_checks():
    command = compiler_command([HERE, ROOT / 'gpu'])
    jobs = [(p, 'accept', None) for p in sorted(HERE.glob('*.rac'))]
    for p in sorted((HERE / 'checks').glob('*.rac')):
        expected = p.read_text().splitlines()[0].removeprefix('// expect: ')
        jobs.append((p, expected, 'Rejected.bad'))
    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(lambda job: check(command, *job), jobs))
    rejects = sum(expected != 'accept' for _, expected, _ in jobs)
    print(f'{len(jobs)} files checked: {len(jobs)-rejects} accepted, {rejects} rejected for their stated rule.', flush=True)


if __name__ == '__main__':
    fixtures()
    static_checks()
    comparisons()
    render()
    target_mutations()
