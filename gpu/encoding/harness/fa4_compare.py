# Runs the generated attention kernels beside FlashAttention-4 (gpu/ATTENTION.md §2.7, §6 A1 and A2) on the same GPU
# and the same inputs: FA4's O is a second numerical cross-check, and its time the performance reference. Needs an
# sm_100a GPU, PyTorch, and Dao-AILab's flash-attention with its CuTe DSL path (`flash_attn.cute`):
#
#   gpu/gen.sh gpu/encoding/examples/attention.rac > attention.cu
#   nvcc -std=c++17 -O2 -shared -Xcompiler -fPIC -gencode arch=compute_100a,code=sm_100a -o libattention.so \
#     attention.cu -lcuda
#   python3 gpu/encoding/harness/fa4_compare.py ./libattention.so
#
# The example's two kernels are compared: `attention` (non-causal, O in f32) with FA4 at causal=False, and
# `attention_causal` (causal, O in bf16) with FA4 at causal=True. The non-causal comparison runs twice, each in a
# process of its own with its environment set before flash_attn is imported: with FA_DISABLE_2CTA=1, FA4's
# cta_group::1 kernel, the like-for-like comparison; and by default, which for head dimension 128 and seq > 256 is its
# 2-CTA kernel, the target of a later stage. The causal comparison runs once, in the first process: FA4's causal path
# is cta_group::1 whatever the flag. FA4 is called through `flash_attn.cute.interface.flash_attn_func` with bf16, head
# dimension 128, and (batch, heads) = (1, BH). The inputs are T1's (§1.3): Q in [-1, 1] with every fourth row of a
# head in [-8, 8], K and V in [-1, 1], at A1's sizes and A2's tails (`seq` not a multiple of 128, down to 1).
# A size passes when every element of O agrees with FA4's within twice T1's bound, 2 · 2^-7 · max|V| (V of the head),
# since both are approximate, plus the rounding of each bf16 O: 2^-8 · |O_FA4|, and for the causal kernel's bf16 O
# 2^-8 · |O_ours| too. Times are reported, not judged: TFLOP/s at 4 · BH · seq² · 128 FLOPs (half that, causal), with
# the host's load average, since both times include host work (our launcher's three tensor-map encodings, FA4's
# Python), which dominates at small sizes.
#
# Our kernels are called through their generated launchers, `attention_launch` and `attention_causal_launch`, with
# ctypes, on PyTorch's current stream.
import argparse
import ctypes
import math
import os
import subprocess
import sys

SEQS = (1, 127, 128, 129, 256, 1000, 1024, 4096)
HEADS = (1, 3, 16)
DIM = 128
REPS = 20
CONFIGS = {"no-2cta": {"FA_DISABLE_2CTA": "1"}, "default": {}}


def launcher(path, name):
    """The launcher `name` from the shared library at `path`, with the generated launchers' parameter list."""
    fn = getattr(ctypes.CDLL(path), name)
    p, u = ctypes.c_void_p, ctypes.c_uint
    # Q, K, V, O, LSE, BH, seq, scale_log2, rows, dim, stream
    fn.argtypes = [p, p, p, p, p, u, u, ctypes.c_float, u, u, p]
    fn.restype = ctypes.c_int
    return fn


def inputs(torch, bh, seq, seed):
    """T1's inputs as `[BH·seq, 128]` bf16 tensors on the GPU."""
    g = torch.Generator(device="cuda").manual_seed(seed)
    def uniform(lo, hi):
        return (torch.rand(bh * seq, DIM, generator=g, device="cuda") * (hi - lo) + lo).to(torch.bfloat16)
    q = uniform(-1, 1)
    peaked = (torch.arange(bh * seq, device="cuda") % seq) % 4 == 3
    q[peaked] = uniform(-8, 8)[peaked]
    return q, uniform(-1, 1), uniform(-1, 1)


def ours(torch, launch, causal, bh, seq, q, k, v):
    """Our O, `[BH·seq, 128]` (f32, or bf16 for the causal kernel) as f32, and a function that launches the kernel
    again."""
    o = torch.empty(bh * seq, DIM, dtype=torch.bfloat16 if causal else torch.float32, device="cuda")
    lse = torch.empty(bh * seq, dtype=torch.float32, device="cuda")
    scale_log2 = math.log2(math.e) / math.sqrt(DIM)
    def run():
        status = launch(q.data_ptr(), k.data_ptr(), v.data_ptr(), o.data_ptr(), lse.data_ptr(), bh, seq, scale_log2,
                        bh * seq, DIM, torch.cuda.current_stream().cuda_stream)
        if status != 0:
            sys.exit(f"launch failed: cudaError {status}")
    run()
    return o, run


def fa4(torch, causal, bh, seq, q, k, v):
    """FA4's O, `[BH·seq, 128]` f32, and a function that runs it again. FA4 takes (batch, seq, heads, dim)."""
    from flash_attn.cute.interface import flash_attn_func
    def layout(x):
        return x.view(1, bh, seq, DIM).transpose(1, 2).contiguous()
    qf, kf, vf = layout(q), layout(k), layout(v)
    def run():
        out = flash_attn_func(qf, kf, vf, softmax_scale=1 / math.sqrt(DIM), causal=causal)
        return out[0] if isinstance(out, tuple) else out
    out = run()
    return out.transpose(1, 2).reshape(bh * seq, DIM).float(), run


def milliseconds(torch, run):
    """The time of one run, averaged over REPS after a warm-up."""
    run()
    torch.cuda.synchronize()
    start, stop = torch.cuda.Event(enable_timing=True), torch.cuda.Event(enable_timing=True)
    start.record()
    for _ in range(REPS):
        run()
    stop.record()
    stop.synchronize()
    return start.elapsed_time(stop) / REPS


def compare(config, lib, causal):
    """Runs every size of one kernel against FA4 in this process's configuration; returns the number of sizes that
    disagree."""
    import torch
    name = "attention_causal_launch" if causal else "attention_launch"
    launch = launcher(lib, name)
    failures = 0
    for seq in SEQS:
        for bh in HEADS:
            q, k, v = inputs(torch, bh, seq, seq * 7919 + bh * 104729)
            o, run_ours = ours(torch, launch, causal, bh, seq, q, k, v)
            o_fa4, run_fa4 = fa4(torch, causal, bh, seq, q, k, v)
            torch.cuda.synchronize()
            o = o.float()
            bound = (2 * 2.0 ** -7 * v.float().abs().view(bh, seq * DIM).amax(dim=1)).view(bh, 1) \
                + 2.0 ** -8 * o_fa4.abs().view(bh, seq * DIM)
            if causal:
                bound = bound + 2.0 ** -8 * o.abs().view(bh, seq * DIM)
            ratio = ((o - o_fa4).abs().view(bh, seq * DIM) / bound).nan_to_num(nan=math.inf)
            bad = int((~(ratio <= 1)).any(dim=1).sum())
            failures += bad != 0
            worst = float(ratio.max())
            flops = (2.0 if causal else 4.0) * bh * seq * seq * DIM
            t_ours, t_fa4 = milliseconds(torch, run_ours), milliseconds(torch, run_fa4)
            print(f"{'FAIL' if bad else 'ok  '} {name} {config} BH={bh} seq={seq}: largest |O - O_FA4| {worst:.3g} of"
                  f" its bound{f' ({bad} heads outside)' if bad else ''}; ours {t_ours:.3f} ms,"
                  f" {flops / t_ours / 1e9:.1f} TFLOP/s; FA4 {t_fa4:.3f} ms, {flops / t_fa4 / 1e9:.1f} TFLOP/s;"
                  f" host load average {os.getloadavg()[0]:.2f}")
    return failures


def main():
    parser = argparse.ArgumentParser(description="Compare the attention kernels with FA4.")
    parser.add_argument("lib", help="the generated launcher, built as a shared library")
    parser.add_argument("--config", choices=sorted(CONFIGS), help="run one FA4 configuration in this process")
    args = parser.parse_args()
    if args.config:
        failures = compare(args.config, args.lib, False)
        if args.config == "no-2cta":
            failures += compare(args.config, args.lib, True)
        sys.exit(1 if failures else 0)
    status = 0
    for config, env in CONFIGS.items():
        inherited = {name: value for name, value in os.environ.items() if name != "FA_DISABLE_2CTA"}
        child = subprocess.run([sys.executable, os.path.abspath(__file__), args.lib, "--config", config],
                               env={**inherited, **env})
        status |= child.returncode
    print("all sizes agree" if status == 0 else "some sizes disagree")
    sys.exit(status)


if __name__ == "__main__":
    main()
