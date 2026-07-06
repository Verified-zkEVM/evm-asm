#!/usr/bin/env python3
"""Sample real mainnet (dividend, divisor) operands from the Phase-2 trace into
a plain decimal file the Lean harness (bench/DivBench.lean) can read and run the
verified `step` semantics over.

This replaces DivBench's representative-per-class weighting (which is only a
point estimate — step count varies WITHIN a divisor word-count with the
normalization shift and dividend, so a single representative is biased) with a
direct frequency-weighted MEAN over actual operands.

The raw stream `bench/div-operands-mainnet.jsonl.gz` is already
frequency-representative (every executed division appears once), so a fixed
stride over it preserves the distribution while bounding the Lean run cost.

Usage:
  python3 scripts/sample-div-operands.py            # default: 800 DIV, 400 MOD
  python3 scripts/sample-div-operands.py --div 1200 --mod 600

Output: bench/div-operands-sample.txt — one operand per line, "<a_dec> <b_dec>",
DIV operands first (header "# DIV <count>"), then MOD ("# MOD <count>").
op codes: 4=DIV, 5=SDIV, 6=MOD, 7=SMOD (only unsigned 4/6 sampled).
"""
import argparse, gzip, json, sys

RAW = "bench/div-operands-mainnet.jsonl.gz"
OUT = "bench/div-operands-sample.txt"


def collect(op):
    out = []
    with gzip.open(RAW, "rt") as f:
        for line in f:
            r = json.loads(line)
            if r["op"] == op:
                out.append((int(r["a"], 16), int(r["b"], 16)))
    return out


def stride_sample(xs, n):
    if n >= len(xs):
        return xs
    step = len(xs) / n
    return [xs[int(i * step)] for i in range(n)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--div", type=int, default=800)
    ap.add_argument("--mod", type=int, default=400)
    args = ap.parse_args()

    divs = collect(4)
    mods = collect(6)
    print(f"raw: {len(divs)} DIV, {len(mods)} MOD", file=sys.stderr)

    ds = stride_sample(divs, args.div)
    ms = stride_sample(mods, args.mod)

    with open(OUT, "w") as f:
        f.write(f"# DIV {len(ds)}\n")
        for a, b in ds:
            f.write(f"{a} {b}\n")
        f.write(f"# MOD {len(ms)}\n")
        for a, b in ms:
            f.write(f"{a} {b}\n")
    print(f"wrote {OUT}: {len(ds)} DIV + {len(ms)} MOD (frequency-weighted stride sample)",
          file=sys.stderr)


if __name__ == "__main__":
    main()
