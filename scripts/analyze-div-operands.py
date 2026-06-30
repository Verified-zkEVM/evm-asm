#!/usr/bin/env python3
"""Bucket DIV/MOD/SDIV/SMOD operand traces by what the division algorithm cares about.

Reads the newline-delimited JSON produced by collect-div-operands.py (or by the
spec-EVM instrumentation, instrument-spec-div.py) and emits a distribution
report plus a machine-readable weights JSON consumable by bench/DivBench.

Bucketing dimensions (the algorithm's dispatch knobs):
  * divisor word-count n in {0 (b==0), 1 (<2^64), 2 (<2^128), 3 (<2^192), 4}
  * dividend word-count (same scheme)
  * fraction with a < b           -> quotient 0, cheap early-out
  * fraction with divisor a power of two -> a shift
  * notable constant divisors (1, 2, 10^k, 2^96, 2^128, ...) frequency

DIV(0x04)/MOD(0x06) are unsigned; SDIV(0x05)/SMOD(0x07) operands are 256-bit
two's-complement, so we bucket those on the *magnitude* (what the verified
unsigned core actually divides) and report them separately.

Usage:
    python3 scripts/analyze-div-operands.py FILE.jsonl [FILE2.jsonl ...] \
        [--label mainnet] [--weights bench/div-weights.json]
"""
import argparse
import collections
import json
import sys

DIV, SDIV, MOD, SMOD = 4, 5, 6, 7
MASK256 = (1 << 256) - 1


def wordcount(v):
    if v == 0:
        return 0
    return (v.bit_length() + 63) // 64


def is_pow2(v):
    return v != 0 and (v & (v - 1)) == 0


def to_magnitude(v, signed):
    """Interpret a 256-bit word; return unsigned magnitude actually divided."""
    if signed and v >= (1 << 255):
        v -= (1 << 256)
    return abs(v)


# notable divisor constants worth calling out explicitly
POW10 = {10 ** k: f"10^{k}" for k in range(0, 28)}
NAMED = {1: "1", 2: "2", 3: "3", 5: "5", 7: "7", 10000: "10000(bps)",
         2 ** 96: "2^96(Q96)", 2 ** 128: "2^128(Q128)", 2 ** 64: "2^64",
         2 ** 192: "2^192", (1 << 256) - 1: "2^256-1"}
NAMED.update(POW10)


def classify(records, op_filter, signed):
    n_div = collections.Counter()        # divisor word-count
    n_dvd = collections.Counter()        # dividend word-count
    joint = collections.Counter()        # (dividend_n, divisor_n)
    named = collections.Counter()        # notable constant divisors
    pow2_by_n = collections.Counter()    # pow2 divisors, keyed by divisor word-count
    altb_by_n = collections.Counter()    # a<b cases, keyed by divisor word-count
    genuine_by_n = collections.Counter() # NOT cheap (real schoolbook work), by word-count
    part = collections.Counter()         # non-overlapping precedence partition
    pow2_byte_aligned = 0                # pow2 divisor == 2^(8k): byte-extraction idiom
    total = a_lt_b = pow2 = b_zero = cheap = 0
    for r in records:
        if r["op"] not in op_filter:
            continue
        a = to_magnitude(int(r["a"], 16) & MASK256, signed)
        b = to_magnitude(int(r["b"], 16) & MASK256, signed)
        total += 1
        nb, na = wordcount(b), wordcount(a)
        n_div[nb] += 1
        n_dvd[na] += 1
        joint[(na, nb)] += 1
        if b == 0:
            b_zero += 1
            cheap += 1
            part["b0"] += 1
        else:
            is_p2 = is_pow2(b)
            is_lt = a < b
            if is_lt:
                a_lt_b += 1
                altb_by_n[nb] += 1
            if is_p2:
                pow2 += 1
                pow2_by_n[nb] += 1
                if (b.bit_length() - 1) % 8 == 0:   # divisor == 2^(8k)
                    pow2_byte_aligned += 1
            if is_lt or is_p2:
                cheap += 1
            else:
                genuine_by_n[nb] += 1
            # non-overlapping precedence partition: a<b > pow2 > genuine-by-n
            if is_lt:
                part["a_lt_b"] += 1
            elif is_p2:
                part["pow2_not_altb"] += 1
            else:
                part[f"genuine_n{nb}"] += 1
            if b in NAMED:
                named[NAMED[b]] += 1
    return {
        "total": total, "n_div": n_div, "n_dvd": n_dvd, "joint": joint,
        "named": named, "a_lt_b": a_lt_b, "pow2": pow2, "b_zero": b_zero,
        "cheap": cheap, "pow2_by_n": pow2_by_n, "altb_by_n": altb_by_n,
        "genuine_by_n": genuine_by_n, "part": part,
        "pow2_byte_aligned": pow2_byte_aligned,
    }


def pct(x, total):
    return f"{100.0 * x / total:5.1f}%" if total else "  n/a"


def report(label, st, kind):
    t = st["total"]
    print(f"\n### {label}: {kind}  (n={t})")
    if t == 0:
        print("  (no samples)")
        return
    print("  divisor word-count n  (with pow2 / a<b share *within* that n):")
    for n in range(0, 5):
        c = st["n_div"].get(n, 0)
        p2 = st["pow2_by_n"].get(n, 0)
        lt = st["altb_by_n"].get(n, 0)
        inner = f"pow2 {pct(p2, c)} a<b {pct(lt, c)}" if c else ""
        print(f"    n={n}: {c:8d}  {pct(c, t)}   {inner}")
    print("  dividend word-count:")
    for n in range(0, 5):
        c = st["n_dvd"].get(n, 0)
        print(f"    m={n}: {c:8d}  {pct(c, t)}")
    print(f"  a < b (quotient 0):   {st['a_lt_b']:8d}  {pct(st['a_lt_b'], t)}")
    print(f"  divisor power-of-two: {st['pow2']:8d}  {pct(st['pow2'], t)}"
          f"   (of which 2^(8k) byte-extraction: {st['pow2_byte_aligned']}"
          f" {pct(st['pow2_byte_aligned'], st['pow2']) if st['pow2'] else ''})")
    print(f"  divisor == 0:         {st['b_zero']:8d}  {pct(st['b_zero'], t)}")
    print(f"  CHEAP (a<b | pow2 | b=0): {st['cheap']:8d}  {pct(st['cheap'], t)}")
    print("  NON-OVERLAPPING partition (a<b > pow2 > genuine-by-n; sums to 100%):")
    for k in ("b0", "a_lt_b", "pow2_not_altb",
              "genuine_n1", "genuine_n2", "genuine_n3", "genuine_n4"):
        c = st["part"].get(k, 0)
        print(f"    {k:16s}: {c:8d}  {pct(c, t)}")
    print("  top notable constant divisors:")
    for name, c in st["named"].most_common(12):
        print(f"    {name:14s}: {c:8d}  {pct(c, t)}")
    print("  joint (dividend_n, divisor_n) top cells:")
    for (na, nb), c in sorted(st["joint"].items(), key=lambda kv: -kv[1])[:10]:
        print(f"    a_n={na} b_n={nb}: {c:8d}  {pct(c, t)}")


def weights_block(st):
    t = st["total"]
    if t == 0:
        return None
    return {
        "total": t,
        "n0": st["n_div"].get(0, 0) / t,
        "n1": st["n_div"].get(1, 0) / t,
        "n2": st["n_div"].get(2, 0) / t,
        "n3": st["n_div"].get(3, 0) / t,
        "n4": st["n_div"].get(4, 0) / t,
        "a_lt_b_frac": st["a_lt_b"] / t,
        "pow2_frac": st["pow2"] / t,
        "b_zero_frac": st["b_zero"] / t,
        "cheap_frac": st["cheap"] / t,
        "pow2_byte_aligned_frac": st["pow2_byte_aligned"] / t,  # divisor==2^(8k): byte-extraction
        # NON-OVERLAPPING partition of ALL divides (sums to 1.0): precedence
        # a<b > pow2 > genuine-by-n. THIS is what Phase 3 should weight against;
        # do NOT add a_lt_b_frac+pow2_frac (they overlap ~15pp).
        "partition": {k: st["part"].get(k, 0) / t for k in
                      ("b0", "a_lt_b", "pow2_not_altb",
                       "genuine_n1", "genuine_n2", "genuine_n3", "genuine_n4")},
        # genuine (non-cheap) schoolbook work as a fraction of ALL divides, by
        # divisor word-count -- the dispatch the Phase 3 algorithm must optimize.
        "genuine_by_n": {str(n): st["genuine_by_n"].get(n, 0) / t for n in range(5)},
        "dividend_n": {str(k): v / t for k, v in sorted(st["n_dvd"].items())},
        "pow2_by_n": {str(n): st["pow2_by_n"].get(n, 0) / st["n_div"][n]
                      for n in st["n_div"] if st["n_div"][n]},
        "altb_by_n": {str(n): st["altb_by_n"].get(n, 0) / st["n_div"][n]
                      for n in st["n_div"] if st["n_div"][n]},
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--label", default="data")
    ap.add_argument("--weights", help="write machine-readable weights JSON here")
    args = ap.parse_args()

    records = []
    for fn in args.files:
        with open(fn) as f:
            for line in f:
                line = line.strip()
                if line:
                    records.append(json.loads(line))
    print(f"loaded {len(records)} records from {len(args.files)} file(s)", file=sys.stderr)

    op_counts = collections.Counter(r["op"] for r in records)
    print(f"op mix: DIV={op_counts[DIV]} MOD={op_counts[MOD]} "
          f"SDIV={op_counts[SDIV]} SMOD={op_counts[SMOD]}")

    st_div = classify(records, {DIV}, signed=False)
    st_mod = classify(records, {MOD}, signed=False)
    st_divmod = classify(records, {DIV, MOD}, signed=False)
    st_sdiv = classify(records, {SDIV, SMOD}, signed=True)

    report(args.label, st_div, "DIV (unsigned)")
    report(args.label, st_mod, "MOD (unsigned)")
    report(args.label, st_divmod, "DIV+MOD combined (unsigned core)")
    report(args.label, st_sdiv, "SDIV+SMOD (signed, on magnitude)")

    if args.weights:
        out = {
            "label": args.label,
            "div": weights_block(st_div),
            "mod": weights_block(st_mod),
            "divmod": weights_block(st_divmod),
            "sdiv_smod": weights_block(st_sdiv),
            "op_mix": {"DIV": op_counts[DIV], "MOD": op_counts[MOD],
                       "SDIV": op_counts[SDIV], "SMOD": op_counts[SMOD]},
        }
        with open(args.weights, "w") as f:
            json.dump(out, f, indent=2)
        print(f"\nwrote weights -> {args.weights}", file=sys.stderr)


if __name__ == "__main__":
    main()
