#!/usr/bin/env python3
"""
opcode_coverage.py — classify a chunk of real EVM bytecode against evm-asm's
capability manifest (conformance/capabilities.json).

Disassembles bytecode into its opcode stream (correctly skipping PUSH
immediate data so data bytes are never miscounted as opcodes), then scores
each distinct opcode by its kernel-checked proof tier and runtime status.

Used by the conformance harness:
  - Act 3 of the demo (real contract bytecode -> coverage scorecard)
  - `run.sh --report` (coverage over a live block's bytecodes)

Usage:
  opcode_coverage.py <capabilities.json> <hex-bytecode>   # 0x.. or bare hex
  opcode_coverage.py <capabilities.json> --json <hex>     # machine-readable
"""
import json
import sys


def build_byte_tables(caps):
    """byte(int) -> (name, tier, runtime), expanding range rows (PUSH2..32 etc.)."""
    by_byte = {}
    for name, e in caps["opcodes"].items():
        b = e["byte"]
        tier, rt = e["tier"], e.get("runtime")
        if "-" in b:
            lo, hi = (int(x, 16) for x in b.split("-"))
            for v in range(lo, hi + 1):
                by_byte[v] = (name, tier, rt)
        else:
            by_byte[int(b, 16)] = (name, tier, rt)
    return by_byte


def disassemble(code):
    """Yield (pc, opcode_byte) skipping PUSH1..32 immediate data bytes."""
    i, n = 0, len(code)
    while i < n:
        op = code[i]
        yield i, op
        if 0x60 <= op <= 0x7F:        # PUSH1..PUSH32
            i += 1 + (op - 0x5F)
        else:
            i += 1


def classify(caps_path, hexstr):
    caps = json.load(open(caps_path))
    by_byte = build_byte_tables(caps)
    h = hexstr.strip()
    if h.startswith(("0x", "0X")):
        h = h[2:]
    code = bytes.fromhex(h)

    hist = {}            # byte -> count
    for _, op in disassemble(code):
        hist[op] = hist.get(op, 0) + 1

    total_ops = sum(hist.values())
    tiers = {"proven": 0, "conditional": 0, "partial": 0, "execSpec": 0,
             "notStarted": 0, "unknown": 0}
    runtime = {"exec": 0, "noop": 0, "zero": 0, "absent": 0, "unknown": 0}
    unsupported = {}     # name/byte -> count (runtime != exec)
    for op, cnt in hist.items():
        entry = by_byte.get(op)
        if entry is None:
            tiers["unknown"] += cnt
            runtime["unknown"] += cnt
            unsupported["0x%02x" % op] = unsupported.get("0x%02x" % op, 0) + cnt
            continue
        name, tier, rt = entry
        tiers[tier] = tiers.get(tier, 0) + cnt
        runtime[rt] = runtime.get(rt, 0) + cnt
        if rt != "exec":
            unsupported[name] = unsupported.get(name, 0) + cnt

    proven = tiers["proven"] + tiers["conditional"]     # has a kernel-checked Hoare triple
    runnable = runtime["exec"]                           # spec-faithful in guest
    return {
        "code_bytes": len(code),
        "total_ops": total_ops,
        "distinct_ops": len(hist),
        "tiers": tiers,
        "runtime": runtime,
        "proven_pct": round(100 * proven / total_ops, 1) if total_ops else 0.0,
        "runnable_pct": round(100 * runnable / total_ops, 1) if total_ops else 0.0,
        "top_unsupported": sorted(unsupported.items(), key=lambda kv: -kv[1])[:6],
    }


def main():
    args = sys.argv[1:]
    as_json = "--json" in args
    args = [a for a in args if a != "--json"]
    if len(args) != 2:
        print(__doc__)
        return 2
    caps_path, hexstr = args
    r = classify(caps_path, hexstr)
    if as_json:
        print(json.dumps(r))
        return 0
    print(f"  bytecode: {r['code_bytes']} bytes, {r['total_ops']} opcodes "
          f"({r['distinct_ops']} distinct)")
    print(f"  kernel-proven opcode spec (proven/conditional triple): {r['proven_pct']}%")
    print(f"  runnable in guest (codegen, unverified emitter):       {r['runnable_pct']}%")
    t = r["tiers"]
    print(f"  by proof tier: proven {t['proven']}  conditional {t['conditional']}  "
          f"partial {t['partial']}  execSpec {t['execSpec']}  "
          f"notStarted {t['notStarted']}  unknown {t['unknown']}")
    if r["top_unsupported"]:
        gaps = ", ".join(f"{n}×{c}" for n, c in r["top_unsupported"])
        print(f"  frontier (not yet spec-faithful in guest): {gaps}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
