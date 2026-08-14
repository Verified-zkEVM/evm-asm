#!/usr/bin/env python3
"""callee-composition-queue.py — startable worklist for the in-image proof lanes (#12318).

WHAT IT ANSWERS
---------------
Per routine actually linked into the guest image:

  * control-flow shape (loop-free? indirect? how many instructions?)
  * its callees, resolved to guest symbols
  * whether every callee already has a registry row  -> STARTABLE by composition
  * which unrowed callee blocks the most routines    -> demand-queue input (#12035)

⛔ WHY THIS DOES NOT USE scripts/shape-census.py
------------------------------------------------
That census parses the emitted `*Function : String` defs as assembly text, and it
is **structurally blind to every converted routine**, which is precisely the
population that can carry a row. A routine's `Function` string contains literal
asm only while it is UNCONVERTED:

    -- unconverted: asm text, census can read it
    def precompileSharedSelectPriceFunction : String :=
      "precompile_shared_select_price:\\n" ++
      "  la t0, precompile_shared_selector\\n  sd zero, 0(t0)\\n" ++ ...

    -- converted: no asm at all, just a label and a Program reference
    def secfEq32Function : String :=
      "secf_eq32:\\n" ++ emitProgram secfEq32_prog

Conversion is what earns a routine a Lean `Program`, hence a `guestImageEntries`
pairing, hence linkage. Measured on this tree: of 984 emitted `*Function` defs,
**565 parse to ZERO instructions**, and of the 449 linked symbols exactly **one**
has readable asm text.

⚠️ And a zero-instruction body is indistinguishable from a branch-free one — no
instructions means no branches — so the census files it as a "flat block". That is
why its flat-block figure reads 588: ~96% of that class is empty parses, not flat
routines. **Any shape claim about in-image routines taken from that tool is
unfounded**, including population figures derived from it. Two such figures were
in circulation and both were wrong; see the header of
`EvmAsm/Tests/GuestImageShapeDump.lean`.

So shape comes from the Lean `Program`s themselves, via that dump.

REGENERATING THE INPUT
    lake env lean scripts/lean/GuestImageShapeDumpRun.lean > /tmp/shape.tsv
    python3 scripts/callee-composition-queue.py --tsv /tmp/shape.tsv

This is a TOOL (it computes an ordering for humans), not a gate: there is nothing
here that can be "violated", so it takes no `--strict` and needs no CI step.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GUESTADDRS = os.path.join(ROOT, "EvmAsm/Codegen/GuestAddrs.lean")
ROUTINES = os.path.join(ROOT, "EvmAsm/Progress/Routines.lean")


def addr_to_symbol() -> dict[int, str]:
    src = open(GUESTADDRS, encoding="utf-8").read()
    out = {}
    for m in re.finditer(r"def\s+([a-z][a-z0-9_]*)\s*:\s*Nat\s*:=\s*(0x[0-9a-fA-F]+)", src):
        out[int(m.group(2), 16)] = m.group(1)
    return out


def rowed_symbols() -> set[str]:
    """Symbols with a registry row, ANY tier: a `.conditional` row is still a
    callee contract you can compose against, so the question is "is there a row",
    not "is it .proven"."""
    src = open(ROUTINES, encoding="utf-8").read()
    return {s.strip() for s in re.findall(r'routine\s+"([a-z][a-z0-9_]*)"', src)}


def load(tsv_path: str):
    a2s = addr_to_symbol()
    rows = []
    with open(tsv_path, encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line:
                continue
            p = line.split("\t")
            addr = int(p[0])
            calls = [int(x) for x in p[4].split(",")] if len(p) > 4 and p[4] else []
            rows.append({
                "addr": addr,
                "symbol": a2s.get(addr, f"?{addr:x}"),
                "ninstr": int(p[1]),
                "backedges": int(p[2]),
                "indirect": p[3] == "1",
                "callees": [a2s.get(c, f"?{c:x}") for c in calls],
            })
    return rows


def classify(rows, rowed):
    for r in rows:
        r["loopfree"] = r["backedges"] == 0 and not r["indirect"]
        r["rowed"] = r["symbol"] in rowed
        uniq = []
        for c in r["callees"]:
            if c not in uniq:
                uniq.append(c)
        r["uniq_callees"] = uniq
        r["missing"] = [c for c in uniq if c not in rowed]
        # Startable = loop-free, unrowed, and nothing unrowed to compose against.
        # Call-free routines are startable trivially: no callee rows are needed.
        r["startable"] = r["loopfree"] and not r["rowed"] and not r["missing"]
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tsv", default="/tmp/shape.tsv",
                    help="shape dump from scripts/lean/GuestImageShapeDumpRun.lean")
    ap.add_argument("--markdown", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--limit", type=int, default=40)
    args = ap.parse_args()

    if not os.path.isfile(args.tsv):
        print(f"callee-composition-queue: no shape dump at {args.tsv}", file=sys.stderr)
        print("  regenerate with:", file=sys.stderr)
        print("    lake env lean scripts/lean/GuestImageShapeDumpRun.lean > "
              f"{args.tsv}", file=sys.stderr)
        return 2

    rowed = rowed_symbols()
    rows = classify(load(args.tsv), rowed)

    loopfree = [r for r in rows if r["loopfree"]]
    callfree = [r for r in loopfree if not r["uniq_callees"] and not r["rowed"]]
    withcalls = [r for r in loopfree if r["uniq_callees"] and not r["rowed"]]
    startable = [r for r in rows if r["startable"]]

    if args.self_test:
        ok = True

        def check(label, cond, detail=""):
            nonlocal ok
            print(f"  {'PASS' if cond else 'FAIL'}  {label}" + (f" — {detail}" if detail else ""))
            if not cond:
                ok = False

        # ⚠️ NON-VACUITY FIRST. An earlier version of this self-test passed all
        # five of its checks while measuring ZERO routines — every `all(...)` over
        # an empty list is true, so a broken input made the suite green. That is
        # the same vacuity failure the proof side of this repo guards against, and
        # it is why these three population floors come before any invariant.
        check("population is non-empty (guards against a vacuous pass)",
              len(rows) > 100, f"{len(rows)} image entries")
        check("some routine is loop-free", len(loopfree) > 0, f"{len(loopfree)}")
        check("some routine is startable", len(startable) > 0, f"{len(startable)}")

        # Controls with independently-known answers: these four were proved by
        # hand, so their shapes are known without this tool. Instruction counts
        # must equal the `#guard <sym>_prog.length` values in their source files.
        known = {
            "call_frame_set_calldata": (4, 0),   # 3-instruction body + ret, no loop
            "u256_from_u64_be":       (19, 0),   # 18 + ret, loop-free
            "secf_eq32":              (15, 1),   # 14 + ret, byte-scan loop
            "blsg_eq48":              (15, 1),   # same shape at 48 bytes
        }
        bysym = {r["symbol"]: r for r in rows}
        for sym, (n, back) in known.items():
            r = bysym.get(sym)
            check(f"control {sym}: {n} instrs, {back} back-edge(s)",
                  r is not None and r["ninstr"] == n and r["backedges"] == back,
                  "" if r is None else f"got {r['ninstr']} instrs, {r['backedges']} back-edges")

        check("startable implies loop-free and unrowed",
              all(r["loopfree"] and not r["rowed"] for r in startable))
        check("startable implies every callee rowed",
              all(all(c in rowed for c in r["uniq_callees"]) for r in startable))
        print()
        print(f"  measured: {len(rows)} entries | {len(loopfree)} loop-free | "
              f"{len(callfree)} call-free unrowed | {len(withcalls)} with-calls unrowed")
        return 0 if ok else 1

    blockers: dict[str, int] = defaultdict(int)
    for r in withcalls:
        for m in r["missing"]:
            blockers[m] += 1

    if args.markdown:
        print(f"| class | count |")
        print(f"|---|---|")
        print(f"| image entries | {len(rows)} |")
        print(f"| loop-free, no indirect | {len(loopfree)} |")
        print(f"| ...call-free **and unrowed** (startable now) | **{len(callfree)}** |")
        print(f"| ...with calls **and unrowed** | {len(withcalls)} |")
        print(f"| loop-bearing | {len(rows) - len(loopfree)} |")
        print()
        print("| symbol | instrs | status |")
        print("|---|---|---|")
        for r in sorted(callfree, key=lambda r: r["ninstr"])[:args.limit]:
            print(f"| `{r['symbol']}` | {r['ninstr']} | ✅ startable, call-free |")
        for r in sorted(withcalls, key=lambda r: r["ninstr"]):
            st = "✅ startable" if r["startable"] else "blocked on `" + "`, `".join(r["missing"]) + "`"
            print(f"| `{r['symbol']}` | {r['ninstr']} | {st} |")
        return 0

    print(f"callee-composition-queue: {len(rows)} image entries, {len(rowed)} rowed symbols")
    print(f"  loop-free, no indirect                 : {len(loopfree)}")
    print(f"    call-free AND unrowed (startable)    : {len(callfree)}")
    print(f"    with calls AND unrowed               : {len(withcalls)}")
    print(f"  loop-bearing                           : {len(rows) - len(loopfree)}")
    print()
    print("STARTABLE NOW — call-free, loop-free, unrowed (smallest first):")
    for r in sorted(callfree, key=lambda r: r["ninstr"])[:args.limit]:
        print(f"  {r['symbol']:<48} {r['ninstr']:>4} instrs")
    if withcalls:
        print()
        print("LOOP-FREE WITH CALLS (composition lane):")
        for r in sorted(withcalls, key=lambda r: r["ninstr"]):
            st = "STARTABLE" if r["startable"] else "blocked: " + ",".join(r["missing"])
            print(f"  {r['symbol']:<48} {r['ninstr']:>4} instrs  {st}")
    if blockers:
        print()
        print("Unrowed callees blocking the composition lane (row these first, #12035):")
        for sym, n in sorted(blockers.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"  {sym:<48} blocks {n}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
