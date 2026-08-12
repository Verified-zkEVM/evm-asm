#!/usr/bin/env python3
"""Pointer-follow reference census for guest asm (GH #11229).

Same-line `la <reg>, S` + load-off-reg censuses are an UPPER BOUND on
deadness, never a proof: they miss pointer arguments passed to callees
that load through the argument register.

This tool is a *different instrument*, not a wider regex:

1. Resolve every `la <reg>, S` (including packed `;`-separated lines).
2. Classify same-line load off `<reg>` (classic census).
3. Track `<reg>` through `mv` / `addi <reg>, <reg>, imm` within a short
   window until a `jal`/`call`.
4. If the tracked value sits in an argument register (`a0`–`a7` / `x10`–
   `x17`) at the call, inspect the callee body for loads that use that
   argument as base (directly or via `add`/`addi` derived temps).

Verdicts per symbol
-------------------
* ``live_direct``     — same-line load off the `la` destination
* ``live_via_callee`` — no same-line load, but a callee loads through the
  argument that received `S`
* ``unresolved``      — `la` into an arg reg (or moved there) with a
  following `jal`, but callee body missing / not analyzable / no load
  found (named gap, NOT "dead")
* ``no_la``           — symbol never appears as `la` target
* ``upper_bound_dead``— has `la` sites, none direct, none via-callee, none
  unresolved — still only an upper bound (store-reload / neighbour
  displacement remain invisible)

Acceptance demo (issue #11229): symbols the same-line census calls
"no load" that this detector proves `live_via_callee`.

Usage
-----
    python3 scripts/pointer-follow-census.py gen-out/stateless_guest.s
    python3 scripts/pointer-follow-census.py gen-out/stateless_guest.s \\
        --symbol bmvmx_gascost --demo
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

# ABI argument registers and x-name aliases (LP64).
ARG_REGS = {
    "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7",
    "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17",
}
ARG_CANON = {
    "a0": "a0", "x10": "a0",
    "a1": "a1", "x11": "a1",
    "a2": "a2", "x12": "a2",
    "a3": "a3", "x13": "a3",
    "a4": "a4", "x14": "a4",
    "a5": "a5", "x15": "a5",
    "a6": "a6", "x16": "a6",
    "a7": "a7", "x17": "a7",
}

LOAD_MNEMS = {"ld", "lwu", "lw", "lhu", "lh", "lbu", "lb", "fld", "flw"}
STORE_MNEMS = {"sd", "sw", "sh", "sb", "fsd", "fsw"}
CALL_MNEMS = {"jal", "call", "tail"}
# Stop tracking across control transfer / clobber barriers.
BARRIER_MNEMS = {"jal", "call", "tail", "jalr", "jr", "ret", "ecall", "ebreak"}

RE_LA = re.compile(r"\bla\s+([A-Za-z0-9]+)\s*,\s*([A-Za-z_.$][\w.$]*)")
RE_LABEL = re.compile(r"^([A-Za-z_.$][\w.$]*):$")
RE_INSN = re.compile(r"^([A-Za-z.]+)\b\s*(.*)$")
RE_MEM = re.compile(r"^(-?\d+)\(([A-Za-z0-9]+)\)$")
RE_JAL = re.compile(
    r"^(?:jal\s+(?:(?:ra|x1)\s*,\s*)?|call\s+|tail\s+)([A-Za-z_.$][\w.$]*)$"
)
RE_MV = re.compile(r"^(?:mv|move)\s+([A-Za-z0-9]+)\s*,\s*([A-Za-z0-9]+)$")
RE_ADDI = re.compile(
    r"^(?:addi|addiu)\s+([A-Za-z0-9]+)\s*,\s*([A-Za-z0-9]+)\s*,\s*(-?\d+|0x[0-9a-fA-F]+)$"
)
RE_ADD = re.compile(
    r"^add\s+([A-Za-z0-9]+)\s*,\s*([A-Za-z0-9]+)\s*,\s*([A-Za-z0-9]+)$"
)


def canon_reg(r: str) -> str:
    r = r.lower()
    return ARG_CANON.get(r, r)


def split_packed(line: str) -> list[str]:
    """Split a source line into individual asm statements."""
    # strip comments
    c = re.split(r"(?<!:)//|#|--", line, maxsplit=1)[0]
    c = c.strip()
    if not c:
        return []
    parts = []
    for sub in c.split(";"):
        sub = sub.strip()
        if sub:
            parts.append(sub)
    return parts


@dataclass
class Insn:
    idx: int          # global statement index
    line_no: int      # 1-based source line
    text: str
    mnem: str
    args: str


@dataclass
class LaSite:
    line_no: int
    reg: str
    sym: str
    insn_idx: int
    same_line_load: bool
    text: str


@dataclass
class CalleeHit:
    callee: str
    arg_reg: str
    load_text: str
    load_line: int


@dataclass
class SymReport:
    sym: str
    la_sites: list[LaSite] = field(default_factory=list)
    direct_loads: list[LaSite] = field(default_factory=list)
    via_callee: list[tuple[LaSite, CalleeHit]] = field(default_factory=list)
    unresolved: list[tuple[LaSite, str, str]] = field(default_factory=list)
    # unresolved: site, reason, callee_or_reg

    @property
    def verdict(self) -> str:
        if not self.la_sites:
            return "no_la"
        if self.direct_loads:
            return "live_direct"
        if self.via_callee:
            return "live_via_callee"
        if self.unresolved:
            return "unresolved"
        return "upper_bound_dead"


def parse_asm(path: Path) -> tuple[list[Insn], dict[str, int], list[str]]:
    """Return (insns, label->insn_idx, source_lines)."""
    src_lines = path.read_text(errors="replace").splitlines()
    insns: list[Insn] = []
    labels: dict[str, int] = {}
    idx = 0
    for li, line in enumerate(src_lines, 1):
        for stmt in split_packed(line):
            lm = RE_LABEL.match(stmt)
            if lm:
                labels[lm.group(1)] = idx
                continue
            im = RE_INSN.match(stmt)
            if not im:
                continue
            mnem = im.group(1).lower()
            args = im.group(2).strip()
            insns.append(Insn(idx, li, stmt, mnem, args))
            idx += 1
    return insns, labels, src_lines


def mem_base(arg_tok: str) -> str | None:
    m = RE_MEM.match(arg_tok.strip())
    return m.group(2).lower() if m else None


def insn_loads_from(insn: Insn, bases: set[str]) -> bool:
    if insn.mnem not in LOAD_MNEMS:
        return False
    # ld rd, off(rs) — last token is mem
    toks = [t.strip() for t in insn.args.split(",")]
    if not toks:
        return False
    b = mem_base(toks[-1])
    return b is not None and b.lower() in bases


def track_aliases(
    insns: list[Insn], start: int, seed_reg: str, window: int = 24
) -> tuple[dict[int, set[str]], int | None, str | None]:
    """Forward-track registers holding the pointer from seed_reg.

    Returns (idx -> live regs holding pointer, jal_idx or None, callee or None).
    """
    live: set[str] = {seed_reg.lower()}
    per_idx: dict[int, set[str]] = {}
    end = min(len(insns), start + 1 + window)
    jal_idx = None
    callee = None
    for i in range(start + 1, end):
        ins = insns[i]
        per_idx[i] = set(live)
        # Detect call first
        if ins.mnem in CALL_MNEMS:
            jm = RE_JAL.match(ins.text.lower().replace("  ", " "))
            # more permissive parse
            cal = None
            if ins.mnem == "jal":
                parts = [p.strip() for p in ins.args.split(",")]
                cal = parts[-1] if parts else None
            elif ins.mnem in ("call", "tail"):
                cal = ins.args.split(",")[0].strip() if ins.args else None
            if cal and re.match(r"^[A-Za-z_.$][\w.$]*$", cal):
                jal_idx = i
                callee = cal
                break
            # jalr / unknown — barrier
            break
        if ins.mnem in BARRIER_MNEMS:
            break

        # Kill / propagate
        text = ins.text
        # mv rd, rs
        m = RE_MV.match(text)
        if m:
            rd, rs = m.group(1).lower(), m.group(2).lower()
            if rs in live:
                live.add(rd)
            elif rd in live:
                live.discard(rd)
            continue
        m = RE_ADDI.match(text)
        if m:
            rd, rs = m.group(1).lower(), m.group(2).lower()
            if rs in live:
                live.add(rd)
            elif rd in live and rd != rs:
                live.discard(rd)
            continue
        m = RE_ADD.match(text)
        if m:
            rd, rs1, rs2 = m.group(1).lower(), m.group(2).lower(), m.group(3).lower()
            if rs1 in live or rs2 in live:
                live.add(rd)
            elif rd in live:
                live.discard(rd)
            continue
        # Generic def: if first operand is rd for arithmetic/logic, kill
        if ins.mnem in LOAD_MNEMS | STORE_MNEMS:
            # loads define rd but don't kill pointer in rs
            toks = [t.strip().lower() for t in ins.args.split(",") if t.strip()]
            if ins.mnem in LOAD_MNEMS and toks:
                rd = toks[0]
                if rd in live and mem_base(toks[-1] if len(toks) > 1 else "") not in (
                    None,
                ):
                    # loading *into* a reg that held the pointer kills it
                    b = mem_base(toks[-1]) if len(toks) > 1 else None
                    if b not in live:
                        live.discard(rd)
            continue
        # li / lui kill rd
        if ins.mnem in ("li", "lui", "auipc", "lla", "la"):
            toks = [t.strip().lower() for t in ins.args.split(",") if t.strip()]
            if toks and toks[0] in live:
                live.discard(toks[0])
            continue
    return per_idx, jal_idx, callee


def callee_arg_bases(arg_reg: str) -> set[str]:
    """Registers that may hold the pointer inside callee at entry + x-name."""
    c = canon_reg(arg_reg)
    # both ABI and x-name
    inv = {v: k for k, v in [("x10", "a0"), ("x11", "a1"), ("x12", "a2"),
                              ("x13", "a3"), ("x14", "a4"), ("x15", "a5"),
                              ("x16", "a6"), ("x17", "a7")]}
    bases = {c, arg_reg.lower()}
    for xn, an in [("x10", "a0"), ("x11", "a1"), ("x12", "a2"), ("x13", "a3"),
                   ("x14", "a4"), ("x15", "a5"), ("x16", "a6"), ("x17", "a7")]:
        if c == an:
            bases.add(xn)
        if c == xn:
            bases.add(an)
    return bases


def analyze_callee_loads(
    insns: list[Insn], labels: dict[str, int], callee: str, arg_reg: str,
    max_insns: int = 120,
) -> CalleeHit | None:
    """Return first load through arg_reg (or derived) in callee body."""
    if callee not in labels:
        return None
    start = labels[callee]
    bases = callee_arg_bases(arg_reg)
    live = set(bases)
    end = min(len(insns), start + max_insns)
    for i in range(start, end):
        ins = insns[i]
        # nested call — stop (conservative)
        if i > start and ins.mnem in CALL_MNEMS:
            break
        if ins.mnem == "ret" or (
            ins.mnem == "jalr" and re.search(r"\b(ra|x1)\b", ins.args)
        ):
            # check loads before ret; ret ends body
            break
        # propagate add/addi/mv from live bases (u256_add_be: add x7, x10, x5)
        m = RE_MV.match(ins.text)
        if m:
            rd, rs = m.group(1).lower(), m.group(2).lower()
            if rs in live:
                live.add(rd)
            elif rd in live:
                live.discard(rd)
        m = RE_ADDI.match(ins.text)
        if m:
            rd, rs = m.group(1).lower(), m.group(2).lower()
            if rs in live:
                live.add(rd)
            elif rd in live and rd != rs:
                live.discard(rd)
        m = RE_ADD.match(ins.text)
        if m:
            rd, rs1, rs2 = (
                m.group(1).lower(),
                m.group(2).lower(),
                m.group(3).lower(),
            )
            if rs1 in live or rs2 in live:
                live.add(rd)
            elif rd in live:
                live.discard(rd)
        if insn_loads_from(ins, live):
            return CalleeHit(callee, canon_reg(arg_reg), ins.text, ins.line_no)
        # kill on li into live
        if ins.mnem in ("li", "lui", "la", "lla", "auipc"):
            toks = [t.strip().lower() for t in ins.args.split(",") if t.strip()]
            if toks and toks[0] in live and toks[0] not in bases:
                live.discard(toks[0])
    return None


def same_line_load_off_reg(line_text: str, reg: str) -> bool:
    """True if any load on this packed line uses reg as base."""
    for stmt in split_packed(line_text):
        im = RE_INSN.match(stmt)
        if not im:
            continue
        mnem = im.group(1).lower()
        if mnem not in LOAD_MNEMS:
            continue
        args = im.group(2)
        toks = [t.strip() for t in args.split(",")]
        if not toks:
            continue
        b = mem_base(toks[-1])
        if b and b.lower() == reg.lower():
            return True
    return False


def collect_la_sites(insns: list[Insn], src_lines: list[str]) -> list[LaSite]:
    sites: list[LaSite] = []
    # Index insns by source line once (avoid O(lines×insns)).
    by_line: dict[int, list[Insn]] = defaultdict(list)
    for ins in insns:
        by_line[ins.line_no].append(ins)
    for li, line in enumerate(src_lines, 1):
        stmts = split_packed(line)
        if not stmts:
            continue
        line_insns = by_line.get(li, [])
        text_to_idx = {ins.text: ins.idx for ins in line_insns}
        fallback = line_insns[0].idx if line_insns else -1
        for stmt in stmts:
            m = RE_LA.search(stmt)
            if not m:
                continue
            reg, sym = m.group(1), m.group(2)
            if sym.startswith(".L"):
                continue
            sites.append(
                LaSite(
                    line_no=li,
                    reg=reg.lower(),
                    sym=sym,
                    insn_idx=text_to_idx.get(stmt, fallback),
                    same_line_load=same_line_load_off_reg(line, reg),
                    text=line.strip()[:160],
                )
            )
    return sites


def analyze_symbol(
    sym: str,
    sites: list[LaSite],
    insns: list[Insn],
    labels: dict[str, int],
) -> SymReport:
    rep = SymReport(sym=sym, la_sites=list(sites))
    for site in sites:
        if site.same_line_load:
            rep.direct_loads.append(site)
            continue
        if site.insn_idx < 0:
            rep.unresolved.append((site, "no_insn_idx", ""))
            continue
        _per, jal_idx, callee = track_aliases(insns, site.insn_idx, site.reg)
        if jal_idx is None or callee is None:
            # Was the seed already an arg reg? still flag if jal somewhere?
            continue
        live_at_jal = _per.get(jal_idx, set())
        # which arg regs hold the pointer?
        arg_holders = [r for r in live_at_jal if canon_reg(r) in ARG_REGS or r in ARG_REGS]
        # also if seed moved into arg
        arg_holders = list({canon_reg(r) for r in arg_holders if canon_reg(r) in {
            "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"
        }})
        if not arg_holders:
            # jal but pointer not in arg reg — may be address-taken differently
            if canon_reg(site.reg) in {"a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"}:
                arg_holders = [canon_reg(site.reg)]
            else:
                rep.unresolved.append((site, "jal_but_not_in_arg", callee))
                continue
        found = False
        for ar in arg_holders:
            hit = analyze_callee_loads(insns, labels, callee, ar)
            if hit:
                rep.via_callee.append((site, hit))
                found = True
                break
        if not found:
            if callee not in labels:
                rep.unresolved.append((site, "callee_not_found", callee))
            else:
                rep.unresolved.append((site, "callee_no_load_found", callee))
    return rep


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("asm", type=Path, help="Emitted guest .s (e.g. gen-out/stateless_guest.s)")
    ap.add_argument("--symbol", action="append", default=[], help="Limit to symbol(s)")
    ap.add_argument("--demo", action="store_true",
                    help="Print same-line vs pointer-follow contrast for demo symbols")
    ap.add_argument("--all-via-callee", action="store_true",
                    help="List every symbol classified live_via_callee")
    ap.add_argument("--json-summary", action="store_true")
    args = ap.parse_args()

    if not args.asm.is_file():
        print(f"error: asm not found: {args.asm}", file=sys.stderr)
        return 2

    insns, labels, src_lines = parse_asm(args.asm)
    all_sites = collect_la_sites(insns, src_lines)
    by_sym: dict[str, list[LaSite]] = defaultdict(list)
    for s in all_sites:
        by_sym[s.sym].append(s)

    print(f"asm: {args.asm}")
    print(f"insns: {len(insns)}  labels: {len(labels)}  la_sites: {len(all_sites)}  symbols_with_la: {len(by_sym)}")

    cache: dict[str, SymReport] = {}

    def get_report(sym: str) -> SymReport:
        if sym not in cache:
            cache[sym] = analyze_symbol(sym, by_sym.get(sym, []), insns, labels)
        return cache[sym]

    # Default analysis set: explicit --symbol, else all symbols with la
    # (full scan only when --all-via-callee or no --demo-only path).
    if args.symbol:
        analyze_list = list(args.symbol)
    elif args.demo and not args.all_via_callee:
        # Fast path: demo candidates only, then expand from their callees' peers
        analyze_list = [
            "bmvmx_gascost", "bmvmx_value", "bmvmx_sender_debit",
            "bmvmx_eff_gas_price", "bmvmx_acct", "bmvmx_cb_post",
            "bmvmx_basefee_be", "bmvmx_priority_fee",
        ]
        # Plus a bounded sample of symbols that appear as la into a0-a7
        sample = []
        for sym, sites in by_sym.items():
            if any(canon_reg(s.reg) in {"a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"}
                   and not s.same_line_load for s in sites):
                sample.append(sym)
            if len(sample) >= 200:
                break
        analyze_list = list(dict.fromkeys(analyze_list + sample))
    else:
        analyze_list = sorted(by_sym.keys())

    reports = [get_report(sym) for sym in analyze_list]

    counts: dict[str, int] = defaultdict(int)
    for r in reports:
        counts[r.verdict] += 1

    print(f"analyzed_symbols: {len(reports)}")
    print("verdict_counts (among analyzed symbols):")
    for k in ("live_direct", "live_via_callee", "unresolved", "upper_bound_dead", "no_la"):
        print(f"  {k:18s} {counts[k]}")

    via = [r for r in reports if r.verdict == "live_via_callee"]
    false_dead = [r for r in via if not r.direct_loads and r.via_callee]
    print(f"\nfalse_dead_upper_bound_broken: {len(false_dead)} "
          f"(same-line 'no load' but live_via_callee)")

    if args.demo:
        demo_syms = [
            "bmvmx_gascost", "bmvmx_value", "bmvmx_sender_debit",
            "bmvmx_eff_gas_price", "bmvmx_acct", "bmvmx_cb_post",
        ]
        print("\n== DEMO (same-line vs pointer-follow) ==")
        shown = 0
        ordered = demo_syms + [r.sym for r in false_dead if r.sym not in demo_syms]
        for sym in ordered:
            if shown >= 10:
                break
            r = get_report(sym)
            if not r.la_sites and r.verdict == "no_la":
                if sym in demo_syms:
                    print(f"\n{sym}: no_la (no la sites in this image)")
                continue
            classic_dead = bool(r.la_sites) and not r.direct_loads
            print(f"\n{sym}:")
            print(f"  classic_same_line: la_sites={len(r.la_sites)} "
                  f"any_load={bool(r.direct_loads)} "
                  f"=> {'NO_LOAD (upper-bound dead)' if classic_dead else 'HAS_LOAD'}")
            print(f"  pointer_follow:    verdict={r.verdict}")
            for site, hit in r.via_callee[:3]:
                print(f"    via_callee: L{site.line_no} la {site.reg}, {sym} "
                      f"-> jal {hit.callee} loads via {hit.arg_reg}: "
                      f"L{hit.load_line} `{hit.load_text}`")
                print(f"      site: {site.text}")
            for site, reason, cal in r.unresolved[:2]:
                print(f"    unresolved: L{site.line_no} {reason} {cal}")
            if classic_dead and r.verdict == "live_via_callee":
                print("  *** ACCEPTANCE: classic says dead; detector proves READ via callee ***")
            shown += 1

    if args.all_via_callee:
        # Full scan if not already
        if len(cache) < len(by_sym):
            for sym in sorted(by_sym.keys()):
                get_report(sym)
        via_all = [r for r in cache.values() if r.verdict == "live_via_callee"]
        print(f"\n== all live_via_callee ({len(via_all)}) ==")
        for r in sorted(via_all, key=lambda x: x.sym):
            cals = sorted({h.callee for _, h in r.via_callee})
            print(f"  {r.sym:40s}  callees={','.join(cals)}")

    if args.symbol:
        for sym in args.symbol:
            r = get_report(sym)
            print(f"\n-- {r.sym} verdict={r.verdict}")
            for s in r.la_sites:
                print(f"  la L{s.line_no} {s.reg} same_line_load={s.same_line_load}")
                print(f"    {s.text}")
            for s, h in r.via_callee:
                print(f"  callee_load {h.callee} {h.arg_reg} L{h.load_line} {h.load_text}")

    if args.json_summary:
        import json
        print(json.dumps({
            "asm": str(args.asm),
            "counts": dict(counts),
            "false_dead_broken": len(false_dead),
            "false_dead_symbols": [r.sym for r in false_dead[:50]],
        }, indent=2))

    if args.demo:
        ok = any(
            (r.verdict == "live_via_callee" and not r.direct_loads)
            for r in cache.values()
        )
        if not ok:
            print("\nNOTE: no false-dead break found in analyzed set.", file=sys.stderr)
            return 1
        print("\nDEMO OK: at least one classic-NO_LOAD symbol is live_via_callee.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
