#!/usr/bin/env python3
"""check-phase-entry-pinned.py — is each phase's ENTRY PC pinned by
`guestImageCodeReq`?  (GH #12166 / #10552, bead evm-asm-4ch8f.64)

## The property, and why it is a gate and not a note

`TopComposition.lean` proves `runStatelessGuestSound_of_phases`: six named
phase hypotheses over ONE shared `cr` compose into the whole-guest statement.
Instantiating that theorem at the real image means taking `cr :=
`Codegen.guestImageCodeReq`.  The same file proves
`cpsTripleWithin_needs_entry_code`: a phase whose `cr` leaves its own ENTRY
address unpinned (`cr entry = none`) is **UNSATISFIABLE** — the phase
hypothesis is FALSE, not merely weak, because `cpsTripleWithin` ranges over
every state satisfying `cr`, including the one whose code memory is exactly
`cr` and is therefore already halted at the entry.

So "is this phase's entry pinned?" is a *precondition on being allowed to
write the phase statement down at all*.  It elaborates fine either way; only
this arithmetic distinguishes a real hypothesis from a vacuous one.  #12166
closed as a CONSTRAINT for exactly that reason, and warned that the failure
mode is citing the coverage-floor GATE CONSTANT
(`guest_image_coverage.EXPECTED_COVERED_BYTES_FLOOR`) in place of measuring.
This script measures; it never reads a floor constant.

## What it checks

1. Every phase entry named by a `*Shape` definition in `TopComposition.lean`
   is resolved to a concrete PC where possible, and each resolved PC is
   tested against the live pinned set.
2. The five inter-phase boundaries are `GuestPhaseLayout` FIELDS
   (`L.pcAfter*`) — a layout parameter, not a fixed address.  They resolve
   only once a non-demo `GuestPhaseLayout` instance fixes them, so today they
   report UNDETERMINED.  That is the weaker-but-real half of the check: the
   one entry we definitely need, `GUEST_ENTRY`, is checked unconditionally,
   together with the unconverted `_start` shell extent that contains it.
3. An expectation record (below) pins the current answer, so a change in
   either direction goes red instead of passing unread: a newly PINNED entry
   is the signal that a phase may now be statable, and a newly unpinned one
   is a regression.

## Pinned set, exactly

`guestImageCodeReq = CodeReq.ofEntries guestImageEntries`, and
`CodeReq.ofProg base prog` pins `base + 4*i` for `i < prog.length`.  So an
address is pinned iff it is 4-aligned relative to some linked converted
entry's base and lies inside that entry's `4 * length` extent.  Lengths come
from the kernel-checked `#guard <prog>.length = N` pins, via
`guest_image_coverage.load_converted` — the same inputs `guestImageEntries`
is generated from, so this cannot disagree with the Lean image by
construction.

Usage:
  python3 scripts/check-phase-entry-pinned.py             # human table
  python3 scripts/check-phase-entry-pinned.py --md        # markdown table
  python3 scripts/check-phase-entry-pinned.py --check     # CI gate
  python3 scripts/check-phase-entry-pinned.py --self-test # negative control
  python3 scripts/check-phase-entry-pinned.py --entry ssz_merkleize --entry 0x80001234
      # ad-hoc probe: is this symbol / address pinned?  Use this the moment a
      # phase boundary is CHOSEN, before it is written into Lean.
"""

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from guest_image_coverage import (  # noqa: E402
    TEXT_BASE,
    load_converted,
    read_guest_addrs,
    read_text_symbols,
)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TOPCOMP = "EvmAsm/Codegen/Proofs/TopComposition.lean"
ENTRYSPEC = "EvmAsm/Stateless/EntrySpec.lean"

# ---------------------------------------------------------------------------
# Expectation record (#12166).  MEASURED, not assumed — re-derive with a plain
# run of this script, never by copying a coverage floor.
#
# Live at the time of writing: `GUEST_ENTRY = 0x80000000` is the base of the
# UNCONVERTED `_start` shell, so it is not pinned, so
# `InputDecodePhaseShape guestImageCodeReq _ L` is FALSE for any layout with
# `pcAfterDecode ≠ GUEST_ENTRY`.  The other five entries are `L.pcAfter*`
# fields with no committed non-demo layout, so they have no PC to test yet.
#
# Flip `EXPECTED_GUEST_ENTRY_PINNED` to True only together with the
# measurement that shows `_start` converted and linked; the point of the
# constant is that the flip is a reviewed event.
EXPECTED_GUEST_ENTRY_PINNED = False
# Phase entries that resolve to a concrete PC at all (the rest are layout
# parameters).  Rises as boundaries are chosen.
EXPECTED_RESOLVED_PHASE_ENTRIES = 1
# Resolved phase entries that are pinned.  This is the number that has to reach
# EXPECTED_RESOLVED_PHASE_ENTRIES (at 6) before the six-hypothesis family can
# be stated at `guestImageCodeReq`.
EXPECTED_PINNED_PHASE_ENTRIES = 0

# `demoLayout` is TopComposition's §5 anti-vacuity witness: it collapses all
# five boundaries onto `GUEST_ENTRY` and is stated at `demoCr` (a single
# EBREAK), NOT at the image CodeReq.  Reading its fields as chosen production
# boundaries would report five bogus "resolved" entries, so it is excluded by
# name.  Do not grow this list without saying which `cr` the layout is for.
DEMO_LAYOUTS = {"demoLayout"}

# Phase order for the report = the composition order in
# `runStatelessGuestSound_of_phases`.
PHASE_ORDER = [
    "InputDecodePhaseShape",
    "WitnessDbPhaseShape",
    "HeaderChainPhaseShape",
    "ExecPhaseShape",
    "StateRootPhaseShape",
    "VerdictPublishShape",
]


def read(path):
    with open(os.path.join(ROOT, path)) as f:
        return f.read()


def read_guest_entry(src=None):
    """`GUEST_ENTRY` from EntrySpec.lean — parsed, never hardcoded."""
    src = read(ENTRYSPEC) if src is None else src
    m = re.search(r"^def GUEST_ENTRY : Word := (0x[0-9a-fA-F]+)", src, re.M)
    if not m:
        sys.exit(f"could not parse `def GUEST_ENTRY : Word := 0x…` from {ENTRYSPEC}")
    return int(m.group(1), 16)


_SHAPE_ENTRY = re.compile(
    r"cps(Halt)?TripleWithin\s+(\S+)\s+(\S+)(?:\s+(\S+))?\s+cr\b")


def read_phase_entries(src=None):
    """name -> (entry_expr, exit_expr_or_None, is_halt), parsed from the
    `*Shape` defs of TopComposition.lean.

    Derived from the source rather than listed here so that a re-shape of the
    phase decomposition (which the file explicitly expects: the boundaries are
    a LAYOUT PARAMETER) flows through instead of silently checking the old
    boundaries."""
    src = read(TOPCOMP) if src is None else src
    out = {}
    # Split on top-level `def`/`theorem` starts; keep only Shape defs.
    for m in re.finditer(r"^def (\w*Shape)\b(.*?)(?=^(?:def|theorem|end|/-)\s)",
                         src, re.M | re.S):
        name, body = m.group(1), m.group(2)
        hit = _SHAPE_ENTRY.search(body)
        if not hit:
            continue
        # Argument order: `cpsTripleWithin n entry exit cr P Q` and
        # `cpsHaltTripleWithin n entry cr P Q` — group 2 is the step BUDGET in
        # both, so the entry PC is group 3 either way (mistaking the budget for
        # the entry is a silent mis-parse: `L.budgetDecode` also "resolves" to
        # UNDETERMINED and the table looks plausible).
        halt = hit.group(1) is not None
        entry = hit.group(3)
        exit_ = None if halt else hit.group(4)
        out[name] = (entry, exit_, halt)
    if not out:
        sys.exit(f"parsed no `*Shape` phase defs from {TOPCOMP} — "
                 "refusing to report a clean sheet from a failed parse")
    bad = sorted(n for n, (e, _, _) in out.items() if "budget" in e.lower())
    if bad:
        sys.exit(f"mis-parse: phase entry expression looks like a step budget "
                 f"for {bad} — the entry PC is the argument AFTER the budget. "
                 "Refusing to report; fix _SHAPE_ENTRY.")
    return out


def read_layout_instances(src=None):
    """layout def name -> {field: rhs} for every `: GuestPhaseLayout where`
    instance, demo layouts included (the caller filters)."""
    src = read(TOPCOMP) if src is None else src
    out = {}
    for m in re.finditer(
            r"^def (\w+)\s*:\s*GuestPhaseLayout\s+where\s*\n((?:[ \t]+\S.*\n)+)",
            src, re.M):
        fields = {}
        for fm in re.finditer(r"^\s+(\w+)\s*:=\s*(.+?)\s*$", m.group(2), re.M):
            fields[fm.group(1)] = fm.group(2)
        out[m.group(1)] = fields
    return out


def pinned_blocks():
    """[(base, n_instrs, entry_symbol, prog)] for every LINKED converted
    entry — exactly the rows `guestImageEntries` is generated from."""
    syms, text_end, converted = load_converted()
    addr_of = {n: a for a, n in syms}
    blocks = []
    for entry, (prog, prog_bytes, _path) in converted.items():
        if entry not in addr_of:
            continue  # converted but NOT linked: excluded from the image CodeReq
        blocks.append((addr_of[entry], prog_bytes // 4, entry, prog))
    blocks.sort()
    return syms, text_end, blocks


def probe(pc, blocks):
    """(pinned, reason). Mirrors CodeReq.ofProg's 4-strided pin exactly."""
    for base, n, entry, prog in blocks:
        if base <= pc < base + 4 * n:
            if (pc - base) % 4 == 0:
                return True, f"{entry} (+0x{pc - base:x} of 0x{4 * n:x}) `{prog}`"
            return False, (f"inside {entry} but MISALIGNED "
                           f"(+0x{pc - base:x}) — ofProg pins 4-strided only")
    return False, "no linked converted entry covers this address"


def owning_symbol(pc, syms, text_end):
    """(symbol, sym_start, sym_end) of the .text symbol whose linker extent
    contains `pc`, or None."""
    for i, (addr, name) in enumerate(syms):
        end = syms[i + 1][0] if i + 1 < len(syms) else text_end
        if addr <= pc < end:
            return name, addr, end
    return None


def resolve(expr, guest_entry, guest_addrs, layouts):
    """Phase-entry expression -> (pc or None, note).

    Resolvable forms: `GUEST_ENTRY`, a `GuestAddrs.<sym>` / bare linked
    symbol, a hex/decimal literal, and `L.<field>` once a non-demo layout
    fixes that field to one of the above."""
    e = expr.strip().strip("()")
    if e == "GUEST_ENTRY":
        return guest_entry, "ELF entry (`Stateless.GUEST_ENTRY`)"
    if re.fullmatch(r"0x[0-9a-fA-F]+", e):
        return int(e, 16), "literal"
    if re.fullmatch(r"\d+", e):
        return int(e), "literal"
    sym = e.split(".")[-1] if e.startswith("GuestAddrs.") else e
    if sym in guest_addrs:
        return guest_addrs[sym], f"`GuestAddrs.{sym}`"
    m = re.fullmatch(r"L\.(\w+)", e)
    if m:
        field = m.group(1)
        real = {n: f for n, f in layouts.items() if n not in DEMO_LAYOUTS}
        for lname, fields in sorted(real.items()):
            if field in fields:
                pc, note = resolve(fields[field], guest_entry, guest_addrs, {})
                if pc is not None:
                    return pc, f"via `{lname}.{field}` = {fields[field]}"
        return None, (f"UNDETERMINED — `GuestPhaseLayout.{field}` is a layout "
                      "parameter and no non-demo layout fixes it")
    return None, f"unresolved expression `{expr}`"


def rows(guest_entry, guest_addrs, phases, layouts, syms, text_end, blocks):
    out = []
    for name in PHASE_ORDER + [n for n in phases if n not in PHASE_ORDER]:
        if name not in phases:
            continue
        entry_expr, _exit, halt = phases[name]
        pc, note = resolve(entry_expr, guest_entry, guest_addrs, layouts)
        if pc is None:
            out.append((name, entry_expr, None, None, "UNDETERMINED", note))
            continue
        ok, why = probe(pc, blocks)
        own = owning_symbol(pc, syms, text_end)
        own_s = (f"{own[0]} [0x{own[1]:08x},0x{own[2]:08x})" if own
                 else "outside .text")
        out.append((name, entry_expr, pc, own_s,
                    "PINNED" if ok else "UNPINNED", f"{note}; {why}"))
    return out


def start_shell(syms, text_end, blocks):
    """(_start extent, pinned bytes inside it) — the shell that contains
    GUEST_ENTRY.  Reported because it is the specific unconverted region that
    blocks the one entry we definitely need."""
    for i, (addr, name) in enumerate(syms):
        if name != "_start":
            continue
        end = syms[i + 1][0] if i + 1 < len(syms) else text_end
        pin = sum(4 * n for base, n, _, _ in blocks if addr <= base < end)
        return addr, end, pin
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--md", action="store_true", help="markdown output")
    ap.add_argument("--check", action="store_true",
                    help="CI gate: exit 1 on expectation drift")
    ap.add_argument("--self-test", action="store_true",
                    help="negative control: the pin probe must report PINNED "
                         "for a planted block and UNPINNED without it")
    ap.add_argument("--entry", action="append", default=[], metavar="SYM|0xADDR",
                    help="ad-hoc probe of an extra candidate entry "
                         "(repeatable)")
    args = ap.parse_args()

    guest_entry = read_guest_entry()
    guest_addrs = read_guest_addrs()
    phases = read_phase_entries()
    layouts = read_layout_instances()
    syms, text_end, blocks = pinned_blocks()

    if args.self_test:
        return self_test(guest_entry, guest_addrs, phases, layouts, blocks)

    table = rows(guest_entry, guest_addrs, phases, layouts, syms, text_end,
                 blocks)
    ge_pinned, ge_why = probe(guest_entry, blocks)
    n_resolved = sum(1 for r in table if r[2] is not None)
    n_pinned = sum(1 for r in table if r[4] == "PINNED")
    covered = sum(4 * n for _, n, _, _ in blocks)
    text_size = text_end - TEXT_BASE

    if args.md:
        print("| phase | entry expression | entry PC | owning `.text` symbol "
              "| pinned? | note |")
        print("|---|---|---|---|---|---|")
        for name, expr, pc, own, status, note in table:
            pcs = f"`0x{pc:08x}`" if pc is not None else "—"
            print(f"| `{name}` | `{expr}` | {pcs} | "
                  f"{('`' + own + '`') if own else '—'} | {status} | {note} |")
        print()
    else:
        print(f"phase entries: {len(table)}  resolved: {n_resolved}  "
              f"pinned: {n_pinned}")
        for name, expr, pc, own, status, note in table:
            pcs = f"0x{pc:08x}" if pc is not None else "----------"
            print(f"  {status:12s} {name:24s} entry={expr:22s} {pcs}")
            print(f"               {note}")

    print(f"GUEST_ENTRY = 0x{guest_entry:08x}: "
          f"{'PINNED' if ge_pinned else 'UNPINNED'} — {ge_why}")
    sh = start_shell(syms, text_end, blocks)
    if sh:
        lo, hi, pin = sh
        print(f"_start shell: [0x{lo:08x}, 0x{hi:08x}) = {hi - lo} B, "
              f"{pin} B pinned, {hi - lo - pin} B unconverted")
    print(f"live pinned extent: {covered} B of {text_size} B .text "
          f"({100 * covered / text_size:.2f}%), {len(blocks)} linked entries")

    for spec in args.entry:
        pc, note = resolve(spec, guest_entry, guest_addrs, layouts)
        if pc is None:
            print(f"probe {spec}: UNRESOLVED — {note}")
            continue
        ok, why = probe(pc, blocks)
        own = owning_symbol(pc, syms, text_end)
        print(f"probe {spec} = 0x{pc:08x}: {'PINNED' if ok else 'UNPINNED'} "
              f"— {why}" + (f" [in {own[0]}]" if own else ""))

    errs = []
    if ge_pinned != EXPECTED_GUEST_ENTRY_PINNED:
        errs.append(
            f"GUEST_ENTRY pinned = {ge_pinned}, expected "
            f"{EXPECTED_GUEST_ENTRY_PINNED}. "
            + ("GOOD NEWS: the ELF entry is now covered, so "
               "InputDecodePhaseShape is no longer refuted by "
               "cpsTripleWithin_needs_entry_code on its entry address. Set "
               "EXPECTED_GUEST_ENTRY_PINNED = True and revisit #12166/#10552 "
               "— note the lemma still applies at every OTHER address the "
               "phase fetches."
               if ge_pinned else
               "REGRESSION: the ELF entry lost its pin."))
    if n_resolved != EXPECTED_RESOLVED_PHASE_ENTRIES:
        errs.append(
            f"resolved phase entries = {n_resolved}, expected "
            f"{EXPECTED_RESOLVED_PHASE_ENTRIES} — the phase decomposition or a "
            "GuestPhaseLayout instance changed. Update the constant together "
            "with the pinned/unpinned finding for the new boundaries.")
    if n_pinned != EXPECTED_PINNED_PHASE_ENTRIES:
        errs.append(
            f"pinned phase entries = {n_pinned}, expected "
            f"{EXPECTED_PINNED_PHASE_ENTRIES} — update the constant; when it "
            "reaches the resolved count at 6 phases, the six-hypothesis family "
            "clears the #12166 entry-coverage precondition.")
    if errs:
        for e in errs:
            print(f"PHASE ENTRY PIN DRIFT: {e}", file=sys.stderr)
        if args.check:
            sys.exit(1)
        return
    if args.check:
        print("check-phase-entry-pinned: OK — live pinned/unpinned status "
              "matches the recorded expectation")


def self_test(guest_entry, guest_addrs, phases, layouts, blocks):
    """Negative control.  A gate whose probe always answered UNPINNED, or
    whose resolver always answered UNDETERMINED, would pass today for the
    wrong reason.  So: prove the probe can say PINNED, can say UNPINNED, and
    rejects a misaligned or past-extent hit; and prove the resolver DOES
    follow a non-demo layout once one exists (planted here), rather than
    reporting UNDETERMINED because it cannot resolve anything at all."""
    fails = []
    # Resolver control: plant a layout fixing `pcAfterDecode` to a real linked
    # symbol and require the L-field path to find it.
    if blocks:
        planted_sym = blocks[0][2]
        planted_layouts = dict(layouts)
        planted_layouts["plantedLayout"] = {
            "pcAfterDecode": f"GuestAddrs.{planted_sym}"}
        pc, note = resolve("L.pcAfterDecode", guest_entry, guest_addrs,
                           planted_layouts)
        if pc != blocks[0][0]:
            fails.append(
                f"planted non-demo layout not followed: L.pcAfterDecode "
                f"resolved to {pc} (expected 0x{blocks[0][0]:08x}); {note}")
        # ...and require the demo layout to be IGNORED (it collapses every
        # boundary onto GUEST_ENTRY at `demoCr`, not at the image CodeReq).
        if "demoLayout" in layouts:
            pc2, _ = resolve("L.pcAfterDecode", guest_entry, guest_addrs,
                             {"demoLayout": layouts["demoLayout"]})
            if pc2 is not None:
                fails.append("demoLayout was read as a production layout — "
                             "its boundaries are the §5 anti-vacuity witness")
        else:
            fails.append("demoLayout not parsed from TopComposition.lean — the "
                         "layout-instance parser is not seeing any instance")
    if len(phases) != 6:
        fails.append(f"parsed {len(phases)} phase shapes, expected 6 "
                     "(TopComposition's six named hypotheses)")
    ok, _ = probe(guest_entry, blocks)
    if ok:
        fails.append("live GUEST_ENTRY probe says PINNED; the negative half of "
                     "this control assumes it is not (see #12166)")
    planted = blocks + [(guest_entry, 4, "planted_start", "planted_prog")]
    ok, why = probe(guest_entry, planted)
    if not ok:
        fails.append(f"planted block covering GUEST_ENTRY not detected: {why}")
    ok, why = probe(guest_entry + 2, planted)
    if ok:
        fails.append("misaligned address inside a planted block reported "
                     "PINNED — ofProg pins 4-strided addresses only")
    ok, _ = probe(guest_entry + 4 * 4, planted)
    if ok:
        fails.append("address past the planted block's extent reported PINNED")
    if not blocks:
        fails.append("no linked converted blocks parsed — the pinned set is "
                     "empty, so every probe would answer UNPINNED vacuously")
    else:
        base, n, entry, _ = blocks[0]
        ok, why = probe(base, blocks)
        if not ok:
            fails.append(f"a real linked entry ({entry} @ 0x{base:08x}) probed "
                         f"UNPINNED: {why}")
    for f in fails:
        print(f"SELF-TEST FAIL: {f}", file=sys.stderr)
    if fails:
        sys.exit(1)
    print(f"check-phase-entry-pinned --self-test: OK "
          f"({len(blocks)} linked blocks; probe distinguishes pinned, "
          f"unpinned, misaligned and past-extent)")


if __name__ == "__main__":
    main()
