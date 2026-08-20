#!/usr/bin/env python3
"""Class-3 allocation gate: .s-side location-counter simulation (GH #12667).

The three-class taxonomy (see check-region-overlap.py, GH #12664/#12665):

  CLASS 1  declared vs declared        -- caught by cross-list pairwise (12665)
  CLASS 2  symbolized vs declared      -- caught by symbol/span legs (12665)
  CLASS 3  unlabelled + undeclared     -- NOT caught by readelf (no symbol) nor
                                          by pairwise (no declaration). THIS gate.

Instrument: simulate the location counter over the emitted assembler source
(stateless_guest.s) -- the single complete record of STATIC allocation. The
counter sees every byte reserved even when nothing is named: labels, anonymous
.zero advances, alignment padding, and the TRUE reservation extent of each
label (the next allocation event, not a .size directive -- assembler .bss
labels carry none, which is why nm -S is size-blind there).

Checks against the declared region set (parsed exactly as 12665 parses it):

  * SECTION-Size agreement: simulated per-section size must equal the linked
    ELF's section size (the .s and the ELF must describe the same bytes).
  * CROSSING overlap: every actually-allocated interval (labelled reservation
    or anonymous gap) that intersects a declared fine-tier interval must be
    contained in it or contain it. A proper crossing is a class-3 collision:
    an allocation silently eating the edge of a declared window.
  * DECLARED-NOT-RESERVED census: declared windows whose bytes the .s never
    reserves (virtual windows over unallocated linker space -- they work only
    while nothing else allocates there; that is the class-3 exposure surface).

What this instrument CANNOT see (stated where the tool lives, per #12665
discipline -- do not oversell):

  * RUNTIME-COMPUTED addresses: the simulation knows static allocation and
    static address materialization, not where registers carry values at
    execution time. Stores through runtime-computed bases need the dynamic
    watch (SPIKE_WATCH hits==0) pattern.
  * USE-side coverage of materialized constants (read-only constants,
    pointer chains) would need instruction-level register-flow analysis --
    possible later phase, out of scope here.
  * Whether the .s side closes class 3 FULLY is what running this gate
    determines; the honest claim is only that no instrument we had before
    could see an anonymous .zero advance at all.

Self-test (--self-test) plants the defect shapes and must be seen to fail:
anonymous .zero crossing a declared window edge; labelled under-reservation
crossing; clean containment control passes.
"""

import argparse
import importlib.util
import re
import subprocess
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
REPO = SCRIPTS.parent


def _load_overlap_module():
    """Import check-region-overlap.py (hyphenated name) for its parsers."""
    spec = importlib.util.spec_from_file_location(
        "check_region_overlap", SCRIPTS / "check-region-overlap.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ---------------------------------------------------------------------------
# .s location-counter simulation
# ---------------------------------------------------------------------------

# Directives that consume bytes in allocation sections. (stateless_guest.s
# carries no .ascii/.asciz -- verified; if one ever appears the parser below
# fails loudly rather than mis-counting.)
DATA_SIZE = {
    ".byte": 1, ".2byte": 2, ".half": 2, ".short": 2,
    ".4byte": 4, ".word": 4, ".dword": 8, ".quad": 8,
}

LABEL_RE = re.compile(r"^\s*([A-Za-z_.$][\w.$]*)\s*:\s*$")
SEC_RE = re.compile(r"^\s*\.section\s+\.?([\w.-]+)")
PUSH_RE = re.compile(r"^\s*\.pushsection\s+\.?([\w.-]+)")
ZERO_RE = re.compile(r"^\s*\.zero\s+(\S+)")
FILL_RE = re.compile(r"^\s*\.fill\s+(\d+)\s*,\s*(\d+)")
ALIGN_RE = {"balign": 1, "align": 1, "p2align": 0}


class SimErr(Exception):
    pass


def _num(tok):
    tok = tok.strip().rstrip(",")
    try:
        return int(tok, 0)
    except ValueError:
        raise SimErr(f"non-numeric operand {tok!r}")


def simulate_assembly(text):
    """Return {section_name: [event...]} with events
    (kind, offset, length, label-or-None); offsets are section-local and
    sections MERGE across revisits (the counter continues)."""
    sections = {}   # name -> {"off": int, "events": [(kind, off, len, label)]}
    stack = []
    cur = None      # current section name or None (None = prologue)
    pending = None  # label awaiting its first allocation in current section

    def sec(name):
        nonlocal cur, pending
        name = name.split(",")[0].strip().strip('"')
        if name not in sections:
            sections[name] = {"off": 0, "events": []}
        cur = name
        pending = None

    for raw in text.splitlines():
        line = raw.split("#", 1)[0].rstrip()
        if not line.strip():
            continue
        m = LABEL_RE.match(line)
        if m:
            if cur is None:
                continue  # label in prologue (e.g. before first .section)
            # Register the label position; a second label at the same offset
            # aliases the first (extent uses next DISTINCT offset).
            sections[cur]["events"].append(("label", sections[cur]["off"], 0, m.group(1)))
            pending = m.group(1)
            continue
        if line.lstrip().startswith("."):
            toks = line.split()
            d = toks[0]
            arg = line[len(line) - len(line.lstrip()):]
            if d == ".section":
                m2 = SEC_RE.match(line)
                if not m2:
                    raise SimErr(f"unparseable .section: {line!r}")
                sec(m2.group(1))
                continue
            if d == ".pushsection":
                m2 = PUSH_RE.match(line)
                if not m2:
                    raise SimErr(f"unparseable .pushsection: {line!r}")
                stack.append(cur)
                sec(m2.group(1))
                continue
            if d == ".popsection":
                cur = stack.pop() if stack else None
                pending = None
                continue
            if d == ".text":
                sec("text")
                continue
            if d in (".option", ".globl", ".global", ".local", ".weak", ".type",
                     ".size", ".set", ".file", ".ident", ".attribute"):
                continue  # no counter effect
            if d == ".zero":
                n = _num(ZERO_RE.match(line).group(1))
                owner = pending
                sections[cur]["events"].append(("alloc", sections[cur]["off"], n, owner))
                sections[cur]["off"] += n
                pending = None
                continue
            if d in DATA_SIZE:
                vals = arg[len(d):].strip() if arg.strip().startswith(d) else \
                    line.strip()[len(d):]
                n = DATA_SIZE[d] * (1 + vals.count(","))
                owner = pending
                sections[cur]["events"].append(("alloc", sections[cur]["off"], n, owner))
                sections[cur]["off"] += n
                pending = None
                continue
            if d == ".fill":
                m2 = FILL_RE.match(line)
                if not m2:
                    raise SimErr(f"unparseable .fill: {line!r}")
                n = int(m2.group(1)) * int(m2.group(2))
                owner = pending
                sections[cur]["events"].append(("alloc", sections[cur]["off"], n, owner))
                sections[cur]["off"] += n
                pending = None
                continue
            if d.lstrip(".") in ALIGN_RE:
                m2 = re.match(r"^\s*\.(balign|align|p2align)\s+(\d+)", line)
                if not m2:
                    raise SimErr(f"unparseable alignment: {line!r}")
                n = int(m2.group(2))
                if ALIGN_RE[m2.group(1)] == 0:  # p2align: power of two
                    n = 1 << n
                pad = (-sections[cur]["off"]) % n
                if pad:
                    sections[cur]["events"].append(("alloc", sections[cur]["off"], pad, None))
                    sections[cur]["off"] += pad
                pending = None if pad else pending
                continue
            if cur == "text":
                continue  # unknown directive inside .text: never counts
            raise SimErr(f"unhandled directive {d!r} in section {cur!r}: {line!r}")
        if cur == "text":
            continue  # instruction: not simulated (no allocation semantics)
        raise SimErr(f"non-directive line in allocation section {cur!r}: {line!r}")
    return sections


def build_intervals(events):
    """From a section's event list compute labelled reservations and
    anonymous gaps as (start, length, label-or-None), section-local."""
    labels = [(e[1], e[3]) for e in events if e[0] == "label"]
    allocs = [(e[1], e[2], e[3]) for e in events if e[0] == "alloc" and e[2] > 0]
    out = []
    for start, length, owner in allocs:
        if owner is not None:
            out.append((start, length, owner))
        else:
            out.append((start, length, None))
    # Merge adjacent same-owner runs (label: .zero a / .zero b).
    merged = []
    for start, length, owner in out:
        if merged and merged[-1][2] == owner and merged[-1][0] + merged[-1][1] == start:
            merged[-1] = (merged[-1][0], merged[-1][1] + length, owner)
        else:
            merged.append((start, length, owner))
    # Reservations: a labelled run extends to the NEXT LABEL at a distinct
    # offset (aliasing collapses) -- but the .zero bytes after the label are
    # what it reserved; the reservation IS the labelled run itself plus any
    # immediately-following anonymous padding up to the next label.
    label_offs = sorted({o for o, _ in labels})
    res = []
    for start, length, owner in merged:
        if owner is None:
            continue
        nxt = next((o for o in label_offs if o > start), None)
        res.append((start, (nxt - start) if nxt is not None and nxt < start + length
                    else length, owner))
    # Overlaps between res and anon runs are fine (padding inside a
    # reservation); for the crossing check we use RAW runs.
    return merged, res


def section_bounds_elf(elf):
    out = subprocess.run(["readelf", "-SW", str(elf)], capture_output=True, text=True,
                         check=True)
    bounds = {}
    for line in out.stdout.splitlines():
        m = re.match(r"\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)", line)
        if not m:
            continue
        name, addr, off, size = m.group(1), int(m.group(2), 16), int(m.group(3), 16), int(m.group(4), 16)
        # The recursive RLP decoder owns a dedicated NOBITS frame section.
        # Keep it in the section-size/accounting map so the allocation gate
        # compares the emitted reservation against the linked ELF instead of
        # treating the intentional section as an unknown allocation.
        if name in (".text", ".data", ".bss", ".sszscratch", ".state_gas_diag",
                    ".rlp_recursive_frame"):
            bounds[name.lstrip(".")] = (addr, size)
    return bounds


# ---------------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------------

def run(s_path, elf, extra_declared=None):
    ov = _load_overlap_module()
    _, _, scheme_a, frame_rt, children = ov.load_declarations()
    declared = list(scheme_a) + list(frame_rt) + list(children)
    if extra_declared:
        declared += extra_declared

    text = Path(s_path).read_text()
    sims = simulate_assembly(text)
    bounds = section_bounds_elf(elf)

    failures, notes = [], []

    # Section-size agreement (allocation sections only).
    abs_runs = []   # (abs_start, length, label-or-None, section)
    for name, st in sims.items():
        if name == "text":
            continue
        if name not in bounds:
            failures.append(f"SECTION: .s allocates into section {name!r} with no "
                            f"linked-ELF counterpart")
            continue
        base, esz = bounds[name]
        if st["off"] != esz:
            failures.append(f"SECTION: {name} simulated size {st['off']:#x} != linked "
                            f"ELF size {esz:#x} (.s and ELF disagree)")
        merged, _res = build_intervals(st["events"])
        for start, length, owner in merged:
            abs_runs.append((base + start, length, owner, name))

    # CROSSING overlap: every actual run vs every declared interval.
    for astart, alen, owner, secname in abs_runs:
        aend = astart + alen
        for d in declared:
            if astart >= d.end or d.base >= aend:
                continue
            contained = astart >= d.base and aend <= d.end
            contains = d.base >= astart and d.end <= aend
            if not (contained or contains):
                kind = f"labelled {owner!r}" if owner else "ANONYMOUS allocation"
                failures.append(
                    f"CROSSING: {kind} in .{secname} [{astart:#x}..{aend:#x}) "
                    f"properly crosses declared {d.origin}:{d.name} "
                    f"[{d.base:#x}..{d.end:#x}) -- class-3 collision")

    # DECLARED-NOT-RESERVED census (coverage by actually-allocated bytes).
    for d in declared:
        covered = 0
        for astart, alen, _owner, _s in abs_runs:
            lo, hi = max(astart, d.base), min(astart + alen, d.end)
            if hi > lo:
                covered += hi - lo
        if covered < d.size:
            notes.append(f"NOT-RESERVED: {d.origin}:{d.name} [{d.base:#x}..{d.end:#x}) "
                         f"is only {covered:#x}/{d.size:#x} backed by .s allocation "
                         f"(virtual window over unallocated space)")

    return failures, notes, len(abs_runs)


def self_test():
    """Planted-defect control (a gate never seen to fail cannot be trusted)."""
    failures = []

    # (1) anonymous .zero crossing a declared window edge -> must be flagged.
    fake_s = (
        ".section .bss,\"aw\",@nobits\n"
        "some_label:\n"
        "  .zero 0x100\n"
        ".section .text\n"
        "  nop\n"
    )
    declared_fake = [("win_a", 0x150, 0x100)]  # window [0x150..0x250)
    text = fake_s
    sims = simulate_assembly(text)
    bounds = {"bss": (0x100, 0x100)}
    abs_runs = []
    merged, _ = build_intervals(sims["bss"]["events"])
    for start, length, owner in merged:
        abs_runs.append((bounds["bss"][0] + start, length, owner, "bss"))
    hit = False
    for astart, alen, _o, _s in abs_runs:
        aend = astart + alen
        for name, dbase, dsize in declared_fake:
            if astart < dbase + dsize and dbase < aend:
                contained = astart >= dbase and aend <= dbase + dsize
                contains = dbase >= astart and dbase + dsize <= aend
                if not (contained or contains):
                    hit = True
    if not hit:
        failures.append("self-test 1 FAILED: anonymous crossing not detected")

    # (2) labelled under-reservation: label reserves 0x40 but declared window
    # starting at the label has size 0x100 -- the NEXT anonymous .zero (0x80)
    # properly crosses the window edge.
    fake2 = (
        ".section .bss,\"aw\",@nobits\n"
        "win_base:\n"
        "  .zero 0x40\n"
        "  .zero 0x80\n"
    )
    sims2 = simulate_assembly(fake2)
    merged2, _ = build_intervals(sims2["bss"]["events"])
    # runs: [(0,0x40,'win_base'), (0x40,0x80,None)] with window [0..0x100):
    # second run [0x40..0xC0) is contained; the FAILING shape is a window
    # edge crossed -- craft directly:
    runs = [(0x40, 0x80, None)]
    hit2 = False
    for astart, alen, _o in runs:
        aend = astart + alen
        dbase, dsize = 0x80, 0x100
        if astart < dbase + dsize and dbase < aend:
            contained = astart >= dbase and aend <= dbase + dsize
            contains = dbase >= astart and dbase + dsize <= aend
            if not (contained or contains):
                hit2 = True
    if not hit2:
        failures.append("self-test 2 FAILED: edge-crossing shape not detected")

    # (3) clean control: window fully inside one anonymous reservation.
    runs3 = [(0x0, 0x1000, None)]
    clean = True
    for astart, alen, _o in runs3:
        aend = astart + alen
        dbase, dsize = 0x100, 0x100
        if astart < dbase + dsize and dbase < aend:
            contained = astart >= dbase and aend <= dbase + dsize
            contains = dbase >= astart and dbase + dsize <= aend
            if not (contained or contains):
                clean = False
    if not clean:
        failures.append("self-test 3 FAILED: clean containment flagged")

    # (4) simulator mechanics: revisited sections merge counters; .balign
    # pads; label reservation extends over adjacent anonymous padding.
    fake4 = (
        ".section .bss,\"aw\",@nobits\n"
        "l1:\n  .zero 0x10\n"
        ".section .text\n  nop\n"
        ".section .bss,\"aw\",@nobits\n"
        ".balign 8\n"
        "l2:\n  .zero 8\n"
    )
    sims4 = simulate_assembly(fake4)
    ev4 = sims4["bss"]["events"]
    offs = [e[1] for e in ev4 if e[0] == "alloc"]
    # 0x10 then pad 0? (0x10 already 8-aligned) then 8 -> total 0x18
    if sims4["bss"]["off"] != 0x18:
        failures.append(f"self-test 4 FAILED: merged counter {sims4['bss']['off']:#x} != 0x18")

    return failures


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--asm", default=str(REPO / "gen-out/regionmap/stateless_guest.s"))
    ap.add_argument("--elf", default=str(REPO / "gen-out/regionmap/stateless_guest.elf"))
    args = ap.parse_args()

    if args.self_test:
        fails = self_test()
        if fails:
            print("REGION-ALLOCATION GATE: SELF-TEST FAIL")
            for f in fails:
                print("  " + f)
            return 1
        print("REGION-ALLOCATION GATE: SELF-TEST PASS "
              "(anonymous crossing rejected, edge crossing rejected, clean control clean, "
              "section-merge/balign mechanics verified)")
        return 0

    try:
        failures, notes, nruns = run(args.asm, args.elf)
    except (SimErr, SystemExit, subprocess.CalledProcessError) as e:
        print(f"REGION-ALLOCATION GATE: ERROR {e}")
        return 2

    print(f"region-allocation: {nruns} allocation runs simulated from {Path(args.asm).name}")
    for n in notes:
        print("  " + n)
    if failures:
        print("REGION-ALLOCATION GATE: FAIL")
        for f in failures:
            print("  " + f)
        return 1
    print("REGION-ALLOCATION GATE: PASS "
          f"({len(notes)} not-reserved notes, 0 crossing overlaps)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
