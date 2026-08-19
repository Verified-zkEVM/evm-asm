#!/usr/bin/env bash
# check-layout-literals.sh — stateless-guest layout addresses must come from
# EvmAsm/Stateless/MemoryLayout.lean, not from scattered literal copies
# (GH #12586).
#
# Wired in .github/workflows/build.yml.
#
# Why this gate exists: a layout address copied as a bare literal (or
# re-materialized arithmetically from bare LUI/ADDI(W)/SLLI immediates) goes
# stale silently — the copy keeps compiling after the canonical constant
# moves. Three false rejects were traced to exactly this:
#   * #12583 — ACCOUNT_WRITES_UNDO_AREA = 0xBE1E2000 (symbolic) vs an
#     open-coded LUI/ADDIW/SLLI sequence evaluating to 0xBE380000.
#   * #12509/#12519 — account_writes base 0xbd562000 (canonical) vs stale
#     0xbdb80000 comment copies and an even older decoder fallback.
#   * #12587 — emitted base 0xBBAAD000 vs guarded STORAGE_WRITES_UNDO_AREA
#     0xBBBCD000.
#
# Sibling of scripts/check-no-hardcoded-guest-pc.sh (same idiom, different
# range): that gate covers linked .text PCs in [0x80000000, 0x80100000) under
# Codegen/Programs; this gate covers the layout data range
# [0xa0000000, 0xc0000000) across ALL of EvmAsm/ — comments included, because
# comment copies are the ones that went stale in #12509/#12519.
#
# DETECTOR 1 — literal occurrence. A hex or decimal literal is flagged only
# when it EQUALS a canonical constant's value (near-miss literals equal no
# constant and are invisible to this detector — see LIMITATIONS in the
# allowlist header). Exemptions:
#   1. MemoryLayout.lean itself (the definition site).
#   2. EvmAsm/Codegen/RegionMap.lean — the second canonical site, explicitly
#      exempted by #12586 (it re-derives the region table from the same
#      constants; flagged there, fix the source instead).
#   3. Anchor form: a line naming the constant beside the hex, e.g. a #guard
#      or doc comment of the shape `MemoryLayout.ACCOUNT_WRITES_AREA =
#      0xbd562000` — one literal anchor per constant is allowed so the
#      encoding/value is auditable in one place. The named constant's value
#      must EQUAL the literal (a comment naming constant A beside constant
#      B's value is a stale comment, not an anchor).
#   4. scripts/layout-literals-allow.txt entries, each with a justification.
#
# DETECTOR 2 — arithmetic reconstruction. A `.LUI reg (N : BitVec 20)` with a
# BARE numeric immediate starts a register-value simulation through the
# contiguous run of `.ADDI(W) reg reg (imm : BitVec 12)` / `.SLLI reg reg
# (s : BitVec 6)` instructions that follows it (order matters: immediates
# added before the shift are scaled, a trailing ADDI after the SLLI is not).
# If the final value lands in the layout range, the sequence materializes a
# layout address without naming it.
# Derived immediates (the #12588 shape,
# `((EvmAsm.Stateless.ACCOUNT_WRITES_UNDO_AREA.toNat >>> 12) >>> 12 :
#   BitVec 20)`) do not match the bare-immediate regex and are the intended
# fix pattern.
#
# DETECTOR 3 — fixture literals (GH #12621). scripts/asm-fixtures/*.s are
# gate-only artifacts whose BYTES are tied to the emitted render by
# check-asm-to-program.sh — but that check compares two copies of the SAME
# value and stays green when both go stale: in #12600 the fixture read
# `li t2, 0xbdb80000` for as long as the bug existed. This detector flags
# ANY hex/decimal literal in a fixture whose value lies in
# [0xa0000000, 0xc0000000) — canonical or not — so a stale copy that equals
# no current constant is still caught (this is deliberately stricter than
# detector 1, which only sees canonical-valued literals). Exemptions, same
# rules as the Lean side: the anchor form (constant NAME and the literal on
# the SAME line, e.g. `li t3, 3149713408  # STORAGE_WRITES_UNDO_AREA`) and
# justified allowlist entries.
#
# `li` is PERMITTED in fixtures: instruction CHOICE is check-asm-to-program's
# byte-identity business (and GAS expands `li` differently from a hand-rolled
# positive-LUI trio, GH #12595). This gate ties VALUES, not encodings — a li
# carrying an in-range value is a literal occurrence like any other.
#
# DETECTOR 4 — fixture arithmetic reconstruction (GH #12621). A `lui` or `li`
# followed by a contiguous run of `addi(w)`/`slli` on the same register that
# lands in the layout range materializes a layout address without naming it.
# This closes the split-reconstruction blind spot (`li 1; slli 19` style).
# Unlike the Lean-side ratchet, which only counts occurrences of a PINNED
# (possibly stale) value, detectors 3+4 flag in-range values regardless of
# whether they match a canonical constant — so an UNTIED-BUT-CORRECT
# reconstruction (the shape that hid five of the six reverted derivations in
# PR #12519) is still caught: it must anchor (a comment on one of the run's
# lines naming the constant with exactly that value) or be justified.
#
# What fixture green does NOT certify (read this before trusting a pass):
#   * reconstruction shapes the simulator does not model — two-register adds
#     building a base across registers, %hi()/%lo() relocs, anything beyond
#     lui/li + addi(w) + slli on ONE register;
#   * near-miss values outside [0xa0000000, 0xc0000000) (e.g. the INPUT-base
#     0x40000000 family) and small immediates added to a base;
#   * the Lean side of any fixture (detectors 1/2 cover EvmAsm/*.lean);
#   * li EXPANSION choice (byte identity is check-asm-to-program's job).
#
# The allowlist is a RATCHET with pinned counts: adding a literal occurrence
# in an allowlisted file fails COUNT, removing one fails STALE. Update the
# pin consciously — that is the ratchet working. NEVER raise a pin to silence
# a STALE or wrong value: that is how #12591 would have been re-opened.
#
# Usage:
#   scripts/check-layout-literals.sh           # exit 1 on any violation
#   scripts/check-layout-literals.sh --report  # always exit 0; print census
#
# Reproduce the raw literal census by hand:
#   git grep -nEi '0xa0020000|0xa0030000|...' origin/main -- 'EvmAsm/**/*.lean'

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

REPORT=0
if [ "${1:-}" = "--report" ]; then
  REPORT=1
fi

REPORT="$REPORT" python3 - <<'PY'
import os
import re
import sys
from pathlib import Path

LAYOUT = Path("EvmAsm/Stateless/MemoryLayout.lean")
DRIVER = Path("EvmAsm/Codegen/Driver.lean")
REGION_MAP = Path("EvmAsm/Codegen/RegionMap.lean")
ALLOW = Path("scripts/layout-literals-allow.txt")
SCAN_ROOT = Path("EvmAsm")
FIXTURE_ROOT = Path("scripts/asm-fixtures")
LO, HI = 0xA0000000, 0xC0000000
REPORT = os.environ.get("REPORT") == "1"

# ---------------------------------------------------------------- canonical

DEF_RE = re.compile(r"(?:def|abbrev)\s+(\w+)\s*:\s*\w+\s*:=\s*(0x[0-9a-fA-F]+)")

val2names: dict[int, list[str]] = {}
for line in LAYOUT.read_text().splitlines():
    m = DEF_RE.match(line)
    if not m:
        continue
    name, val = m.group(1), int(m.group(2), 16)
    if LO <= val < HI:  # layout addresses only; sizes (e.g. SSZ_SCRATCH_SIZE) stay out
        val2names.setdefault(val, []).append(name)

if not val2names:
    sys.stderr.write("check-layout-literals.sh: no canonical constants parsed from "
                     f"{LAYOUT} — did the def syntax change?\n")
    sys.exit(1)

# ---------------------------------------------------------------- allowlist
# Entry: literal|arith <TAB> path <TAB> 0xvalue <TAB> count <TAB> reason
# count pins the number of occurrences of that value in that file.

allow: dict[tuple[str, str, int], list[int]] = {}  # (kind, path, val) -> [pinned, seen]
allow_reasons: dict[tuple[str, str, int], str] = {}
if ALLOW.exists():
    for raw in ALLOW.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 5:
            sys.stderr.write(f"check-layout-literals.sh: malformed allowlist line: {raw}\n")
            sys.exit(1)
        kind, path, hexval, count = parts[0], parts[1], parts[2], parts[3]
        reason = "\t".join(parts[4:])
        key = (kind, path, int(hexval, 16))
        allow[key] = [int(count), 0]
        allow_reasons[key] = reason


def allowlisted(kind: str, path: str, val: int) -> bool:
    key = (kind, path, val)
    if key not in allow:
        return False
    allow[key][1] += 1
    return True


# ---------------------------------------------------------------- anchor

def is_anchor(line: str, lit: str, val: int) -> bool:
    """Line names a canonical constant whose value equals the literal."""
    for name in val2names.get(val, []):
        if re.search(rf"(?<![A-Za-z0-9_]){re.escape(name)}\b", line):
            return True
    return False


# ------------------------------------------------------------- detector 1

hits1: list[str] = []
census1: dict[tuple[str, int], int] = {}  # (path, val) -> occurrences (all, for census)

hex_res = {val: re.compile(rf"0x{val:x}(?![0-9a-f])", re.I) for val in val2names}
dec_res = {val: re.compile(rf"(?<![0-9a-zA-Z_]){val}(?![0-9a-zA-Z_])") for val in val2names}

for path in sorted(SCAN_ROOT.rglob("*.lean")):
    if path == LAYOUT or path == REGION_MAP:
        continue
    text = path.read_text(errors="replace")
    for lineno, line in enumerate(text.splitlines(), 1):
        for val, hre in hex_res.items():
            for m in hre.finditer(line):
                census1[(str(path), val)] = census1.get((str(path), val), 0) + 1
                if is_anchor(line, m.group(0), val):
                    continue
                if allowlisted("literal", str(path), val):
                    continue
                names = "/".join(val2names[val])
                hits1.append(f"{path}:{lineno}: literal equals {names} ({hex(val)})\n"
                             f"    {line.strip()}")
        for val, dre in dec_res.items():
            for m in dre.finditer(line):
                census1[(str(path), val)] = census1.get((str(path), val), 0) + 1
                if is_anchor(line, m.group(0), val):
                    continue
                if allowlisted("literal", str(path), val):
                    continue
                names = "/".join(val2names[val])
                hits1.append(f"{path}:{lineno}: decimal literal equals {names} ({val})\n"
                             f"    {line.strip()}")

# ------------------------------------------------------------- detector 2

LUI_RE = re.compile(
    r"\.LUI\s+(\.\w+)\s+\(\s*(\d+|0x[0-9a-fA-F]+)\s*:\s*BitVec\s+20\s*\)")
ADDI_RE = re.compile(
    r"\.ADDIW?\s+(\.\w+)\s+(\.\w+)\s+\(\s*(-?\d+)\s*:\s*BitVec\s+12\s*\)")
SLLI_RE = re.compile(
    r"\.SLLI\s+(\.\w+)\s+(\.\w+)\s+\(\s*(\d+)\s*:\s*BitVec\s+6\s*\)")

MAX_CHAIN = 6  # LUI plus the contiguous ADDI(W)/SLLI run on the same register

hits2: list[str] = []
census2: dict[tuple[str, int], int] = {}

for path in sorted(SCAN_ROOT.rglob("*.lean")):
    lines = path.read_text(errors="replace").splitlines()
    for i, line in enumerate(lines):
        m = LUI_RE.search(line)
        if not m:
            continue
        reg = m.group(1)
        val = int(m.group(2), 0) << 12
        # Simulate the contiguous ADDI(W)/SLLI run on the same register, in
        # program order. The run ends at the first line that does not adjust
        # the register.
        j = i + 1
        while j < min(i + MAX_CHAIN, len(lines)):
            am = ADDI_RE.search(lines[j])
            if am and am.group(1) == reg and am.group(2) == reg:
                imm = int(am.group(3))
                val += imm - 4096 if imm >= 2048 else imm
                j += 1
                continue
            sm = SLLI_RE.search(lines[j])
            if sm and sm.group(1) == reg and sm.group(2) == reg:
                val <<= int(sm.group(3))
                j += 1
                continue
            break
        if not (LO <= val < HI):
            continue
        census2[(str(path), val)] = census2.get((str(path), val), 0) + 1
        if allowlisted("arith", str(path), val):
            continue
        canonical = "/".join(val2names.get(val, [])) or "no canonical constant"
        hits2.append(f"{path}:{i + 1}: LUI/ADDI(W)/SLLI reconstructs {hex(val)} "
                     f"({canonical})\n    {line.strip()}")

# ------------------------------------------------------------- ssz tie (GH #12593)
# Driver.lean is deliberately import-free IO glue (layering: it must not import
# MemoryLayout), so its ld flag `--section-start=.sszscratch=0x…` is a shell
# string the Lean side cannot derive. The gate itself cross-checks that string
# against the canonical SSZ_SCRATCH_BASE so a region move fails the build here
# instead of silently splitting CallFrameLayout.sszScratchBase from the linker.

name2val = {n: v for v, ns in val2names.items() for n in ns}
ssz_canonical = name2val.get("SSZ_SCRATCH_BASE")
ssz_split: list[str] = []
if ssz_canonical is None:
    ssz_split.append(f"{LAYOUT.name}: SSZ_SCRATCH_BASE def not parsed — "
                     "the ssz tie cannot check the Driver ld flag")
else:
    m = re.search(r"--section-start=\.sszscratch=(0x[0-9a-fA-F]+)",
                  DRIVER.read_text())
    if m is None:
        ssz_split.append(f"{DRIVER.name}: no --section-start=.sszscratch= flag "
                         "found — did the ld invocation change?")
    else:
        ssz_val = int(m.group(1), 16)
        if ssz_val != ssz_canonical:
            ssz_split.append(
                f"SSZ scratch split (GH #12593): {DRIVER.name} links "
                f".sszscratch at {hex(ssz_val)} but MemoryLayout declares "
                f"SSZ_SCRATCH_BASE = {hex(ssz_canonical)}; CallFrameLayout."
                "sszScratchBase derives from the latter. Align the ld flag.")

# ------------------------------------------------------------- detector 3+4
# GH #12621 fixture scanner. See the header for policy (li permitted, VALUES
# tied) and the limits (what a fixture green does not certify).

F_LUI = re.compile(r"^lui\s+(\w+)\s*,\s*(-?(?:0x[0-9a-fA-F]+|\d+))$")
F_LI = re.compile(r"^li\s+(\w+)\s*,\s*(-?(?:0x[0-9a-fA-F]+|\d+))$")
F_ADDI = re.compile(r"^addiw?\s+(\w+)\s*,\s*(\w+)\s*,\s*(-?(?:0x[0-9a-fA-F]+|\d+))$")
F_SLLI = re.compile(r"^slli\s+(\w+)\s*,\s*(\w+)\s*,\s*(\d+)$")
F_HEX = re.compile(r"0x[0-9a-fA-F]+")
F_DEC = re.compile(r"(?<![0-9a-zA-Z_])(\d{8,})(?![0-9a-zA-Z_])")
FIX_MAX_CHAIN = 6  # lui/li plus the contiguous addi(w)/slli run on one register


def _sext(v: int, bits: int) -> int:
    return v - (1 << bits) if v >= (1 << (bits - 1)) else v


def run_is_anchored(span_lines: list[str], val: int) -> bool:
    """Some line spanned by the run names a canonical constant == val."""
    for line in span_lines:
        if is_anchor(line, None, val):
            return True
    return False


hitsF: list[str] = []
censusF: dict[tuple[str, str, int], int] = {}  # (kind, path, val) -> occurrences

fixture_files = sorted(FIXTURE_ROOT.glob("*.s"))
if not fixture_files:
    sys.stderr.write(f"check-layout-literals.sh: no fixtures found under "
                     f"{FIXTURE_ROOT} — did the layout change?\n")
    sys.exit(1)

for path in fixture_files:
    text = path.read_text(errors="replace")
    lines = text.splitlines()

    # Detector 3 — in-range literals, comments included (stale copies in
    # comments are exactly what outlived #12600).
    for lineno, line in enumerate(lines, 1):
        lits: list[int] = []
        for m in F_HEX.finditer(line):
            lits.append(int(m.group(0), 16))
        for m in F_DEC.finditer(line):
            lits.append(int(m.group(1)))
        for val in lits:
            if not (LO <= val < HI):
                continue
            censusF[("fixliteral", str(path), val)] = \
                censusF.get(("fixliteral", str(path), val), 0) + 1
            if is_anchor(line, None, val):
                continue
            if allowlisted("fixliteral", str(path), val):
                continue
            names = "/".join(val2names.get(val, [])) or "no canonical constant"
            hitsF.append(f"{path}:{lineno}: fixture literal {hex(val)} in "
                         f"[{hex(LO)}, {hex(HI)}) ({names})\n    {line.strip()}")

    # Tokenize into instructions (fixtures pack `a; b; c` per line; `#`
    # starts a comment). Runs must be contiguous in this token stream.
    instrs: list[tuple[int, str]] = []  # (lineno, instruction text)
    line_of: dict[int, int] = {}  # token index -> lineno
    for lineno, raw in enumerate(lines, 1):
        body = raw.split("#", 1)[0]
        for tok in body.split(";"):
            t = tok.strip()
            if t:
                line_of[len(instrs)] = lineno
                instrs.append((lineno, t))

    # Detector 4 — lui/li + contiguous addi(w)/slli run on one register.
    for i, (lineno, instr) in enumerate(instrs):
        m = F_LUI.match(instr) or F_LI.match(instr)
        if not m:
            continue
        reg = m.group(1)
        imm = int(m.group(2), 0)
        val = _sext(imm, 20) << 12 if F_LUI.match(instr) else imm
        consumed = 0
        j = i + 1
        while j < min(i + FIX_MAX_CHAIN, len(instrs)):
            am = F_ADDI.match(instrs[j][1])
            if am and am.group(1) == reg and am.group(2) == reg:
                val += _sext(int(am.group(3), 0), 12)
                consumed += 1
                j += 1
                continue
            sm = F_SLLI.match(instrs[j][1])
            if sm and sm.group(1) == reg and sm.group(2) == reg:
                val <<= int(sm.group(3))
                consumed += 1
                j += 1
                continue
            break
        if consumed == 0 or not (LO <= val < HI):
            continue  # a bare li/lui in range is detector 3's case
        censusF[("fixarith", str(path), val)] = \
            censusF.get(("fixarith", str(path), val), 0) + 1
        span_lines = [lines[lineno - 1]] + \
            [lines[instrs[k][0] - 1] for k in range(i + 1, j)]
        if run_is_anchored(span_lines, val):
            continue
        if allowlisted("fixarith", str(path), val):
            continue
        names = "/".join(val2names.get(val, [])) or "no canonical constant"
        hitsF.append(f"{path}:{lineno}: fixture lui/li+addi(w)/slli run "
                     f"reconstructs {hex(val)} ({names})\n"
                     f"    {lines[lineno - 1].strip()}")

# ---------------------------------------------------------------- verdict

stale: list[str] = []
miscount: list[str] = []
pinned_total = 0
for key, (pinned, seen) in sorted(allow.items()):
    pinned_total += pinned
    if seen == 0:
        stale.append(f"{key[1]} {hex(key[2])} ({key[0]}) — no occurrences remain; "
                     f"delete the entry. Reason was: {allow_reasons[key]}")
    elif seen != pinned:
        miscount.append(f"{key[1]} {hex(key[2])} ({key[0]}): pinned {pinned}, "
                        f"found {seen} — update the pin consciously")

fail = bool(hits1 or hits2 or hitsF or stale or miscount or ssz_split)

if REPORT:
    print(f"canonical constants: {sum(len(v) for v in val2names.values())} defs, "
          f"{len(val2names)} distinct values in [{hex(LO)}, {hex(HI)})")
    print(f"\n--- detector 1 census (literal occurrences, incl. exempt/allowlisted) ---")
    for (path, val), n in sorted(census1.items()):
        names = "/".join(val2names[val])
        print(f"{n:4d}  {hex(val)}  {names}  {path}")
    print(f"total literal occurrences: {sum(census1.values())}")
    print(f"\n--- detector 2 census (arithmetic reconstructions in range) ---")
    for (path, val), n in sorted(census2.items()):
        names = "/".join(val2names.get(val, [])) or "(no canonical constant)"
        print(f"{n:4d}  {hex(val)}  {names}  {path}")
    print(f"total arithmetic reconstructions: {sum(census2.values())}")
    print(f"\n--- fixture scanner census (detectors 3+4, GH #12621; "
          f"{len(fixture_files)} fixtures) ---")
    for (kind, path, val), n in sorted(censusF.items()):
        names = "/".join(val2names.get(val, [])) or "(no canonical constant)"
        print(f"{n:4d}  {hex(val)}  {kind}  {names}  {path}")
    print(f"total fixture in-range occurrences: {sum(censusF.values())}")
    print(f"\nallowlist: {len(allow)} entries, {pinned_total} pinned occurrences")
    print(f"unallowlisted hits: {len(hits1) + len(hits2) + len(hitsF)}")
    for h in hits1 + hits2 + hitsF:
        print(f"  {h}")
    for s in stale + miscount:
        print(f"  allowlist: {s}")
    sys.exit(0)

if fail:
    w = sys.stderr.write
    if hits1 or hits2:
        w("check-layout-literals.sh failed: layout addresses materialized without\n"
          "naming the MemoryLayout constant (GH #12586).\n"
          "Fix: reference the constant (for emitted code, derive immediates from\n"
          "it — the #12588 shape with a #guard on the encoding preconditions);\n"
          "or, if this occurrence is genuinely NEW and has no constant, justify\n"
          "it as a new pinned allowlist entry after verifying the value against\n"
          "MemoryLayout. Never raise a pin to silence a STALE or wrong value\n"
          "(that re-opens the #12591/#12600 class): fix the source instead.\n"
          "One literal anchor per constant of the form `Symbol = 0x…` is exempt.\n\n")
        for h in hits1 + hits2:
            w(h + "\n")
    if hitsF:
        w("check-layout-literals.sh failed: fixture layout addresses not tied to\n"
          "a MemoryLayout constant (GH #12621 — the #12600 mechanism: fixture and\n"
          "emitted copies of one stale value both passed the byte-identity gate).\n"
          "Fix, in order of preference:\n"
          "  1. anchor: put the constant NAME on the SAME line as the literal\n"
          "     (e.g. `li t3, 3149713408  # STORAGE_WRITES_UNDO_AREA`). The name\n"
          "     and the value must share one line — a reflow that splits them\n"
          "     fails the gate (that bit PR #12619).\n"
          "  2. for arithmetic runs (lui/li + addi(w)/slli), anchor by naming the\n"
          "     constant in a comment on one of the run's lines.\n"
          "  3. if the occurrence is genuinely NEW and no constant exists (e.g.\n"
          "     RAM bounds that are prose-only), justify it as a new pinned\n"
          "     allowlist entry — verify the value first, and never raise a pin\n"
          "     to silence a STALE or wrong value: fix the source instead.\n\n")
        for h in hitsF:
            w(h + "\n")
    for s in stale:
        w(f"STALE allowlist entry: {s}\n")
    for s in miscount:
        w(f"COUNT allowlist entry: {s}\n")
    for s in ssz_split:
        w(f"{s}\n")
    w(f"\n{len(hits1) + len(hits2) + len(hitsF)} hit(s), {len(stale)} stale, "
      f"{len(miscount)} miscounted, {len(ssz_split)} ssz-split.\n")
    sys.exit(1)

print(f"check-layout-literals.sh: no uncanonical layout literals "
      f"({pinned_total} allowlisted occurrences pinned, "
      f"{sum(censusF.values())} fixture occurrences tied).")
PY
