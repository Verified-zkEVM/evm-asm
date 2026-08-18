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
# The allowlist is a RATCHET with pinned counts: adding a literal occurrence
# in an allowlisted file fails COUNT, removing one fails STALE. Update the
# pin consciously — that is the ratchet working.
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

fail = bool(hits1 or hits2 or stale or miscount or ssz_split)

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
    print(f"\nallowlist: {len(allow)} entries, {pinned_total} pinned occurrences")
    print(f"unallowlisted hits: {len(hits1) + len(hits2)}")
    for h in hits1 + hits2:
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
          "or add a justified allowlist entry in scripts/layout-literals-allow.txt.\n"
          "One literal anchor per constant of the form `Symbol = 0x…` is exempt.\n\n")
        for h in hits1 + hits2:
            w(h + "\n")
    for s in stale:
        w(f"STALE allowlist entry: {s}\n")
    for s in miscount:
        w(f"COUNT allowlist entry: {s}\n")
    for s in ssz_split:
        w(f"{s}\n")
    w(f"\n{len(hits1) + len(hits2)} hit(s), {len(stale)} stale, "
      f"{len(miscount)} miscounted, {len(ssz_split)} ssz-split.\n")
    sys.exit(1)

print(f"check-layout-literals.sh: no uncanonical layout literals "
      f"({pinned_total} allowlisted occurrences pinned).")
PY
