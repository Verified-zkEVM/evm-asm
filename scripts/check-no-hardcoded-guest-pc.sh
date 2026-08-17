#!/usr/bin/env bash
# check-no-hardcoded-guest-pc.sh — linked guest PC literals must use GuestAddrs.*
#
# Wired in .github/workflows/build.yml (GH #12496).
#
# Blind spots this rewrite closes (both were live on main before #12505):
#   1. Glob was `*SAsm*.lean` — missed every Programs/*.lean offender.
#   2. Pattern was hex-only `0x800xxxxx` — the eleven toNat decides were DECIMAL
#      (e.g. 2147502060 = 0x800047ec) and never matched.
#
# Scan: EvmAsm/Codegen/Programs/**/*.lean for integers in the linked guest
# .text window [0x80000000, 0x80100000), hex or decimal.
#
# A literal is a HARDCODED GUEST PC only when it equals some current
# GuestAddrs.* value (linked-image identity). Absolute decimals used as a
# fictitious local base for brOff/jalOff relative encoding in unlinked /
# probe Programs do NOT equal any GuestAddrs entry — they are not linked PCs
# (measured on #12498: 58/58 bare brOff targets absent from ELF + GuestAddrs).
#
# Exemptions (documented; do not grow silently):
#   1. 0x80000000 — relocation-invariance sentinel.
#   2. 0x80052073 — zkVM Keccak custom insn encoding, not a symbol PC.
#   3. `GuestAddrs.<routine> = 0x800…` — one literal anchor per routine
#      (`#guard` or prose that names the symbol beside the hex).
#   4. Shape: jalOff|laHi|laLo GuestAddrs.<sym> <bareFromPc>
#      — linked address is symbolic; second arg is the from-PC reloc needs.
#   5. Shape: brOff|jalOff <bare> <bare> when NEITHER end equals a GuestAddrs
#      value — fictitious local coordinate pair for relative encoding
#      (probe / unlinked Programs; see #12498).
#   6. Files named *OfflineAddrs* — deliberate frozen ghost bases.
#
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

python3 - <<'PY'
import re
import sys
from pathlib import Path

ROOT = Path("EvmAsm/Codegen/Programs")
GA_PATH = Path("EvmAsm/Codegen/GuestAddrs.lean")
LO, HI = 0x80000000, 0x80100000
CUSTOM_INSN = 0x80052073

HEX_RE = re.compile(r"0x800[0-9a-fA-F]{5}\b")
DEC_RE = re.compile(r"(?<![0-9a-zA-Z_])(2147[0-9]{6}|2148[0-9]{6})(?![0-9a-zA-Z_])")
# One literal anchor per routine — #guard or prose naming GuestAddrs beside hex.
ANCHOR_RE = re.compile(
    r"GuestAddrs\.[A-Za-z0-9_]+\s*=\s*0x800[0-9A-Fa-f]{5}\b",
    re.I,
)
HELPER_RE = re.compile(r"\b(jalOff|brOff|laHi|laLo)\b\s+")


def load_guestaddrs() -> set[int]:
    vals: set[int] = set()
    for line in GA_PATH.read_text().splitlines():
        m = re.match(r"def \w+ : Nat := (0x[0-9a-fA-F]+)", line)
        if m:
            vals.add(int(m.group(1), 16))
    vals.discard(0x80000000)
    return vals


def split_two_args(rest: str):
    rest = rest.split("--")[0].rstrip().rstrip(",)")
    tokens: list[str] = []
    i = 0
    s = rest
    while i < len(s) and len(tokens) < 2:
        if s[i].isspace() or s[i] in ",":
            i += 1
            continue
        if s[i] == "(":
            depth = 1
            j = i + 1
            while j < len(s) and depth:
                if s[j] == "(":
                    depth += 1
                elif s[j] == ")":
                    depth -= 1
                j += 1
            tokens.append(s[i:j])
            i = j
            continue
        j = i
        while j < len(s) and not s[j].isspace() and s[j] not in ",)":
            j += 1
        atom = s[i:j]
        k = j
        while k < len(s) and s[k].isspace():
            k += 1
        if k < len(s) and s[k] == "+":
            k += 1
            while k < len(s) and s[k].isspace():
                k += 1
            m = re.match(r"[^\s,)]+", s[k:])
            if m:
                atom = s[i : k + m.end()]
                j = k + m.end()
        tokens.append(atom)
        i = j
    if len(tokens) >= 2:
        return tokens[0], tokens[1]
    if len(tokens) == 1:
        return tokens[0], None
    return None, None


def is_guestaddrs(arg: str | None) -> bool:
    return bool(arg) and "GuestAddrs." in arg


def is_bare_numeric(arg: str | None) -> bool:
    if not arg:
        return False
    a = arg.strip()
    return bool(re.fullmatch(r"0x[0-9a-fA-F]+", a) or re.fullmatch(r"\d+", a))


def parse_num(arg: str) -> int | None:
    a = arg.strip()
    if re.fullmatch(r"0x[0-9a-fA-F]+", a):
        return int(a, 16)
    if re.fullmatch(r"\d+", a):
        return int(a)
    return None


def shape_exempt_spans(line: str, ga_vals: set[int]) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    pos = 0
    while True:
        m = HELPER_RE.search(line, pos)
        if not m:
            break
        name = m.group(1)
        a1, a2 = split_two_args(line[m.end() :])
        region = line[m.end() :]

        def add_arg_span(arg: str | None) -> None:
            if not arg:
                return
            idx = region.find(arg.strip())
            if idx >= 0:
                start = m.end() + idx
                spans.append((start, start + len(arg.strip())))

        # jalOff|laHi|laLo GuestAddrs.* <bareFromPc>
        if name in ("jalOff", "laHi", "laLo") and is_guestaddrs(a1) and is_bare_numeric(a2):
            add_arg_span(a2)
        # brOff|jalOff <bare> <bare> when neither end is a live GuestAddrs PC
        if name in ("brOff", "jalOff") and is_bare_numeric(a1) and is_bare_numeric(a2):
            t, f = parse_num(a1), parse_num(a2)
            if t is not None and f is not None and t not in ga_vals and f not in ga_vals:
                add_arg_span(a1)
                add_arg_span(a2)
        pos = m.start() + 1
    return spans


def in_spans(start: int, end: int, spans: list[tuple[int, int]]) -> bool:
    return any(s <= start and end <= e for s, e in spans)


ga_vals = load_guestaddrs()
hits: list[str] = []

for path in sorted(ROOT.rglob("*.lean")):
    if "OfflineAddrs" in path.name:
        continue
    text = path.read_text(errors="replace")
    for lineno, line in enumerate(text.splitlines(), 1):
        spans = shape_exempt_spans(line, ga_vals)
        for m in HEX_RE.finditer(line):
            lit = m.group(0)
            val = int(lit, 16)
            if val == 0x80000000 or val == CUSTOM_INSN:
                continue
            if ANCHOR_RE.search(line) and re.search(
                rf"GuestAddrs\.[A-Za-z0-9_]+\s*=\s*{re.escape(lit)}\b",
                line,
                re.I,
            ):
                continue
            if not (LO <= val < HI):
                continue
            if in_spans(m.start(), m.end(), spans):
                continue
            if val not in ga_vals:
                continue
            hits.append(f"{path}:{lineno}:{line.rstrip()}")
        for m in DEC_RE.finditer(line):
            lit = m.group(1)
            val = int(lit)
            if val == 0x80000000 or val == CUSTOM_INSN:
                continue
            if not (LO <= val < HI):
                continue
            if in_spans(m.start(), m.end(), spans):
                continue
            if val not in ga_vals:
                continue
            hits.append(f"{path}:{lineno}:{line.rstrip()}")

if hits:
    sys.stderr.write(
        "check-no-hardcoded-guest-pc.sh failed: a literal equals a live\n"
        "GuestAddrs.* value — use the symbol (or GuestAddrs.<r> = 0x… anchor).\n"
        "Bare from-PC as jalOff|laHi|laLo's second arg after GuestAddrs is OK;\n"
        "bare brOff/jalOff pairs that are NOT live GuestAddrs values are OK\n"
        "(fictitious local coords for relative encoding; see #12498).\n\n"
    )
    for h in hits:
        sys.stderr.write(h + "\n")
    sys.stderr.write(f"\n{len(hits)} hit(s).\n")
    sys.exit(1)

print("check-no-hardcoded-guest-pc.sh: no hardcoded linked guest PCs.")
PY
