#!/usr/bin/env python3
"""Routine-liveness gate (GH #11303), invoked by scripts/check-routine-liveness.sh.

THE GAP THIS CLOSES: `check-asm-to-program.sh` compares a Program's rendered
string against a saved fixture — a drift guard between two CHECKED-IN
artifacts. A Program, its fixture, and the theorems about them can all go dead
together (nothing references the routine) and every gate stays green: the
theorem keeps proving two dead artifacts agree. The issue's instance,
`bal_canonical_sort_selftest`, has since been wired to a probe caller
(4aa007ef8); the instances this gate found on main the day it was written are
`secf_add_mod_n` (a probe-only PC placeholder, annotated below in the
allowlist) and two Progress/Routines.lean rows whose `symbol` field held a
spec-side pseudo-name instead of the linker symbol the field contract demands
(fixed in the same PR).

WHAT IT CHECKS: for every routine that carries a theorem — the union of
  * conversion entry symbols (scripts/asm-fixtures/MANIFEST.tsv rows, whose
    fixture's first line is `<symbol>:`; each has an `_eq_prog`), and
  * spec'd symbols (`routine "<symbol>"` rows in EvmAsm/Progress/Routines.lean)
— require that it be ALIVE: at least one reference in emitted text, OR
presence in the linked guest's symbol census
(scripts/asm-fixtures/symbol-addresses.tsv). Neither signal alone suffices:
call-site scanning misses routines reached only through the linked ELF's own
internal calls, and the census misses probe-only compositions that are
exercised without being linked into the guest. A symbol with NEITHER signal is
DEAD unless it has an explicit entry in scripts/routine-liveness-allow.txt
with a reason.

WHAT COUNTS AS A REFERENCE (the issue's trap 2: a name is not a contract —
count instructions in emitted strings, never prose or `#guard` mentions):
  * hand-written asm strings:      jal ra|x1|x5|t0, <sym> / call <sym> / j <sym>
  * address taken:                 la <reg>, <sym>
  * converted-Program reloc rows:  .jal .xN "<sym>"  /  .la .xN "<sym>"
  * concrete Program immediates:   jalOff|laHi|laLo GuestAddrs.<sym>
Label definitions (`<sym>:`), splitOn guards (`"<sym>:"`) and docstring
mentions match none of these patterns.

THE ALLOWLIST EXPIRES: an allowlisted symbol that GAINS a liveness signal
fails as STALE, so an inertness claim cannot outlive its reason. This is also
the fix direction for the inverse defect (#11258, a docstring claiming INERT
on live code): inertness claims belong here, where they are checked every run,
not in prose, where they rot.

SELF-TEST (the issue's trap 1: a gate nobody has seen fail is
indistinguishable from one that cannot): `--self-test` drops the canary
`secf_add_mod_n` from the allowlist in memory and asserts the checker reports
it dead — so every CI run re-proves the gate can fire.
"""

import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(REPO, "scripts", "asm-fixtures", "MANIFEST.tsv")
FIXDIR = os.path.join(REPO, "scripts", "asm-fixtures")
TSV = os.path.join(REPO, "scripts", "asm-fixtures", "symbol-addresses.tsv")
ROUTINES = os.path.join(REPO, "EvmAsm", "Progress", "Routines.lean")
ALLOWLIST = os.path.join(REPO, "scripts", "routine-liveness-allow.txt")
CANARY = "secf_add_mod_n"


def guest_symbols() -> set[str]:
    """The linked guest's symbol census (linker facts; includes local labels —
    e.g. `enrg_u32le` is a plain local label and appears)."""
    out = set()
    with open(TSV) as f:
        for line in f:
            if line.startswith("#"):
                continue
            parts = line.split("\t")
            if len(parts) >= 2:
                out.add(parts[1])
    return out


def manifest_symbols() -> set[str]:
    syms = set()
    with open(MANIFEST) as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            fn = line.split("\t")[0].strip()
            fixture = os.path.join(FIXDIR, fn + ".s")
            if not os.path.exists(fixture):
                continue
            with open(fixture) as fx:
                first = fx.readline().strip()
            if first.endswith(":"):
                syms.add(first[:-1])
    return syms


def registry_symbols() -> set[str]:
    if not os.path.exists(ROUTINES):
        return set()
    text = open(ROUTINES).read()
    return set(re.findall(r'routine\s+"([A-Za-z0-9_]+)"', text))


def load_allowlist() -> dict[str, str]:
    allow: dict[str, str] = {}
    if not os.path.exists(ALLOWLIST):
        return allow
    with open(ALLOWLIST) as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            parts = line.split("\t", 1)
            if len(parts) != 2 or not parts[1].strip():
                print(f"check-routine-liveness: MALFORMED allowlist line "
                      f"(need <symbol><TAB><reason>): {line!r}", file=sys.stderr)
                sys.exit(1)
            allow[parts[0].strip()] = parts[1].strip()
    return allow


def lean_sources() -> list[str]:
    out = []
    for root, _dirs, files in os.walk(os.path.join(REPO, "EvmAsm")):
        for f in files:
            if f.endswith(".lean"):
                out.append(os.path.join(root, f))
    return out


# Generic call-site extractors: ONE pass over the tree capturing every call
# target, then intersect with the symbol set. (A per-symbol regex sweep is
# O(symbols x files) and takes tens of minutes; this is seconds.)
CALL_PATTERNS = [
    re.compile(r"\bjal\s+(?:ra|x1|x5|t0),\s*([A-Za-z_][A-Za-z0-9_]*)"),  # hand-written jal
    re.compile(r"\bcall\s+([A-Za-z_][A-Za-z0-9_]*)"),                    # call pseudo
    re.compile(r"[;\"]\s*j\s+([A-Za-z_][A-Za-z0-9_]*)"),                 # tail call
    re.compile(r"\\n\s*j\s+([A-Za-z_][A-Za-z0-9_]*)"),                  # tail call after \n
    re.compile(r"\.jal\s+\.x\d+\s+\"([A-Za-z_][A-Za-z0-9_]*)\""),        # reloc jal row
    re.compile(r"\.la\s+\.x\d+\s+\"([A-Za-z_][A-Za-z0-9_]*)\""),         # reloc la row (address taken)
    re.compile(r"\bla\s+[a-z]\d?\d?,\s*([A-Za-z_][A-Za-z0-9_]*)"),     # hand-written la
    re.compile(r"\b(?:jalOff|laHi|laLo)\s+GuestAddrs\.([A-Za-z_][A-Za-z0-9_]*)"),  # concrete imm
]


def count_call_sites(symbols: set[str]) -> dict[str, int]:
    counts = {s: 0 for s in symbols}
    for path in lean_sources():
        text = open(path, encoding="utf-8", errors="replace").read()
        for pat in CALL_PATTERNS:
            for target in pat.findall(text):
                if target in counts:
                    counts[target] += 1
    return counts


def run(allow: dict[str, str], quiet: bool = False) -> tuple[list[str], list[str]]:
    symbols = manifest_symbols() | registry_symbols()
    counts = count_call_sites(symbols)
    guest = guest_symbols()
    dead, stale = [], []
    for s in sorted(symbols):
        alive = counts[s] > 0 or s in guest
        if s in allow:
            if alive:
                how = (f"{counts[s]} reference(s)" if counts[s] > 0
                       else "present in the guest census")
                stale.append(s)
                if not quiet:
                    print(f"  STALE   {s} — allowlisted as dead but has {how}; "
                          f"delete its entry "
                          f"(reason recorded, no longer true: {allow[s]})")
            elif not quiet:
                print(f"  KNOWN   {s} — {allow[s]}")
        elif not alive:
            dead.append(s)
            if not quiet:
                print(f"  DEAD    {s} — theorem subject with ZERO references "
                      f"(no call, jump, or address-taken site) and absent from "
                      f"the guest symbol census")
    return dead, stale


def main() -> None:
    allow = load_allowlist()

    if "--self-test" in sys.argv:
        if CANARY not in allow:
            print(f"check-routine-liveness --self-test: canary {CANARY} is not "
                  f"in the allowlist; the self-test needs it there to remove")
            sys.exit(1)
        pruned = {k: v for k, v in allow.items() if k != CANARY}
        dead, _ = run(pruned, quiet=True)
        if CANARY in dead:
            print(f"check-routine-liveness --self-test: OK — gate fires on "
                  f"{CANARY} when its annotation is removed")
            sys.exit(0)
        print(f"check-routine-liveness --self-test: FAIL — removed {CANARY}'s "
              f"annotation and the gate did NOT flag it; the checker is broken "
              f"or the canary gained a real caller (then pick a new canary)")
        sys.exit(1)

    dead, stale = run(allow)
    total = len(manifest_symbols() | registry_symbols())
    if dead or stale:
        print(f"check-routine-liveness: FAILED "
              f"({len(dead)} dead, {len(stale)} stale of {total} symbols).")
        print("  DEAD  — a routine with a theorem about it has no call site in any")
        print("          emitted composition. Either wire a caller, or record the")
        print("          reason in scripts/routine-liveness-allow.txt")
        print("          (<symbol><TAB><reason>).")
        print("  STALE — an allowlisted routine gained a caller; delete its entry")
        print("          so the exemption does not outlive its reason.")
        sys.exit(1)
    known = sum(1 for s in allow)
    print(f"check-routine-liveness: OK — {total} theorem-bearing routines, "
          f"{total - known} with live call sites, {known} annotated no-caller.")


if __name__ == "__main__":
    main()
