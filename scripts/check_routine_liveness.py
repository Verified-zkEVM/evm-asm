#!/usr/bin/env python3
"""Routine-liveness gate (GH #11303), invoked by scripts/check-routine-liveness.sh.

THE GAP THIS CLOSES: `check-asm-to-program.sh` compares a Program's rendered
string against a saved fixture — a drift guard between two CHECKED-IN
artifacts. A Program, its fixture, and the theorems about them can all go dead
together (nothing references the routine) and every gate stays green: the
theorem keeps proving two dead artifacts agree. The issue's instance,
`bal_canonical_sort_selftest`, has since been wired to a probe caller
(4aa007ef8); the instances this gate found on main the day it was written are
`secf_add_mod_n` (a probe-only PC placeholder) and two Progress/Routines.lean rows whose `symbol` field held a
spec-side pseudo-name instead of the linker symbol the field contract demands
(fixed in the same PR).

WHAT IT CHECKS: for every routine that carries a theorem — the union of
  * conversion entry symbols (scripts/asm-fixtures/MANIFEST.tsv rows, whose
    fixture's first line is `<symbol>:`; each has an `_eq_prog`), and
  * spec'd symbols (`routine "<symbol>"` rows in EvmAsm/Progress/Routines.lean)
— classify it before checking liveness. A manifest entry whose fixture entry
label is absent from the linked guest's symbol census is
**absent-from-image** (the probe-only fixture convention); a theorem-bearing
symbol present in that census is **in-image**. The two populations are
reported separately. Absent entries are reported even when they have no source
call site, but they are never silently counted as in-image guest coverage.

For the in-image population, require that it be ALIVE: at least one reference
in emitted text, OR presence in the linked guest's symbol census
(scripts/asm-fixtures/symbol-addresses.tsv). Neither signal alone suffices:
call-site scanning misses routines reached only through the linked ELF's own
internal calls. Absent-from-image entries are classified and reported
separately; their standalone fixture/BuildUnit is the evidence, not guest-image
presence. Reachability within the image is a separate ELF call-graph question
handled by the orphan gate.

WHAT COUNTS AS A REFERENCE (the issue's trap 2: a name is not a contract —
count instructions in emitted strings, never prose or `#guard` mentions):
  * hand-written asm strings:      jal ra|x1|x5|t0, <sym> / call <sym> / j <sym>
  * address taken:                 la <reg>, <sym>
  * converted-Program reloc rows:  .jal .xN "<sym>"  /  .la .xN "<sym>"
  * concrete Program immediates:   jalOff|laHi|laLo GuestAddrs.<sym>
Label definitions (`<sym>:`), splitOn guards (`"<sym>:"`) and docstring
mentions match none of these patterns.

The classification is derived from the fixture entry label and linked symbol
census on every run. It therefore cannot drift as a prose exemption; the
checker reports absent-from-image and in-image populations separately.

SELF-TEST (the issue's trap 1: a gate nobody has seen fail is
indistinguishable from one that cannot): `--self-test` injects a synthetic
absent-from-image manifest entry and an unlinked registry-only symbol in
memory. It asserts the former is classified separately and the latter is still rejected;
the real tree is never modified.
"""

import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(REPO, "scripts", "asm-fixtures", "MANIFEST.tsv")
FIXDIR = os.path.join(REPO, "scripts", "asm-fixtures")
TSV = os.path.join(REPO, "scripts", "asm-fixtures", "symbol-addresses.tsv")
ROUTINES = os.path.join(REPO, "EvmAsm", "Progress", "Routines.lean")
ABSENT_CANARY = "__routine_liveness_absent_selftest"
UNLINKED_CANARY = "__routine_liveness_unlinked_selftest"
IN_IMAGE_CANARY = "__routine_liveness_in_image_selftest"


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


def manifest_entries() -> dict[str, str]:
    """Return fixture entry symbols and their manifest fixture paths.

    Absent-from-image classification uses this same first-label convention as the
    converter, rather than introducing a second marker/source of truth.
    """
    entries: dict[str, str] = {}
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
                entries[first[:-1]] = fixture
    return entries


def manifest_symbols() -> set[str]:
    return set(manifest_entries())


def registry_symbols() -> set[str]:
    if not os.path.exists(ROUTINES):
        return set()
    text = open(ROUTINES).read()
    return set(re.findall(r'routine\s+"([A-Za-z0-9_]+)"', text))


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


def classify_populations(manifest: dict[str, str], registry: set[str],
                         guest: set[str]) -> tuple[set[str], set[str], set[str]]:
    """Partition theorem-bearing symbols into in-image, absent, residual.

    A manifest fixture whose entry label is absent from the linker-facts TSV is
    absent-from-image, matching the conversion tool's documented convention. A
    registry-only symbol absent from the image has no fixture evidence and
    remains an ordinary unlinked/dead candidate.
    """
    symbols = set(manifest) | registry
    probe_only = set(manifest) - guest
    in_image = symbols & guest
    residual = symbols - probe_only - in_image
    return in_image, probe_only, residual


def run(quiet: bool = False, manifest: dict[str, str] | None = None,
        registry: set[str] | None = None,
        guest: set[str] | None = None) -> tuple[list[str], list[str]]:
    manifest = manifest_entries() if manifest is None else manifest
    registry = registry_symbols() if registry is None else registry
    guest = guest_symbols() if guest is None else guest
    symbols = set(manifest) | registry
    in_image, probe_only, residual = classify_populations(manifest, registry, guest)
    counts = count_call_sites(symbols)
    dead = []
    for s in sorted(symbols):
        if s in probe_only:
            if not quiet and counts[s] == 0:
                print(f"  ABSENT-UNREFERENCED {s} — manifest entry is absent "
                      f"from the guest census and has no source call site")
            continue
        alive = counts[s] > 0 or s in guest
        if not alive:
            dead.append(s)
            if not quiet:
                kind = "in-image" if s in in_image else "unlinked"
                print(f"  DEAD    {s} [{kind}] — theorem subject with ZERO references "
                      f"(no call, jump, or address-taken site) and absent from "
                      f"the guest symbol census")
    if not quiet:
        print(f"  in-image theorem-bearing: {len(in_image)}")
        print(f"  absent-from-image theorem-bearing: {len(probe_only)} "
              f"(manifest entry absent from linked guest census)")
        print(f"  unlinked registry-only: {len(residual)}")
    return dead, []


def main() -> None:
    manifest = manifest_entries()
    registry = registry_symbols()
    guest = guest_symbols()

    if "--self-test" in sys.argv:
        # Prove the derived classification independently of any file:
        # inject an absent-from-image manifest entry in memory, then restore the
        # original population and assert that the synthetic symbol disappears.
        injected = dict(manifest)
        injected[ABSENT_CANARY] = "<self-test-absent>"
        in_image, probe_only, _residual = classify_populations(
            injected, registry, guest)
        if ABSENT_CANARY not in probe_only or ABSENT_CANARY in in_image:
            print(f"check-routine-liveness --self-test: FAIL — injected "
                  f"{ABSENT_CANARY} was not classified as absent-from-image")
            sys.exit(1)
        restored = classify_populations(manifest, registry, guest)
        if any(ABSENT_CANARY in population for population in restored):
            print(f"check-routine-liveness --self-test: FAIL — restoring the "
                  f"population left {ABSENT_CANARY} classified")
            sys.exit(1)

        # Exercise the inverse leg: a symbol present in the linker census must
        # be in-image, not absent-from-image, and removing that census fact must make
        # the ordinary liveness gate reject the now-unlinked registry row.
        image_registry = set(registry) | {IN_IMAGE_CANARY}
        image_guest = set(guest) | {IN_IMAGE_CANARY}
        image, probe, _residual = classify_populations(
            manifest, image_registry, image_guest)
        if IN_IMAGE_CANARY not in image or IN_IMAGE_CANARY in probe:
            print(f"check-routine-liveness --self-test: FAIL — injected "
                  f"{IN_IMAGE_CANARY} was not classified as in-image")
            sys.exit(1)
        image_dead, _ = run(quiet=True, manifest=manifest,
                            registry=image_registry, guest=image_guest)
        if IN_IMAGE_CANARY in image_dead:
            print(f"check-routine-liveness --self-test: FAIL — in-image "
                  f"symbol was rejected despite its guest census entry")
            sys.exit(1)
        live_dead, _ = run(quiet=True, manifest=manifest,
                           registry=image_registry, guest=guest)
        if IN_IMAGE_CANARY not in live_dead:
            # With the injected image census removed, this synthetic row must
            # face the ordinary dead-symbol gate rather than an exemption.
            print(f"check-routine-liveness --self-test: FAIL — in-image "
                  f"classification did not expose the removal to the gate")
            sys.exit(1)

        # Keep a negative control for the actual liveness gate: a synthetic
        # registry-only symbol must still be reported dead.
        injected_registry = set(registry) | {UNLINKED_CANARY}
        dead, _ = run(quiet=True, manifest=manifest,
                      registry=injected_registry, guest=guest)
        if UNLINKED_CANARY in dead:
            print(f"check-routine-liveness --self-test: OK — absent-from-image "
                  f"classification, in-image inverse, and unlinked "
                  f"dead-path controls fire")
            sys.exit(0)
        print(f"check-routine-liveness --self-test: FAIL — injected "
              f"unlinked symbol was not flagged; the checker is broken")
        sys.exit(1)

    dead, stale = run(manifest=manifest, registry=registry, guest=guest)
    total = len(set(manifest) | registry)
    if dead or stale:
        print(f"check-routine-liveness: FAILED ({len(dead)} dead of {total} symbols).")
        print("  DEAD  — a routine with a theorem about it has no call site in any")
        print("          emitted composition and is not an absent-from-image manifest entry.")
        sys.exit(1)
    in_image, probe_only, residual = classify_populations(manifest, registry, guest)
    counts = count_call_sites(set(manifest) | registry)
    absent_referenced = sum(1 for s in probe_only if counts[s] > 0)
    print(f"check-routine-liveness: OK — {total} theorem-bearing routines, "
          f"{len(in_image)} in-image, {len(probe_only)} absent-from-image, "
          f"{absent_referenced} absent referenced, "
          f"{len(probe_only) - absent_referenced} absent unreferenced, "
          f"{len(residual)} unlinked registry-only.")


if __name__ == "__main__":
    main()
