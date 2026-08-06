#!/usr/bin/env python3
"""Fail when a linked, spec-bearing guest routine has NO row in either registry (GH #11637).

WHY THIS GATE EXISTS. Both proof registries already gate row *contents* — a row must
name a witnessed theorem (`gen-axiom-witnesses.py`), a verdict needs a spec
(`verdict_requires_spec`), a witnessed routine must not be `.unproven`
(`crossVerdictOk`). Every one of those quantifies over rows that EXIST. Nothing
gated row *existence*, so a routine could be linked into the guest, carry a
`sorry`-free whole-routine triple, and appear in neither registry — counting toward
nothing. #11342 found one instance; #11348 found another (`bloom_or_into`), and the
sweep behind #11637 found ~103. Proven work no census can see is indistinguishable
from work not done.

WHAT IT CHECKS. Recomputes three sets from source on every run:

  1. linked symbols          -- `def <sym> : Nat := 0x…` in Codegen/GuestAddrs.lean
  2. registered routines     -- Progress/Routines.lean `routine "<sym>"`
                                UNION Progress/Correspondence.lean `routine := "<sym>"`
  3. routine-level specs     -- `theorem <name>{Fn_spec,Flat_spec,_spec_within,_spec}`
                                anywhere under EvmAsm/, mapped to a symbol by
                                camel->snake on the name minus that suffix

A symbol in (1) ∩ (3) but not in (2) must carry an allowlist entry naming a reason.

⚠️ THE MAPPING IS NAME-BASED, and deliberately so: it needs no build and no
elaboration, which is what makes it cheap enough to run every time. The cost is that
a theorem whose name happens to match a symbol while proving something narrower
reads as covered. That is the right failure direction for a *coverage* gate — it can
under-report a gap, never invent one — but it means this gate is a floor on the
backlog, not a census. `EvmAsm/Progress/**` is excluded from the scan so the
registries' own witness abbrevs and docstrings do not count as specs.

THE ALLOWLIST EXPIRES, which is the whole ratchet (same shape as
routine-liveness-allow.txt, GH #11303/#11332). An entry is STALE — and fails the run,
naming the line to delete — once the symbol gains a row, loses its spec, or leaves
the guest image. So the backlog burns down visibly instead of silently, and a NEW
gap fails immediately rather than joining a pile nobody reads.

TIERS are reported because the remedies differ:
  * A -- a flat `cpsTripleWithin` at the guest address (the file names
    `GuestAddrs.<sym>`): registrable as `.proven` today, no new proof work.
  * B -- a structured SAsm `.Spec` only: needs `Fn.retSpecFlat` first, so a
    `.proven` row would overclaim. Do NOT bulk-register these.
"""
from __future__ import annotations

import collections
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
GUEST_ADDRS = REPO / "EvmAsm" / "Codegen" / "GuestAddrs.lean"
ROUTINES = REPO / "EvmAsm" / "Progress" / "Routines.lean"
CORRESPOND = REPO / "EvmAsm" / "Progress" / "Correspondence.lean"
ALLOW = REPO / "scripts" / "registry-coverage-allow.txt"

SPEC_SUFFIXES = ("Fn_spec", "Flat_spec", "_spec_within", "_spec")
SPEC_RE = re.compile(r"^\s*theorem\s+(\w*(?:Fn_spec|Flat_spec|_spec_within|_spec))\b", re.M)


def camel_to_snake(s: str) -> str:
    s = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", s)
    s = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", "_", s)
    return s.lower().strip("_")


def linked_symbols() -> set[str]:
    return set(re.findall(r"^def ([a-z_0-9]+) : Nat := 0x", GUEST_ADDRS.read_text(), re.M))


def registered() -> set[str]:
    return (set(re.findall(r'^  routine "([a-z_0-9]+)"', ROUTINES.read_text(), re.M))
            | set(re.findall(r'routine := "([a-z_0-9]+)"', CORRESPOND.read_text())))


def spec_bearing(symbols: set[str]) -> dict[str, list[tuple[str, str, bool]]]:
    """symbol -> [(theorem, file, cites_guest_addr)]"""
    out: dict[str, list[tuple[str, str, bool]]] = collections.defaultdict(list)
    for f in sorted(REPO.glob("EvmAsm/**/*.lean")):
        rel = f.relative_to(REPO).as_posix()
        if rel.startswith("EvmAsm/Progress/"):
            continue
        try:
            txt = f.read_text()
        except OSError:
            continue
        if "theorem" not in txt:
            continue
        for thm in SPEC_RE.findall(txt):
            base = thm
            for suf in SPEC_SUFFIXES:
                if base.endswith(suf):
                    base = base[: -len(suf)]
                    break
            sym = camel_to_snake(base)
            if sym in symbols:
                out[sym].append((thm, rel, f"GuestAddrs.{sym}" in txt))
    return out


def read_allow() -> dict[str, str]:
    entries: dict[str, str] = {}
    if not ALLOW.is_file():
        return entries
    for line in ALLOW.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        sym, _, reason = line.partition("\t")
        entries[sym.strip()] = reason.strip()
    return entries


def main() -> int:
    symbols = linked_symbols()
    reg = registered()
    specs = spec_bearing(symbols)
    allow = read_allow()

    gaps = {s: v for s, v in specs.items() if s not in reg}
    tier_a = {s: v for s, v in gaps.items()
              if any(cites and thm.endswith(("_spec_within", "Flat_spec"))
                     for thm, _, cites in v)}

    # NEW gaps -- not allowlisted. These fail.
    new = sorted(set(gaps) - set(allow))
    # STALE entries -- allowlisted but no longer a gap. These fail too (the ratchet).
    stale: list[tuple[str, str]] = []
    for sym in sorted(allow):
        if sym not in symbols:
            stale.append((sym, "no longer a linked guest symbol"))
        elif sym in reg:
            stale.append((sym, "now registered -- delete this line"))
        elif sym not in specs:
            stale.append((sym, "no longer has a routine-level spec theorem"))

    print(f"check-registry-coverage: {len(symbols)} linked symbols, {len(reg)} registered, "
          f"{len(specs)} spec-bearing, {len(gaps)} uncovered "
          f"({len(tier_a)} tier-A, {len(gaps) - len(tier_a)} tier-B), "
          f"{len(allow)} allowlisted")

    if new:
        print(f"\ncheck-registry-coverage: FAIL — {len(new)} linked, spec-bearing "
              f"routine(s) have NO row in either registry and no allowlist entry:",
              file=sys.stderr)
        for sym in new:
            thm, rel, cites = specs[sym][0]
            tier = "A" if sym in tier_a else "B"
            print(f"    [{tier}] {sym}\t{thm}\t{rel}", file=sys.stderr)
        print("\n  Add a row to EvmAsm/Progress/Routines.lean (tier A: a flat triple at the\n"
              "  guest address is registrable as `.proven` today) or, if the spec is a\n"
              "  structured SAsm `.Spec` only (tier B), either derive the flat triple with\n"
              "  `Fn.retSpecFlat` first or add an allowlist entry in\n"
              "  scripts/registry-coverage-allow.txt saying why it is not registered yet.\n"
              "  ⚠️ Do NOT grade a structured-only spec `.proven` to silence this — that is\n"
              "  the invisible overclaim #11637 exists to stop.", file=sys.stderr)

    if stale:
        print(f"\ncheck-registry-coverage: FAIL — {len(stale)} STALE allowlist entr(ies) in "
              f"{ALLOW.relative_to(REPO)}:", file=sys.stderr)
        for sym, why in stale:
            print(f"    {sym}\t{why}", file=sys.stderr)
        print("\n  Delete them. The allowlist expires on purpose: an exemption that outlives\n"
              "  its reason is how a backlog goes silent again.", file=sys.stderr)

    if new or stale:
        return 1
    print("check-registry-coverage: OK — every linked, spec-bearing routine is either "
          "registered or allowlisted with a reason.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
