#!/usr/bin/env python3
"""Fail when MANIFEST and GuestImageEntries disagree (GH #12146).

WHY THIS GATE EXISTS
--------------------
Nothing previously checked that the two registration surfaces agree:

  * scripts/asm-fixtures/MANIFEST.tsv  — conversion manifest (Function → Lean)
  * EvmAsm/Codegen/Proofs/GuestImageEntries.lean — linked (GuestAddrs, Program)
    table consumed by guestImageCodeReq

asm_to_program.py check-all validates MANIFEST rows against source/fixtures and
regenerates GuestAddrs but never parses GuestImageEntries. guest_image_coverage.py
reads MANIFEST + GuestAddrs + symbol-addresses.tsv and can *emit* GuestImageEntries,
but CI does not assert the committed table still matches that emission.

So a routine can sit in one registry and not the other indefinitely with CI green.
Three violations in one night each surfaced far from the cause (#12134 coverage
gap; #12072 GuestAddrs deletions; #12143 self-certifying acceptance).

LEGS
----
1. Every GuestImageEntries row has a MANIFEST-bound Function whose entry symbol
   matches (would have caught #12072 at cause).
2. Every MANIFEST-bound entry that is LINKED (present in symbol-addresses.tsv)
   has a GuestImageEntries row with the same Program name (would have caught
   #12134). Prog-name mismatch on the intersection is also a failure.
3. ⭐ NOT COVERED. "Every registered Program is the def actually consumed by the
   emitting composition" (no parallel String copy — #12143) is not cheaply
   decidable: emission walks Dispatch/unit String concatenations, not a closed
   registry. Landing a false-positive-prone grep would imply coverage the gate
   does not have. This gate does NOT claim leg 3.

Linked-only for leg 2 matches GuestImageEntries generation: conversions whose
entry symbol is absent from the linker-facts table are excluded by design
(guest_image_coverage.py --emit-lean).

NON-VACUITY
-----------
--self-test injects a temporary MANIFEST deletion for a registered linked entry
and asserts exit 1, then restores and asserts exit 0. A gate that has never
failed is indistinguishable from one that cannot (#12142 check-embedded-counts
shape).

Usage:
  python3 scripts/check-manifest-guestimage.py           # check + self-test
  python3 scripts/check-manifest-guestimage.py --check   # check only
  python3 scripts/check-manifest-guestimage.py --self-test
"""
from __future__ import annotations

import os
import re
import shutil
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
MANIFEST = REPO / "scripts/asm-fixtures/MANIFEST.tsv"
ENTRIES = REPO / "EvmAsm/Codegen/Proofs/GuestImageEntries.lean"
SYMBOLS = REPO / "scripts/asm-fixtures/symbol-addresses.tsv"

GIE_ROW = re.compile(r"\(GuestAddrs\.(\w+),\s*(\w+)\)")


def _load_gic():
    sys.path.insert(0, str(REPO / "scripts"))
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "guest_image_coverage", REPO / "scripts/guest_image_coverage.py"
    )
    gic = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(gic)
    return gic


def read_gie() -> dict[str, str]:
    """entry_symbol -> prog_name from committed GuestImageEntries.lean."""
    text = ENTRIES.read_text()
    rows = GIE_ROW.findall(text)
    if not rows:
        sys.exit(f"check-manifest-guestimage: no GuestImageEntries rows in {ENTRIES}")
    out: dict[str, str] = {}
    for e, p in rows:
        if e in out and out[e] != p:
            sys.exit(
                f"check-manifest-guestimage: duplicate GuestAddrs.{e} with "
                f"conflicting progs {out[e]!r} vs {p!r}"
            )
        out[e] = p
    return out


def read_linked_symbols() -> set[str]:
    names: set[str] = set()
    for ln in SYMBOLS.read_text().splitlines():
        if not ln.strip() or ln.startswith("#"):
            continue
        parts = ln.rstrip("\n").split("\t")
        if len(parts) >= 2:
            names.add(parts[1])
    return names


def compute_violations(gic_mod, manifest_path: Path | None = None) -> tuple[list[str], list[str], list[str]]:
    """Return (leg1, leg2, prog_mismatch) violation message lists.

    If manifest_path is set, temporarily point gic.MANIFEST at it (injection).
    """
    saved = None
    if manifest_path is not None:
        saved = gic_mod.MANIFEST
        gic_mod.MANIFEST = str(manifest_path)
    try:
        _syms, _text_end, converted = gic_mod.load_converted()
    finally:
        if saved is not None:
            gic_mod.MANIFEST = saved

    # converted: entry -> (prog_name, prog_bytes, lean_path)
    gie = read_gie()
    linked = read_linked_symbols()

    leg1: list[str] = []
    for e, p in sorted(gie.items()):
        if e not in converted:
            leg1.append(
                f"GuestAddrs.{e} → {p} in GuestImageEntries but no MANIFEST-bound "
                f"Function with that entry (leg 1; #12072 class)"
            )

    leg2: list[str] = []
    mismatch: list[str] = []
    for e, (prog, _nbytes, path) in sorted(converted.items()):
        if e not in linked:
            continue  # unlinked conversion: correctly absent from GIE
        if e not in gie:
            leg2.append(
                f"MANIFEST-bound linked entry {e!r} → {prog} ({path}) missing from "
                f"GuestImageEntries (leg 2; #12134 class)"
            )
        elif gie[e] != prog:
            mismatch.append(
                f"entry {e!r}: GuestImageEntries has {gie[e]!r} but MANIFEST "
                f"binding has {prog!r} ({path})"
            )

    return leg1, leg2, mismatch


def report(leg1: list[str], leg2: list[str], mismatch: list[str]) -> int:
    n = len(leg1) + len(leg2) + len(mismatch)
    if n == 0:
        gie_n = len(read_gie())
        print(
            f"check-manifest-guestimage: OK — GuestImageEntries ({gie_n}) ↔ "
            f"MANIFEST linked bindings agree (legs 1–2). "
            f"Leg 3 (emission consumes registered Program) NOT covered — see script header."
        )
        return 0

    print(
        f"check-manifest-guestimage: FAIL — {n} registration disagreement(s)",
        file=sys.stderr,
    )
    if leg1:
        print(f"\nLeg 1 — GuestImageEntries without MANIFEST binding ({len(leg1)}):", file=sys.stderr)
        for m in leg1:
            print(f"  ✗  {m}", file=sys.stderr)
    if leg2:
        print(
            f"\nLeg 2 — MANIFEST linked without GuestImageEntries ({len(leg2)}):",
            file=sys.stderr,
        )
        for m in leg2:
            print(f"  ✗  {m}", file=sys.stderr)
    if mismatch:
        print(f"\nProg-name mismatch on intersection ({len(mismatch)}):", file=sys.stderr)
        for m in mismatch:
            print(f"  ✗  {m}", file=sys.stderr)
    print(
        """
Nothing previously checked MANIFEST ↔ GuestImageEntries. Symptoms of drift
do not resemble the cause (#12134 coverage gap, #12072 GuestAddrs deletion,
#12143 self-certifying measurement). Fix the registries to agree, then
`python3 scripts/guest_image_coverage.py --emit-lean` if regenerating Entries.
Leg 3 (emit composition consumes the registered Program) is NOT this gate.
""",
        file=sys.stderr,
    )
    return 1


def self_test(gic_mod) -> int:
    """Inject leg-1 and leg-2 faults; each must fail then restore clean (#12142 shape)."""
    gie = read_gie()
    _syms, _te, converted = gic_mod.load_converted()
    linked = read_linked_symbols()
    candidates = sorted(set(gie) & set(converted) & linked)
    if not candidates:
        print("check-manifest-guestimage --self-test: FAIL — no intersection to inject", file=sys.stderr)
        return 1
    victim_entry = candidates[0]
    victim_prog = gie[victim_entry]

    src_files = gic_mod.with_layout_leaves(gic_mod.read_manifest().values())
    bindings = gic_mod.read_function_bindings(src_files)
    victim_func = None
    for func, (entry, _prog) in bindings.items():
        if entry == victim_entry:
            victim_func = func
            break
    if victim_func is None:
        print(
            f"check-manifest-guestimage --self-test: FAIL — no Function for entry "
            f"{victim_entry!r}",
            file=sys.stderr,
        )
        return 1

    # --- Leg 1 inject: delete MANIFEST row; GIE still has entry ---
    manifest_text = MANIFEST.read_text()
    stripped_lines = []
    removed = 0
    for ln in manifest_text.splitlines(keepends=True):
        if ln.startswith("#") or not ln.strip():
            stripped_lines.append(ln)
            continue
        func = ln.split("\t", 1)[0]
        if func == victim_func:
            removed += 1
            continue
        stripped_lines.append(ln)
    if removed != 1:
        print(
            f"check-manifest-guestimage --self-test: FAIL — expected to remove 1 MANIFEST "
            f"row for {victim_func!r}, removed {removed}",
            file=sys.stderr,
        )
        return 1

    td = tempfile.mkdtemp(prefix="manifest-gie-")
    try:
        inj = Path(td) / "MANIFEST.tsv"
        inj.write_text("".join(stripped_lines))
        leg1, leg2, mm = compute_violations(gic_mod, manifest_path=inj)
        if not any(victim_entry in m for m in leg1):
            print(
                f"check-manifest-guestimage --self-test: FAIL — leg-1 inject of "
                f"{victim_func!r} / GuestAddrs.{victim_entry} did not fail "
                f"(leg1={len(leg1)} leg2={len(leg2)} mm={len(mm)})",
                file=sys.stderr,
            )
            return 1
    finally:
        shutil.rmtree(td, ignore_errors=True)

    # --- Leg 2 inject: delete GIE row; MANIFEST still binds linked entry ---
    gie_text = ENTRIES.read_text()
    gie_lines = []
    gie_removed = 0
    for ln in gie_text.splitlines(keepends=True):
        if f"GuestAddrs.{victim_entry}," in ln and victim_prog in ln and gie_removed == 0:
            gie_removed = 1
            continue
        gie_lines.append(ln)
    if gie_removed != 1:
        print(
            f"check-manifest-guestimage --self-test: FAIL — could not strip GIE row "
            f"for {victim_entry!r}",
            file=sys.stderr,
        )
        return 1
    bak = ENTRIES.read_text()
    try:
        ENTRIES.write_text("".join(gie_lines))
        leg1b, leg2b, mmb = compute_violations(gic_mod, manifest_path=None)
        if not any(victim_entry in m for m in leg2b):
            print(
                f"check-manifest-guestimage --self-test: FAIL — leg-2 inject removing "
                f"GuestAddrs.{victim_entry} from GuestImageEntries did not fail "
                f"(leg1={len(leg1b)} leg2={len(leg2b)} mm={len(mmb)})",
                file=sys.stderr,
            )
            return 1
    finally:
        ENTRIES.write_text(bak)

    # Restored tree must be clean.
    leg1r, leg2r, mmr = compute_violations(gic_mod, manifest_path=None)
    if leg1r or leg2r or mmr:
        print(
            f"check-manifest-guestimage --self-test: FAIL — restored tree not clean "
            f"(leg1={len(leg1r)} leg2={len(leg2r)} mm={len(mmr)}). "
            f"Census first; do not silence.",
            file=sys.stderr,
        )
        for m in (leg1r + leg2r + mmr)[:10]:
            print(f"  ✗  {m}", file=sys.stderr)
        return 1

    print(
        f"check-manifest-guestimage --self-test: OK — leg1 delete MANIFEST "
        f"{victim_func!r} fails; leg2 delete GuestAddrs.{victim_entry} GIE row "
        f"fails; restore exits 0."
    )
    return 0


def main(argv: list[str]) -> int:
    os.chdir(REPO)
    gic = _load_gic()
    args = set(argv[1:])
    only_self = "--self-test" in args and "--check" not in args and len(args) == 1
    only_check = "--check" in args
    # Default: self-test then check (non-vacuity every CI run).
    if only_self:
        return self_test(gic)
    if not only_check:
        rc = self_test(gic)
        if rc != 0:
            return rc
    leg1, leg2, mm = compute_violations(gic)
    return report(leg1, leg2, mm)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
