#!/usr/bin/env python3
"""Generate EvmAsm/Codegen/RegionMapLinkPins.lean from a linked stateless_guest ELF.

Source of truth at regen time: the ELF passed in (default gen-out/regionmap/stateless_guest.elf).
check-region-map.sh re-reads the ELF built at *check* time independently — pins and
expectation are two readings of two artefacts, never a value compared to itself.

Link-layout-dependent only (class A). Class B stable bases stay hand-typed in RegionMap.
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
DEFAULT_ELF = REPO / "gen-out" / "regionmap" / "stateless_guest.elf"
OUT = REPO / "EvmAsm" / "Codegen" / "RegionMapLinkPins.lean"

SYMBOLS = {
    "callFrameArenaBase": "call_frame_arena",
    "evmMemoryPoolBase": "evm_memory_pool",
    "syslogBase": "bv_system_storage_log",
}


def _find_tool(*names: str) -> str:
    import shutil

    for n in names:
        p = shutil.which(n)
        if p:
            return p
    sys.exit(f"missing required tool (tried {', '.join(names)})")


def readelf_sections(elf: Path) -> dict[str, int]:
    """Section sizes via the same wide-format parse as check-region-map.sh."""
    # Probe all three spellings, matching gen-symbol-addresses.py:82. Homebrew's
    # riscv64-elf-binutils installs `riscv64-elf-readelf`; omitting it made this
    # generator unusable on macOS while its sibling worked (#11043's class).
    readelf = _find_tool("readelf", "riscv64-unknown-elf-readelf",
                         "riscv64-elf-readelf")
    out = subprocess.check_output([readelf, "-SW", str(elf)], text=True)
    sizes: dict[str, int] = {}
    for line in out.splitlines():
        m = re.search(
            r"\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)", line
        )
        if not m:
            continue
        name = m.group(1)
        if name in (".text", ".data", ".bss"):
            sizes[name] = int(m.group(3), 16)
    for req in (".text", ".data", ".bss"):
        if req not in sizes:
            sys.exit(f"section {req} not found in {elf}")
    return sizes


def nm_symbol(elf: Path, name: str) -> int:
    nm = _find_tool("nm", "riscv64-unknown-elf-nm")
    out = subprocess.check_output([nm, str(elf)], text=True)
    for line in out.splitlines():
        parts = line.split()
        if len(parts) >= 3 and parts[-1] == name:
            return int(parts[0], 16)
    sys.exit(f"symbol {name} not found in {elf}")


def render(elf: Path) -> str:
    sec = readelf_sections(elf)
    addrs = {k: nm_symbol(elf, sym) for k, sym in SYMBOLS.items()}
    rel = os.path.relpath(elf, REPO)
    lines = [
        "/-",
        "  EvmAsm.Codegen.RegionMapLinkPins",
        "",
        "  GENERATED — do not edit by hand.",
        "  `python3 scripts/gen-region-map-link-pins.py` regenerates this from the",
        "  linked stateless_guest ELF (issue #11230).",
        "",
        "  Link-layout-dependent pins only (class A): section sizes + three BSS",
        "  bases that move when the guest image moves. Class B stable bases stay",
        "  hand-typed in RegionMap.lean.",
        "",
        f"  Regenerated from: {rel}",
        "  Guard contract (check-region-map.sh): pins are this file (regen-time",
        "  ELF reading); expectation is readelf/nm of the ELF built at *check*",
        "  time. Two independent readings of two artefacts. Catches: image moved",
        "  and nobody regenerated.",
        "-/",
        "",
        "namespace EvmAsm.Codegen.RegionMapLinkPins",
        "",
        # abbrev so decide/omega/simp reduce through without hand-unfold (GuestImage).
        f"abbrev textSizeBytes : Nat := {sec['.text']:#x}",
        f"abbrev dataSizeBytes : Nat := {sec['.data']:#x}",
        f"abbrev bssSizeBytes : Nat := {sec['.bss']:#x}",
        "",
        f"abbrev callFrameArenaBase : Nat := {addrs['callFrameArenaBase']:#x}",
        f"abbrev evmMemoryPoolBase : Nat := {addrs['evmMemoryPoolBase']:#x}",
        f"abbrev syslogBase : Nat := {addrs['syslogBase']:#x}",
        "",
        "end EvmAsm.Codegen.RegionMapLinkPins",
        "",
    ]
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--elf", type=Path, default=DEFAULT_ELF)
    ap.add_argument("--check", action="store_true", help="diff only; exit 1 if stale")
    args = ap.parse_args()
    if not args.elf.is_file():
        sys.exit(f"ELF not found: {args.elf}")
    body = render(args.elf)
    if args.check:
        cur = OUT.read_text() if OUT.is_file() else ""
        if cur != body:
            print(
                f"DRIFT {OUT.relative_to(REPO)}: run "
                f"`python3 scripts/gen-region-map-link-pins.py`",
                file=sys.stderr,
            )
            return 1
        print(f"check-region-map-link-pins: CLEAN ({OUT.relative_to(REPO)})")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body)
    print(f"wrote {OUT.relative_to(REPO)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
