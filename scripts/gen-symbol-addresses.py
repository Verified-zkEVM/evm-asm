#!/usr/bin/env python3
"""Generate the linker-facts symbol->address table for bead evm-asm-4ch8f.6.

Unblocks wave evm-asm-4ch8f.9.3 (550 functions using `la`/cross-function `jal`):
for each named guest build unit it emits every DEFINED symbol's linked address,
its section, and a STABLE vs LINK_DEPENDENT classification.

  * STABLE           - pinned by codegen constants / linker flags (section
                       bases from -Ttext/-Tdata/--section-start, INPUT/OUTPUT
                       constants, and the Stateless scheme-A working-RAM anchors).
                       These may be hardcoded by downstream `la` consumers.
  * LINK_DEPENDENT   - every emitted symbol (function entries in .text; data
                       arena/label addresses in .data). These MOVE whenever any
                       earlier function or data object changes size, so wave .9.3
                       must resolve them from the ELF at build time, never bake
                       them into Lean.

Usage:
  scripts/gen-symbol-addresses.py [--build] [--elf-dir DIR] [PROG ...]

With no PROG, defaults to `stateless_guest runtime_dispatcher`. With --build,
(re)emits each ELF via `lake exe codegen`; otherwise expects the ELF to already
exist under --elf-dir (default gen-out/regionmap).

Writes scripts/asm-fixtures/symbol-addresses.tsv (checked-in snapshot).
Requires riscv64-unknown-elf toolchain (via `lake exe codegen`) + readelf.
"""
import argparse
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# stateless_guest is the single fully-linked guest ELF. The runtime dispatcher
# and the ~873 *Function routines are spliced INTO it (they are NOT independently
# linkable: `runtime_dispatcher` alone has undefined cross-unit references), so
# every function entry + data arena base the .9.3 wave needs is a symbol here.
DEFAULT_PROGS = ["stateless_guest"]
OUT_TSV = os.path.join(REPO, "scripts", "asm-fixtures", "symbol-addresses.tsv")

# STABLE absolute bases, mirroring EvmAsm/Codegen/RegionMap.lean stableGuestBases.
# (symbol -> address). Keep in sync with RegionMap.schemeAAnchors + section bases.
STABLE_BASES = {
    "INPUT_ADDR":   0x40000000,
    "OUTPUT_ADDR":  0xa0010000,
    ".text":        0x80000000,
    ".data":        0xa3000000,
    ".bss":         0xa4000000,
    ".sszscratch":  0xbf800000,
    "ssz_input_decoded":      0xa0020000,
    "execution_witness_area": 0xa0030000,
    "node_db_buckets":        0xa0130000,
    "code_db_buckets":        0xa0530000,
    "state_tracker_area":     0xa0630000,
    "evm_frame_stack":        0xa0a30000,
    "evm_value_stack":        0xa0a70000,
    "evm_memory_area":        0xa0b70000,
    "keccak_scratch":         0xa1b70000,
    "ecrecover_scratch":      0xa1b80000,
    "sha256_scratch":         0xa1b90000,
}


def which_readelf():
    for c in ("readelf", "riscv64-unknown-elf-readelf", "riscv64-elf-readelf"):
        if subprocess.run(["which", c], capture_output=True).returncode == 0:
            return c
    sys.exit("readelf not found on PATH")


def build_elf(prog, elf_dir):
    prefix = os.path.join(elf_dir, prog)
    subprocess.run(
        ["lake", "exe", "codegen", "--program", prog, "--halt", "linux93", "-o", prefix],
        cwd=REPO, check=True)
    return prefix + ".elf"


def section_of(addr, headers):
    for name, base, size in headers:
        if base <= addr < base + size:
            return name
    return "?"


def read_sections(readelf, elf):
    """Return [(name, base, size)] for allocated sections."""
    out = subprocess.run([readelf, "-SW", elf], capture_output=True, text=True, check=True).stdout
    secs = []
    for line in out.splitlines():
        m = re.search(r"\]\s+(\.\S+)\s+\S+\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)", line)
        if m:
            base = int(m.group(2), 16)
            if base == 0:  # non-alloc (.symtab/.strtab/.shstrtab/.riscv.attributes)
                continue
            secs.append((m.group(1), base, int(m.group(3), 16)))
    return secs


def read_symbols(readelf, elf):
    """Return [(addr, name)] for defined, named data/func/notype symbols."""
    out = subprocess.run([readelf, "-sW", elf], capture_output=True, text=True, check=True).stdout
    syms = []
    for line in out.splitlines():
        f = line.split()
        # Num: Value Size Type Bind Vis Ndx Name
        if len(f) < 8 or not re.match(r"^\d+:$", f[0]):
            continue
        typ, ndx, name = f[3], f[6], f[7]
        if ndx == "UND" or typ in ("SECTION", "FILE") or not name:
            continue
        if name.startswith("$"):  # RISC-V mapping symbols
            continue
        syms.append((int(f[1], 16), name))
    return syms


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("progs", nargs="*", default=None)
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--elf-dir", default=os.path.join(REPO, "gen-out", "regionmap"))
    args = ap.parse_args()
    progs = args.progs if args.progs else DEFAULT_PROGS
    readelf = which_readelf()
    os.makedirs(args.elf_dir, exist_ok=True)

    rows = []
    for prog in progs:
        elf = os.path.join(args.elf_dir, prog + ".elf")
        if args.build or not os.path.exists(elf):
            elf = build_elf(prog, args.elf_dir)
        secs = read_sections(readelf, elf)
        # STABLE section-base rows first (one per unit).
        for name, base, size in secs:
            rows.append((prog, name, base, name, "STABLE"))
        for addr, name in sorted(read_symbols(readelf, elf)):
            sec = section_of(addr, secs)
            stable = "STABLE" if name in STABLE_BASES else "LINK_DEPENDENT"
            rows.append((prog, name, addr, sec, stable))

    with open(OUT_TSV, "w") as fh:
        fh.write("# symbol->address linker-facts table (bead evm-asm-4ch8f.6, wave .9.3)\n")
        fh.write("# Regenerate: scripts/gen-symbol-addresses.py --build\n")
        fh.write("# columns: unit\tsymbol\taddress\tsection\tstability\n")
        fh.write("# STABLE addresses are pinned by codegen/linker flags; LINK_DEPENDENT\n")
        fh.write("# addresses move on any .text/.data size change and MUST be read from the ELF.\n")
        for unit, name, addr, sec, stab in rows:
            fh.write(f"{unit}\t{name}\t0x{addr:08x}\t{sec}\t{stab}\n")
    print(f"wrote {OUT_TSV} ({len(rows)} rows, units: {', '.join(progs)})")


if __name__ == "__main__":
    main()
