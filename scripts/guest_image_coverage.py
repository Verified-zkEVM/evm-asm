#!/usr/bin/env python3
"""guest_image_coverage.py — coverage accounting for the guest-image CodeReq
(bead evm-asm-4ch8f.63).

Compares the `.text` extent of every `stateless_guest` symbol
(scripts/asm-fixtures/symbol-addresses.tsv, the .9.3 linker-facts table)
against the wave-.9 conversion manifest (scripts/asm-fixtures/MANIFEST.tsv)
and the kernel-pinned `#guard <name>_prog.length = N` facts in the converted
Lean files, and reports which byte ranges of
[0x80000000, 0x80000000 + textSizeBytes) are covered by a converted
`_prog` (i.e. contribute to `guestImageCodeReq`) and which are NOT.

Usage:
  python3 scripts/guest_image_coverage.py            # human summary
  python3 scripts/guest_image_coverage.py --gaps     # gap list only (tsv)
  python3 scripts/guest_image_coverage.py --md       # markdown tables
"""

import argparse
import os
import re
import sys
from collections import defaultdict

from asm_to_program import layout_leaf_path

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TSV = os.path.join(ROOT, "scripts/asm-fixtures/symbol-addresses.tsv")
MANIFEST = os.path.join(ROOT, "scripts/asm-fixtures/MANIFEST.tsv")
REGIONMAP = os.path.join(ROOT, "EvmAsm/Codegen/RegionMap.lean")

TEXT_BASE = 0x80000000


def lean_camel(entry: str) -> str:
    """symbol label -> Lean camelCase stem (mirrors asm_to_program.py lean_camel)."""
    parts = entry.split("_")
    return parts[0] + "".join(p.capitalize() for p in parts[1:])


def read_text_size() -> int:
    src = open(REGIONMAP).read()
    m = re.search(r"def textSizeBytes : Nat := (0x[0-9a-fA-F]+)", src)
    if not m:
        sys.exit("textSizeBytes not found in RegionMap.lean")
    return int(m.group(1), 16)


def read_text_symbols():
    """All stateless_guest .text symbols (excluding the section symbol),
    sorted by address. Returns [(addr, name)]."""
    syms = []
    for ln in open(TSV):
        if ln.startswith("#"):
            continue
        f = ln.rstrip("\n").split("\t")
        if len(f) < 5 or f[0] != "stateless_guest" or f[3] != ".text":
            continue
        if f[1] == ".text":
            continue
        syms.append((int(f[2], 16), f[1]))
    syms.sort()
    return syms


def read_manifest():
    """FunctionName -> lean file (repo-relative)."""
    out = {}
    for ln in open(MANIFEST):
        if ln.startswith("#") or not ln.strip():
            continue
        func, path = ln.rstrip("\n").split("\t")
        out[func] = path
    return out


def with_layout_leaves(files):
    """Expand manifest paths with their GH-#10753 layout leaves
    (`<Name>Prog.lean` next to `<Name>.lean`), where converted modules keep
    their Function defs and `#guard` length pins.  Same existence rule as
    asm_to_program.check_file's layout detection, via the shared helper."""
    out = set(files)
    for p in files:
        leaf = layout_leaf_path(p, ROOT)
        if leaf:
            out.add(leaf)
    return out


_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")


def read_prog_lengths(files):
    """prog def name -> instruction count, from the kernel-checked
    `#guard <prog>.length = N` pins in the manifest's Lean files.

    GH #10753 leaf awareness: a converted bridge module keeps the pins in
    its leaf `<Name>Prog.lean`, in the layout-independent applied form
    `#guard (<prog>_of .zero).length = N`; those are normalised to the
    bridge's concrete `<prog>` def name (strip the `_of` application)."""
    lens = {}
    pat = re.compile(
        r"#guard\s+(?:\((\w+)_of\s+\.zero\)|(\w+))\.length\s*=\s*(\d+)")
    for path in sorted(set(files)):
        for m in pat.finditer(open(os.path.join(ROOT, path)).read()):
            lens[m.group(1) or m.group(2)] = int(m.group(3))
    return lens


def read_function_bindings(files):
    """FunctionName -> (entry_label, prog_name), parsed from the generated
    `def <func> : String := "<entry>:\\n" ++ emitProgram(R) <prog>` defs.

    GH #10753 leaf awareness: the applied form
    `emitProgramR (<prog>_of .zero)` in a leaf is normalised to the
    bridge's concrete `<prog>` def name."""
    out = {}
    pat = re.compile(
        r'def\s+(\w+Function)\s*:\s*String\s*:=\s*\n?\s*"([\w.]+):\\n"\s*\+\+\s*'
        r"emitProgramR?\s+(?:\((\w+)_of\s+\.zero\)|(\w+))")
    for path in sorted(set(files)):
        for m in pat.finditer(open(os.path.join(ROOT, path)).read()):
            out[m.group(1)] = (m.group(2), m.group(3) or m.group(4))
    return out


ENTRIES_LEAN = "EvmAsm/Codegen/Proofs/GuestImageEntries.lean"


def emit_entries_lean(linked, files):
    """Write the GENERATED (address-by-name, Program) entries module.
    `linked`: [(entry_symbol, prog_name, addr)] sorted by addr."""
    mods = sorted({p[:-len(".lean")].replace("/", ".") for p in files})
    L = ["/-", "  EvmAsm.Codegen.Proofs.GuestImageEntries", "",
         "  GENERATED — do not edit by hand.",
         "  `python3 scripts/guest_image_coverage.py --emit-lean` regenerates",
         "  this from scripts/asm-fixtures/MANIFEST.tsv +",
         "  scripts/asm-fixtures/symbol-addresses.tsv (bead evm-asm-4ch8f.63).",
         "",
         "  One row per converted `_prog` that is LINKED into the",
         "  `stateless_guest` image: (entry address BY NAME via `GuestAddrs`,",
         "  the verification-view `Program`), sorted by entry address.",
         "  Conversions whose entry symbol is absent from the linker-facts",
         "  table (converted but not linked) are excluded — the image",
         "  `CodeReq` must reflect the emitted ELF, nothing more.",
         "  Consumer: `guestImageCodeReq` (EvmAsm/Codegen/Proofs/GuestImage.lean).",
         "-/", "import EvmAsm.Codegen.GuestAddrs"]
    L += [f"import {m}" for m in mods]
    L += ["", "namespace EvmAsm.Codegen", "",
          "open EvmAsm.Rv64 in",
          "/-- The linked converted functions of the guest image, ascending by",
          "    entry address: `(GuestAddrs.<entry>, <entry>_prog)`. -/",
          "def guestImageEntries : List (Nat × Program) := ["]
    rows = [f"  (GuestAddrs.{e}, {p})" for e, p, _ in linked]
    L.append(",\n".join(rows) + " ]")
    L += ["", f"#guard guestImageEntries.length = {len(linked)}", "",
          "end EvmAsm.Codegen", ""]
    with open(os.path.join(ROOT, ENTRIES_LEAN), "w") as f:
        f.write("\n".join(L))
    print(f"wrote {ENTRIES_LEAN} ({len(linked)} entries, {len(mods)} imports)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gaps", action="store_true", help="tsv gap list only")
    ap.add_argument("--md", action="store_true", help="markdown output")
    ap.add_argument("--emit-lean", action="store_true",
                    help=f"regenerate {ENTRIES_LEAN}")
    args = ap.parse_args()

    text_size = read_text_size()
    text_end = TEXT_BASE + text_size
    syms = read_text_symbols()
    manifest = read_manifest()
    src_files = with_layout_leaves(manifest.values())
    prog_lens = read_prog_lengths(src_files)

    bindings = read_function_bindings(src_files)

    # Anti-mis-parser asserts (GH #10753): the parse must be EXACT — every
    # manifest row bound, every bound program a plain identifier.  (Files
    # legitimately define extra non-manifest Functions — callExtraGas,
    # eip8037TxStateGas, rlpItemSize, rlpItemSpan — so the check is the
    # manifest SUBSET, not total count equality.)  A stale
    # GuestImageEntries that still compiles is worse than a loud exit, so
    # fail here rather than emit a silently wrong table.
    n_bound = sum(1 for f in manifest if f in bindings)
    if n_bound != len(manifest):
        missing = sorted(set(manifest) - set(bindings))[:5]
        sys.exit(f"only {n_bound}/{len(manifest)} manifest rows have a "
                 f"parsed Function binding (missing e.g. {missing}) — "
                 "refusing to emit (possible mis-parse)")

    # entry symbol -> (prog def name, prog byte length, lean file)
    converted = {}
    for func, path in manifest.items():
        if func not in bindings:
            sys.exit(f"could not parse Function def for {func} in {path}")
        entry, prog = bindings[func]
        if not _IDENT.fullmatch(prog):
            sys.exit(f"parsed program name {prog!r} for {func} is not a "
                     "plain identifier — refusing to emit (possible "
                     "mis-parse)")
        if prog not in prog_lens:
            sys.exit(f"no `#guard {prog}.length = N` pin found "
                     f"(manifest entry {func} in {path})")
        converted[entry] = (prog, 4 * prog_lens[prog], path)

    if args.emit_lean:
        addr_of = dict((n, a) for a, n in syms)
        linked = sorted(
            ((e, prog, addr_of[e]) for e, (prog, _, _) in converted.items()
             if e in addr_of),
            key=lambda t: t[2])
        emit_entries_lean(linked,
                          [converted[e][2] for e, _, _ in linked])
        return

    rows = []          # (addr, extent_end, name, status, covered_end)
    gaps = []          # (start, end, owner_symbol, kind)
    covered_bytes = 0

    for i, (addr, name) in enumerate(syms):
        ext_end = syms[i + 1][0] if i + 1 < len(syms) else text_end
        if name in converted:
            _, prog_bytes, _ = converted[name]
            cov_end = min(addr + prog_bytes, ext_end)
            covered_bytes += cov_end - addr
            status = "CONVERTED"
            if cov_end < ext_end:
                gaps.append((cov_end, ext_end, name, "TAIL"))
            if addr + prog_bytes > ext_end:
                status = "OVERRUN"  # prog longer than linker extent: drift!
        else:
            cov_end = addr
            status = "UNCONVERTED"
            gaps.append((addr, ext_end, name, "UNCONVERTED"))
        rows.append((addr, ext_end, name, status, cov_end))

    # leading gap before the first symbol (shouldn't exist: _start = base)
    if syms and syms[0][0] > TEXT_BASE:
        gaps.insert(0, (TEXT_BASE, syms[0][0], "<pre-_start>", "HEAD"))

    gaps.sort()
    gap_bytes = sum(e - s for s, e, _, _ in gaps)
    overruns = [r for r in rows if r[3] == "OVERRUN"]

    if args.gaps:
        print("# start\tend\tbytes\tsymbol\tkind")
        for s, e, sym, kind in gaps:
            print(f"0x{s:08x}\t0x{e:08x}\t{e - s}\t{sym}\t{kind}")
        return

    n_conv = sum(1 for r in rows if r[3] in ("CONVERTED", "OVERRUN"))
    n_unconv = sum(1 for r in rows if r[3] == "UNCONVERTED")

    if args.md:
        print(f"`.text` = [0x{TEXT_BASE:08x}, 0x{text_end:08x}), "
              f"{text_size} bytes (`RegionMap.textSizeBytes = 0x{text_size:x}`)\n")
        print(f"- symbols in `.text`: {len(syms)} "
              f"({n_conv} converted, {n_unconv} unconverted)")
        print(f"- covered by converted `_prog`s: {covered_bytes} bytes "
              f"({100 * covered_bytes / text_size:.2f}%)")
        print(f"- NOT covered: {gap_bytes} bytes "
              f"({100 * gap_bytes / text_size:.2f}%), {len(gaps)} ranges\n")
        print("| start | end | bytes | symbol | kind |")
        print("|---|---|---|---|---|")
        for s, e, sym, kind in gaps:
            print(f"| `0x{s:08x}` | `0x{e:08x}` | {e - s} | `{sym}` | {kind} |")
    else:
        print(f".text: [0x{TEXT_BASE:08x}, 0x{text_end:08x})  {text_size} bytes")
        print(f"symbols: {len(syms)}  converted: {n_conv}  "
              f"unconverted: {n_unconv}")
        print(f"covered: {covered_bytes} ({100 * covered_bytes / text_size:.2f}%)  "
              f"gaps: {gap_bytes} ({100 * gap_bytes / text_size:.2f}%) "
              f"in {len(gaps)} ranges")
        for s, e, sym, kind in gaps:
            print(f"  gap 0x{s:08x}..0x{e:08x} ({e - s:6d}B) {kind:11s} {sym}")

    if overruns:
        print("\nOVERRUNS (prog length exceeds linker extent — layout drift!):")
        for addr, ext_end, name, _, _ in overruns:
            print(f"  0x{addr:08x} {name}")
        sys.exit(1)

    # sanity: accounted = covered + gaps must tile .text exactly
    if covered_bytes + gap_bytes != text_size:
        print(f"\nACCOUNTING MISMATCH: covered({covered_bytes}) + "
              f"gaps({gap_bytes}) != text({text_size})", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
