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
  python3 scripts/guest_image_coverage.py --write-doc
      # regenerate docs/4ch8f-guest-image-coverage.md from
      # scripts/asm-fixtures/guest-image-coverage-template.md + live numbers
  python3 scripts/guest_image_coverage.py --check-doc
      # CI drift guard: exit 1 if the committed doc differs from --write-doc
      # output (wired via scripts/check-guest-image-coverage.sh)
  python3 scripts/guest_image_coverage.py --check-declared-starts
      # #11280: GuestAddrs declared start vs TSV actual for each converted
      # linked entry; exit 1 on DECLARED_START_MISMATCH / DECLARED_EXTENT_OVERRUN
"""

import argparse
import difflib
import os
import re
import sys
from collections import defaultdict

from asm_to_program import layout_leaf_path

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TSV = os.path.join(ROOT, "scripts/asm-fixtures/symbol-addresses.tsv")
MANIFEST = os.path.join(ROOT, "scripts/asm-fixtures/MANIFEST.tsv")
REGIONMAP = os.path.join(ROOT, "EvmAsm/Codegen/RegionMap.lean")
GUEST_ADDRS = os.path.join(ROOT, "EvmAsm/Codegen/GuestAddrs.lean")
DOC = os.path.join(ROOT, "docs/4ch8f-guest-image-coverage.md")
TEMPLATE = os.path.join(
    ROOT, "scripts/asm-fixtures/guest-image-coverage-template.md")

TEXT_BASE = 0x80000000
_GA_DEF = re.compile(r"^def (\w+) : Nat := (0x[0-9a-fA-F]+)$", re.M)

# Coverage floor ratchet (#11923 / #12136). Absolute covered *bytes*, not ratio.
# Soundness bar (#12136/#12138): a DROP must not pass unnoticed → hard fail
# when covered/converted < floor. The up-side is NOT hard equality (#12136
# hazard: every concurrent conversion PR would conflict on the same two
# constants). Instead #12138 CAPS drift: live may exceed the floor by at most
# the slack below without failing; beyond slack → hard fail + paste. That
# keeps typical conversion PRs unserialized while making the accepted
# unnoticed-revert window an explicit number rather than unbounded.
# Conversion authors SHOULD still bump via `--write-floor` in the landing
# commit so slack stays near zero.
# Live-synced after #12139 batch (main b1863a9e4): 96368 B / 376 converted
# (includes #12135 rlp_item_size +140 B / +1). MEASURED, not assumed.
# GH #12127: +576 B / +1 converted — `account_write_record`, 144 instructions,
# transcribed byte-identically (`asm_cmp=IDENTICAL (576 vs 576 bytes)`).
#
# ⚠️ This is THIS change's own delta added to main's CURRENT floor, re-read at
# merge time rather than carried: main moved 109016/414 -> 120788/448 while this
# branch was open (the #12213-12216 batch and friends), so the earlier value
# here was a correct delta on a base that had since advanced.
#     120788 + 576 = 121364      448 + 1 = 449
# Not a resync to live: the one routine is exactly the one MANIFEST row this
# branch adds. Ratchet direction is up on both constants, which is the only
# direction the gate cannot catch by itself.
# GH #12351: deliberately LOWERED — retired three uncalled `chain_validate_*`
# from the guest image. Floor re-measured after rebase onto f40398e8e
# (`python3 scripts/guest_image_coverage.py --write-floor`).
EXPECTED_COVERED_BYTES_FLOOR = 120388
# Linked converted entry count floor (guestImageEntries.length #guard twin).
EXPECTED_CONVERTED_COUNT_FLOOR = 446
# Max live−floor before the exceed path hard-fails (#12138).
# Window of unnoticed revert this accepts: up to this many covered bytes /
# converted entries can land without `--write-floor` and a later drop that
# stays above the stale floor still passes. Past this bound CI forces a
# catch-up. Sized for a few typical conversions (median ~152 B, p90 ~540 B)
# without serializing concurrent PRs; not a license to skip --write-floor.
COVERED_BYTES_FLOOR_SLACK = 2000
CONVERTED_COUNT_FLOOR_SLACK = 5

_FLOOR_BYTES_RE = re.compile(
    r"^(EXPECTED_COVERED_BYTES_FLOOR = )\d+(\s*(?:#.*)?)$", re.M)
_FLOOR_CONV_RE = re.compile(
    r"^(EXPECTED_CONVERTED_COUNT_FLOOR = )\d+(\s*(?:#.*)?)$", re.M)


def write_floor_constants(covered_bytes: int, n_conv: int) -> None:
    """Rewrite the two EXPECTED_*_FLOOR assignments in this file to live values."""
    path = os.path.abspath(__file__)
    src = open(path).read()
    src2, n1 = _FLOOR_BYTES_RE.subn(rf"\g<1>{covered_bytes}\2", src, count=1)
    src3, n2 = _FLOOR_CONV_RE.subn(rf"\g<1>{n_conv}\2", src2, count=1)
    if n1 != 1 or n2 != 1:
        sys.exit(f"--write-floor: rewrite failed (bytes={n1} conv={n2}); "
                 f"edit {path} by hand")
    open(path, "w").write(src3)


def lean_camel(entry: str) -> str:
    """symbol label -> Lean camelCase stem (mirrors asm_to_program.py lean_camel)."""
    parts = entry.split("_")
    return parts[0] + "".join(p.capitalize() for p in parts[1:])


def read_text_size() -> int:
    # Prefer generated LinkPins (#11230); RegionMap only re-exports the alias.
    for path in (
        os.path.join(os.path.dirname(REGIONMAP), "RegionMapLinkPins.lean"),
        REGIONMAP,
    ):
        if not os.path.isfile(path):
            continue
        src = open(path).read()
        m = re.search(r"(?:def|abbrev) textSizeBytes : Nat := (0x[0-9a-fA-F]+)", src)
        if m:
            return int(m.group(1), 16)
    sys.exit("textSizeBytes hex not found in RegionMapLinkPins.lean or RegionMap.lean")


def read_guest_addrs() -> dict:
    """Parse generated GuestAddrs.lean: name -> declared Nat address.

    #11280: coverage previously used TSV actuals only, so a stale GuestAddrs
    (CodeReq input) with a fresh TSV still passed --gaps. This map is the
    declared half of DECLARED_START_MISMATCH.
    """
    if not os.path.isfile(GUEST_ADDRS):
        sys.exit(f"missing {GUEST_ADDRS}")
    src = open(GUEST_ADDRS).read()
    out = {m.group(1): int(m.group(2), 16) for m in _GA_DEF.finditer(src)}
    if not out:
        sys.exit(f"no `def name : Nat := 0x…` rows parsed from {GUEST_ADDRS}")
    return out


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
        r"#guard\s+(?:\((\w+)_of\s+\.zero\)|(\w+))\.length\s*(?:==|=)\s*(\d+)")
    for path in sorted(set(files)):
        for m in pat.finditer(open(os.path.join(ROOT, path)).read()):
            lens[m.group(1) or m.group(2)] = int(m.group(3))
    return lens


def read_function_bindings(files):
    """FunctionName -> (entry_label, prog_name), parsed from the generated
    `def <func> : String := "<entry>:\\n" ++ emitProgram(R) <prog>` defs,
    allowing an optional assembler directive prefix such as
    `.globl <entry>\\n" ++` before the label string.

    GH #10753 leaf awareness: the applied form
    `emitProgramR (<prog>_of .zero)` in a leaf is normalised to the
    bridge's concrete `<prog>` def name."""
    out = {}
    pat = re.compile(
        r'def\s+(\w+Function)\s*:\s*String\s*:=\s*\n?\s*'
        r'(?:"\s*\.globl\s+[\w.]+\\n"\s*\+\+\s*)?'
        r'"([\w.]+):\\n"\s*\+\+\s*'
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


def load_converted():
    """Shared manifest/bindings parse. Returns (syms, text_end, converted).

    converted: entry_symbol -> (prog_name, prog_bytes, lean_path)
    """
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
    return syms, text_end, converted


def check_declared_starts(syms, text_end, converted) -> int:
    """#11280: declared GuestAddrs start vs TSV actual for converted linked entries.

    Returns number of failures (0 = clean). Prints one line per failure with a
    stable tag (DECLARED_START_MISMATCH / DECLARED_MISSING / DECLARED_EXTENT_OVERRUN).
    Unlinked converted aliases are skipped (no TSV row).
    """
    guest_addrs = read_guest_addrs()
    addr_of = {n: a for a, n in syms}
    # next-symbol boundary for extent check
    next_end = {}
    for i, (addr, name) in enumerate(syms):
        next_end[name] = syms[i + 1][0] if i + 1 < len(syms) else text_end

    linked = sorted(
        (e for e in converted if e in addr_of),
        key=lambda e: addr_of[e])
    n_ok = 0
    failures = []
    for entry in linked:
        actual = addr_of[entry]
        prog, prog_bytes, _ = converted[entry]
        if entry not in guest_addrs:
            failures.append(
                f"DECLARED_MISSING entry={entry} actual=0x{actual:x} "
                f"prog={prog} — GuestAddrs has no def for linked converted symbol")
            continue
        declared = guest_addrs[entry]
        if declared != actual:
            delta = declared - actual
            sign = "+" if delta >= 0 else "-"
            failures.append(
                f"DECLARED_START_MISMATCH entry={entry} "
                f"declared=0x{declared:x} actual=0x{actual:x} "
                f"delta={sign}0x{abs(delta):x} prog={prog}")
            continue
        # Extent: declared start + prog bytes must not past next TSV symbol
        # (same overrun class CodeReq catches, but keyed on declared start).
        ext_end = next_end[entry]
        if declared + prog_bytes > ext_end:
            failures.append(
                f"DECLARED_EXTENT_OVERRUN entry={entry} "
                f"declared=0x{declared:x} prog_bytes={prog_bytes} "
                f"next=0x{ext_end:x} prog={prog}")
            continue
        n_ok += 1

    print(f"check-declared-starts: linked_converted={len(linked)} ok={n_ok} "
          f"fail={len(failures)}")
    for line in failures:
        print(f"  {line}")
    if failures:
        print(f"check-declared-starts: FAILED ({len(failures)} entries) — "
              "regenerate GuestAddrs via `python3 scripts/asm_to_program.py "
              "guest-addrs` after a fresh symbol-addresses.tsv (#11280)")
        return len(failures)
    print("check-declared-starts: OK — GuestAddrs starts match TSV for all "
          "converted linked entries")
    return 0


def render_doc(syms, text_end, converted, gaps, covered_bytes, gap_bytes,
               n_conv, n_unconv):
    """Render docs/4ch8f-guest-image-coverage.md from the template.

    The template holds prose and @@SLOT@@s only — every figure comes from
    the live inputs here, so there is exactly one hand-maintained copy of
    the prose and zero hand-maintained copies of any number."""
    text_size = text_end - TEXT_BASE
    sym_names = {name for _, name in syms}
    not_linked = sum(1 for e in converted if e not in sym_names)
    subst = {
        "TEXT_BASE": f"{TEXT_BASE:08x}",
        "TEXT_END": f"{text_end:08x}",
        "TEXT_SIZE": str(text_size),
        "TEXT_SIZE_HEX": f"{text_size:x}",
        "N_SYMS": str(len(syms)),
        "N_CONV": str(n_conv),
        "N_UNCONV": str(n_unconv),
        "COVERED_BYTES": str(covered_bytes),
        "COVERED_PCT": f"{100 * covered_bytes / text_size:.2f}",
        "GAP_BYTES": str(gap_bytes),
        "GAP_PCT": f"{100 * gap_bytes / text_size:.2f}",
        "N_GAPS": str(len(gaps)),
        "NOT_LINKED": str(not_linked),
        "MANIFEST_TOTAL": str(len(converted)),
        "GAP_TABLE_ROWS": "\n".join(
            f"| `0x{s:08x}` | `0x{e:08x}` | {e - s} | `{sym}` | {kind} |"
            for s, e, sym, kind in gaps),
    }
    doc = open(TEMPLATE).read()
    for key, val in subst.items():
        doc = doc.replace(f"@@{key}@@", val)
    leftover = sorted(set(re.findall(r"@@[A-Z_]+@@", doc)))
    if leftover:
        sys.exit(f"template slots left unfilled: {leftover} — "
                 "template/generator drift, refusing to emit")
    return doc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gaps", action="store_true", help="tsv gap list only")
    ap.add_argument("--md", action="store_true", help="markdown output")
    ap.add_argument("--write-doc", action="store_true",
                    help=f"regenerate {os.path.relpath(DOC, ROOT)} from "
                         f"{os.path.relpath(TEMPLATE, ROOT)} + live numbers")
    ap.add_argument("--check-doc", action="store_true",
                    help="exit 1 if the committed coverage doc differs from "
                         "--write-doc output (CI drift guard)")
    ap.add_argument("--emit-lean", action="store_true",
                    help=f"regenerate {ENTRIES_LEAN}")
    ap.add_argument("--check-declared-starts", action="store_true",
                    help="#11280: GuestAddrs declared start vs TSV actual "
                         "(converted linked only); exit 1 on mismatch")
    ap.add_argument("--check-floor", action="store_true",
                    help="#11923/#12136: fail if covered/converted drops "
                         "below EXPECTED_*_FLOOR (also on --check-doc and "
                         "default summary). Exceed is stderr paste only.")
    ap.add_argument("--write-floor", action="store_true",
                    help="#12136: rewrite EXPECTED_*_FLOOR in this file to "
                         "live covered/converted (conversion commits; not CI)")
    args = ap.parse_args()

    syms, text_end, converted = load_converted()
    text_size = text_end - TEXT_BASE

    if args.emit_lean:
        addr_of = dict((n, a) for a, n in syms)
        linked = sorted(
            ((e, prog, addr_of[e]) for e, (prog, _, _) in converted.items()
             if e in addr_of),
            key=lambda t: t[2])
        emit_entries_lean(linked,
                          [converted[e][2] for e, _, _ in linked])
        return

    if args.check_declared_starts:
        n_fail = check_declared_starts(syms, text_end, converted)
        sys.exit(1 if n_fail else 0)

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

    if args.write_doc or args.check_doc:
        doc = render_doc(syms, text_end, converted, gaps, covered_bytes,
                         gap_bytes, n_conv, n_unconv)
        if args.write_doc:
            with open(DOC, "w") as f:
                f.write(doc)
            print(f"wrote {os.path.relpath(DOC, ROOT)}")
        else:
            if not os.path.isfile(DOC):
                sys.exit(f"{os.path.relpath(DOC, ROOT)} missing; regenerate:\n\n"
                         "    python3 scripts/guest_image_coverage.py --write-doc\n")
            current = open(DOC).read()
            if current != doc:
                sys.stdout.writelines(difflib.unified_diff(
                    current.splitlines(keepends=True),
                    doc.splitlines(keepends=True),
                    fromfile="committed", tofile="regenerated"))
                sys.exit(f"\n{os.path.relpath(DOC, ROOT)} is out of date "
                         "relative to the live generator. Regenerate:\n\n"
                         "    python3 scripts/guest_image_coverage.py --write-doc\n")
            print(f"{os.path.relpath(DOC, ROOT)}: CLEAN")
    elif args.check_floor or args.write_floor:
        # Quiet: floor line / write-floor only. Accounting still runs below.
        pass
    elif args.md:
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

    # #11923/#12136 floor ratchet — skip pure emit/declared-starts/gaps/
    # write-doc/md/write-floor. --check-doc and default summary always
    # enforce; --check-floor is the explicit quiet CI entry.
    enforce_floor = (
        args.check_floor or args.check_doc
        or not (args.gaps or args.emit_lean or args.check_declared_starts
                or args.write_doc or args.md or args.write_floor)
    )
    if args.write_floor:
        write_floor_constants(covered_bytes, n_conv)
        print(f"wrote EXPECTED_COVERED_BYTES_FLOOR = {covered_bytes}")
        print(f"wrote EXPECTED_CONVERTED_COUNT_FLOOR = {n_conv}")
        return
    if enforce_floor:
        pct = 100 * covered_bytes / text_size if text_size else 0.0
        print(f"coverage floor: covered={covered_bytes} B "
              f"({pct:.2f}% of {text_size}) "
              f"converted={n_conv}  "
              f"floor_bytes={EXPECTED_COVERED_BYTES_FLOOR}  "
              f"floor_converted={EXPECTED_CONVERTED_COUNT_FLOOR}")
        errs = []
        if covered_bytes < EXPECTED_COVERED_BYTES_FLOOR:
            errs.append(
                f"covered bytes {covered_bytes} < floor "
                f"{EXPECTED_COVERED_BYTES_FLOOR} — conversion drop; "
                f"restore coverage or lower the floor only with an "
                f"explicit #11923 justification")
        if n_conv < EXPECTED_CONVERTED_COUNT_FLOOR:
            errs.append(
                f"converted count {n_conv} < floor "
                f"{EXPECTED_CONVERTED_COUNT_FLOOR} — conversion drop")
        if errs:
            for e in errs:
                print(f"COVERAGE FLOOR FAIL: {e}", file=sys.stderr)
            sys.exit(1)
        # Up-side (#12138): within slack → advisory paste, exit 0 (no
        # serialization). Beyond slack → hard fail + paste (capped drift).
        bytes_over = covered_bytes - EXPECTED_COVERED_BYTES_FLOOR
        conv_over = n_conv - EXPECTED_CONVERTED_COUNT_FLOOR
        if bytes_over > 0 or conv_over > 0:
            paste = (
                "  python3 scripts/guest_image_coverage.py --write-floor\n"
                f"EXPECTED_COVERED_BYTES_FLOOR = {covered_bytes}\n"
                f"EXPECTED_CONVERTED_COUNT_FLOOR = {n_conv}"
            )
            beyond = (
                bytes_over > COVERED_BYTES_FLOOR_SLACK
                or conv_over > CONVERTED_COUNT_FLOOR_SLACK
            )
            if beyond:
                print(
                    "COVERAGE FLOOR SLACK EXCEEDED: live exceeds floor by more "
                    f"than slack (bytes_over={bytes_over} "
                    f"slack={COVERED_BYTES_FLOOR_SLACK}; "
                    f"conv_over={conv_over} "
                    f"slack={CONVERTED_COUNT_FLOOR_SLACK}). "
                    "Bump the floor (paste), or:\n" + paste,
                    file=sys.stderr,
                )
                sys.exit(1)
            print(
                "COVERAGE FLOOR STALE: live exceeds floor within slack "
                f"(bytes_over={bytes_over}/{COVERED_BYTES_FLOOR_SLACK}; "
                f"conv_over={conv_over}/{CONVERTED_COUNT_FLOOR_SLACK}) — "
                "bump in the conversion commit (paste), or:\n" + paste,
                file=sys.stderr,
            )


if __name__ == "__main__":
    main()
