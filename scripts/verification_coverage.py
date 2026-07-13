#!/usr/bin/env python3
"""Report instruction coverage for emitted Codegen ``Program`` routines.

The total is the sum of the kernel-checked ``#guard <name>_prog.length = N``
pins in ``EvmAsm/Codegen/Programs`` and the three dispatcher programs emitted
from ``EvmAsm/Codegen/Dispatch.lean``.  The verified set is the exact
``MANIFEST.tsv`` enumeration consumed by ``scripts/check-asm-to-program.sh``;
each manifest entry must also have its generated ``*_eq_prog`` byte-tie
theorem and a pinned ``_prog`` length.

This is accounting tooling only.  It does not modify Lean sources, generated
guest bytes, or the manifest.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn


ROOT = Path(__file__).resolve().parent.parent
PROGRAMS = ROOT / "EvmAsm/Codegen/Programs"
DISPATCH = ROOT / "EvmAsm/Codegen/Dispatch.lean"
MANIFEST = ROOT / "scripts/asm-fixtures/MANIFEST.tsv"

GUARD_RE = re.compile(
    r"(?m)^#guard\s+(?P<prog>[A-Za-z0-9_]+_prog)\.length\s*=\s*(?P<n>\d+)\s*$"
)
FUNCTION_RE = re.compile(
    r'def\s+(?P<func>[A-Za-z0-9_]+Function)\s*:\s*String\s*:=\s*\n?'
    r'\s*"(?P<entry>[A-Za-z0-9_.$]+):\\n"\s*\+\+\s*'
    r'emitProgramR?\s+(?P<prog>[A-Za-z0-9_]+_prog)\b'
)


@dataclass(frozen=True)
class Routine:
    prog: str
    instructions: int
    source: str
    manifest_function: str = ""


def fail(message: str) -> NoReturn:
    print(f"verification-coverage: ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def read_guards(path: Path) -> dict[str, tuple[int, str]]:
    """Read the source-pinned instruction lengths from one Lean file."""
    source = path.relative_to(ROOT).as_posix()
    out: dict[str, tuple[int, str]] = {}
    for match in GUARD_RE.finditer(path.read_text()):
        prog = match.group("prog")
        value = int(match.group("n"))
        if prog in out:
            fail(f"duplicate length guard for {prog} in {source}")
        out[prog] = (value, source)
    return out


GuardKey = tuple[str, str]


def read_all_guards() -> dict[GuardKey, int]:
    guards: dict[GuardKey, int] = {}
    files = sorted(PROGRAMS.glob("*.lean")) + [DISPATCH]
    for path in files:
        source = path.relative_to(ROOT).as_posix()
        for prog, (length, _source) in read_guards(path).items():
            key = (source, prog)
            if key in guards:
                fail(f"duplicate program {prog} in {source}")
            guards[key] = length
    if not guards:
        fail("no _prog length guards found")
    return guards


def read_manifest() -> list[tuple[str, str]]:
    entries: list[tuple[str, str]] = []
    for line_number, line in enumerate(MANIFEST.read_text().splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2:
            fail(f"{MANIFEST.relative_to(ROOT)}:{line_number}: expected two TSV fields")
        entries.append((fields[0], fields[1]))
    return entries


def read_bindings(paths: set[str]) -> dict[str, tuple[str, str, str]]:
    """Return Function -> (program, source, function source text)."""
    out: dict[str, tuple[str, str, str]] = {}
    for rel in sorted(paths):
        path = ROOT / rel
        text = path.read_text()
        source = rel
        for match in FUNCTION_RE.finditer(text):
            func = match.group("func")
            if func in out:
                fail(f"duplicate Function binding for {func}")
            out[func] = (match.group("prog"), source, text)
    return out


def verified_routines(guards: dict[GuardKey, int]) -> dict[GuardKey, Routine]:
    entries = read_manifest()
    bindings = read_bindings({path for _, path in entries})
    out: dict[GuardKey, Routine] = {}
    for func, _manifest_path in entries:
        if func not in bindings:
            fail(f"manifest entry {func} has no generated Function binding")
        prog, source, text = bindings[func]
        key = (source, prog)
        if key not in guards:
            fail(f"manifest entry {func} references {prog}, but it has no length guard")
        theorem = rf"(?m)^theorem\s+{re.escape(func)}_eq_prog\b"
        if not re.search(theorem, text):
            fail(f"manifest entry {func} has no {func}_eq_prog byte-tie theorem")
        if key in out:
            fail(f"manifest entries alias the same program {prog} in {source}")
        out[key] = Routine(prog, guards[key], source, func)
    return out


def print_report(guards: dict[GuardKey, int], verified: dict[GuardKey, Routine],
                 summary_only: bool) -> None:
    total = sum(guards.values())
    verified_total = sum(row.instructions for row in verified.values())
    total_routines = len(guards)
    verified_routines_count = len(verified)
    percent = 100.0 * verified_total / total if total else 0.0

    if not summary_only:
        print("Guest instruction verification coverage")
        print("  total source: #guard _prog.length pins in Programs/*.lean + Dispatch.lean")
        print("  verified source: MANIFEST.tsv entries checked by check-asm-to-program.sh")
        print(f"  routines: {verified_routines_count}/{total_routines} verified")
        print(f"  instructions: {verified_total}/{total} verified ({percent:.4f}%)")
        print()
        print("STATUS\tPROGRAM\tINSTRUCTIONS\tSOURCE\tBYTE_TIE_FUNCTION")
        for source, prog in sorted(guards):
            length = guards[(source, prog)]
            row = verified.get((source, prog))
            if row is None:
                print(f"UNVERIFIED\t{prog}\t{length}\t{source}\t")
            else:
                print(f"VERIFIED\t{prog}\t{length}\t{row.source}\t{row.manifest_function}")

    # Keep this single line stable for dashboards and shell consumers.
    print("SUMMARY"
          f" total_instructions={total}"
          f" verified_instructions={verified_total}"
          f" verified_percent={percent:.4f}"
          f" total_routines={total_routines}"
          f" verified_routines={verified_routines_count}"
          f" unverified_routines={total_routines - verified_routines_count}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--summary-only", action="store_true",
                        help="print only the machine-readable SUMMARY line")
    args = parser.parse_args()
    guards = read_all_guards()
    verified = verified_routines(guards)
    print_report(guards, verified, args.summary_only)


if __name__ == "__main__":
    main()
