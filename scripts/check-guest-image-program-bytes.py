#!/usr/bin/env python3
"""Compare linked guest routines with the registered ``GuestImageEntries`` Programs.

This is leg 3 of the guest-image registration contract (GH #12151).  The
MANIFEST/GuestImageEntries checks establish that a row exists and names the
right Program; this check measures the linked image itself.  Every registered
Program is rendered by Lean, assembled into one temporary object, and compared
byte-for-byte with the linked ``stateless_guest`` ELF at the corresponding
symbol.  It therefore catches a parallel String definition even when all
source registries agree.

The check is deliberately post-link: the linked ELF is the authority, and a
source consumer census is only a proxy.  ``--self-test`` injects one different
registered Program in memory and requires the comparison to fail, so a
permanently green or disconnected check cannot pass unnoticed.

The expected render is the concrete ``Program`` view of an
``emitProgramR prog relocs`` Function: its ``jalOff`` values are already
resolved through ``GuestAddrs``.  This relies on the companion
``check-guestaddrs-starts`` gate, which ties those GuestAddrs values to the
linker symbol table; it is not a circular assumption.  It also catches a
Program/RelocTable target disagreement as a side effect: the linker follows
the reloc table while this render follows the concrete Program (the historical
PR #12110 class).
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
ENTRIES = REPO / "EvmAsm/Codegen/Proofs/GuestImageEntries.lean"

ROW_RE = re.compile(
    r"\(GuestAddrs\.([A-Za-z_][A-Za-z0-9_']*),\s*"
    r"([A-Za-z_][A-Za-z0-9_']*)\)"
)


def run(cmd: list[str], *, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            cmd,
            cwd=REPO,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=True,
        )
    except FileNotFoundError as exc:
        raise RuntimeError(f"required tool is not installed: {cmd[0]}") from exc
    except subprocess.CalledProcessError as exc:
        detail = (exc.stdout + exc.stderr).strip()
        raise RuntimeError(f"command failed ({' '.join(cmd)}):\n{detail}") from exc


def parse_entries() -> list[tuple[str, str]]:
    rows = ROW_RE.findall(ENTRIES.read_text())
    if not rows:
        raise RuntimeError(f"no GuestImageEntries rows found in {ENTRIES}")
    seen: set[str] = set()
    for entry, _prog in rows:
        if entry in seen:
            raise RuntimeError(f"duplicate GuestAddrs.{entry} in {ENTRIES}")
        seen.add(entry)
    return rows


def render_programs(rows: list[tuple[str, str]], out: Path) -> None:
    """Use the real Lean elaborator to render every registered Program."""
    row_expr = ",\n    ".join(f'("{entry}", {prog})' for entry, prog in rows)
    source = f'''import EvmAsm.Codegen.Proofs.GuestImageEntries
import EvmAsm.Codegen.Emit

open EvmAsm.Codegen
open EvmAsm.Rv64

def _guestImageProgramRows : List (String × Program) := [
    {row_expr}
  ]

def main : IO Unit := do
  _guestImageProgramRows.forM fun (entry, prog) => do
    IO.print ("@@BEGIN " ++ entry ++ "\\n")
    IO.print (emitProgram prog)
    IO.print "\\n@@END\\n"
'''
    runner = out.parent / "guest-image-program-render.lean"
    runner.write_text(source)
    try:
        # Materialize the exact imported module before `lake env lean`.  A
        # cache-satisfied Lake build can execute the codegen binary without
        # placing its imported oleans in `.lake/build`; invoking Lean directly
        # in that state would turn a real gate into a misleading missing-olean
        # failure.  This targeted non-cache build is cheap after the normal
        # post-build lane and keeps the failure mode explicit on a fresh tree.
        env = os.environ.copy()
        env["LAKE_ARTIFACT_CACHE"] = "false"
        run(["lake", "build", "EvmAsm.Codegen.Proofs.GuestImageEntries"], env=env)
        proc = run(["lake", "env", "lean", "--run", str(runner)], env=env)
        out.write_text(proc.stdout)
    finally:
        runner.unlink(missing_ok=True)


def parse_rendered(path: Path, rows: list[tuple[str, str]]) -> dict[str, str]:
    text = path.read_text()
    rendered: dict[str, str] = {}
    for entry, _prog in rows:
        begin = f"@@BEGIN {entry}\n"
        end = "\n@@END\n"
        start = text.find(begin)
        if start < 0:
            raise RuntimeError(f"Lean render omitted GuestAddrs.{entry}")
        body_start = start + len(begin)
        finish = text.find(end, body_start)
        if finish < 0:
            raise RuntimeError(f"Lean render for GuestAddrs.{entry} has no end marker")
        if entry in rendered:
            raise RuntimeError(f"Lean render duplicated GuestAddrs.{entry}")
        rendered[entry] = text[body_start:finish]
    return rendered


def write_combined_asm(rendered: dict[str, str], rows: list[tuple[str, str]], path: Path) -> None:
    lines = [".text", ".option norvc"]
    for entry, _prog in rows:
        marker = f"__guest_image_program_{entry}"
        lines += [f".globl {marker}", f"{marker}:", rendered[entry]]
    path.write_text("\n".join(lines) + "\n")


def parse_nm(text: str) -> dict[str, int]:
    result: dict[str, int] = {}
    for line in text.splitlines():
        fields = line.split()
        if len(fields) != 3:
            continue
        try:
            addr = int(fields[0], 16)
        except ValueError:
            continue
        result.setdefault(fields[2], addr)
    return result


def assemble_rendered(asm: Path, obj: Path, binary: Path) -> dict[str, int]:
    assembler = shutil.which("riscv64-unknown-elf-as") or shutil.which("riscv64-elf-as")
    objcopy = shutil.which("riscv64-unknown-elf-objcopy") or shutil.which("riscv64-elf-objcopy")
    nm = shutil.which("riscv64-unknown-elf-nm") or shutil.which("riscv64-elf-nm")
    if not assembler or not objcopy or not nm:
        raise RuntimeError("riscv64 cross assembler/objcopy/nm is required for leg 3")
    run([assembler, "-march=rv64imac", "-mno-relax", "-o", str(obj), str(asm)])
    run([objcopy, "-O", "binary", "--only-section=.text", str(obj), str(binary)])
    return parse_nm(run([nm, "-n", "--defined-only", str(obj)]).stdout)


def readelf_text_base(elf: Path) -> int:
    readelf = shutil.which("riscv64-unknown-elf-readelf") or shutil.which("readelf")
    if not readelf:
        raise RuntimeError("readelf is required for leg 3")
    output = run([readelf, "-SW", str(elf)]).stdout
    for line in output.splitlines():
        if ".text" not in line:
            continue
        match = re.search(r"\]\s+\.text\s+\S+\s+([0-9a-fA-F]+)\s+[0-9a-fA-F]+\s+[0-9a-fA-F]+", line)
        if match:
            return int(match.group(1), 16)
    raise RuntimeError(f"linked ELF has no .text section: {elf}")


def read_elf(elf: Path) -> tuple[dict[str, int], bytes, int]:
    objcopy = shutil.which("riscv64-unknown-elf-objcopy") or shutil.which("objcopy")
    nm = shutil.which("riscv64-unknown-elf-nm") or shutil.which("nm")
    if not objcopy or not nm:
        raise RuntimeError("readelf/nm/objcopy are required for leg 3")
    with tempfile.TemporaryDirectory(prefix="guest-image-elf-") as td:
        binary = Path(td) / "text.bin"
        run([objcopy, "-O", "binary", "--only-section=.text", str(elf), str(binary)])
        blob = binary.read_bytes()
    return parse_nm(run([nm, "-n", "--defined-only", str(elf)]).stdout), blob, readelf_text_base(elf)


def expected_slices(
    rows: list[tuple[str, str]],
    render_symbols: dict[str, int],
    render_binary: bytes,
) -> dict[str, bytes]:
    marker_starts = [render_symbols[f"__guest_image_program_{entry}"] for entry, _ in rows]
    expected: dict[str, bytes] = {}
    for idx, (entry, _prog) in enumerate(rows):
        marker = f"__guest_image_program_{entry}"
        if marker not in render_symbols:
            raise RuntimeError(f"rendered object has no marker {marker}")
        start = render_symbols[marker]
        end = marker_starts[idx + 1] if idx + 1 < len(marker_starts) else len(render_binary)
        expected[entry] = render_binary[start:end]
    return expected


def compare(
    rows: list[tuple[str, str]],
    expected: dict[str, bytes],
    elf_symbols: dict[str, int],
    elf_binary: bytes,
    text_base: int,
) -> list[str]:
    failures: list[str] = []
    for entry, _prog in rows:
        expected_bytes = expected[entry]
        if entry not in elf_symbols:
            failures.append(f"{entry}: GuestImageEntries row has no linked ELF symbol")
            continue
        actual_start = elf_symbols[entry] - text_base
        if actual_start < 0 or actual_start + len(expected_bytes) > len(elf_binary):
            failures.append(
                f"{entry}: linked slice outside .text (offset={actual_start} "
                f"bytes={len(expected_bytes)} text={len(elf_binary)})"
            )
            continue
        actual = elf_binary[actual_start : actual_start + len(expected_bytes)]
        if actual != expected_bytes:
            first = next(
                (i for i, (a, b) in enumerate(zip(actual, expected_bytes)) if a != b),
                min(len(actual), len(expected_bytes)),
            )
            failures.append(
                f"{entry}: linked bytes differ at +0x{first:x} "
                f"(actual_len={len(actual)} expected_len={len(expected_bytes)})"
            )
    return failures


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--elf", required=True, type=Path, help="linked stateless_guest ELF")
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="inject a different Program and require failure",
    )
    args = ap.parse_args(argv[1:])
    rows = parse_entries()
    if not args.elf.is_file():
        print(f"check-guest-image-program-bytes: missing ELF {args.elf}", file=sys.stderr)
        return 1
    with tempfile.TemporaryDirectory(prefix="guest-image-program-") as td:
        tmp = Path(td)
        rendered_file = tmp / "rendered.txt"
        render_programs(rows, rendered_file)
        rendered = parse_rendered(rendered_file, rows)
        asm = tmp / "programs.s"
        obj = tmp / "programs.o"
        binary = tmp / "programs.bin"
        write_combined_asm(rendered, rows, asm)
        render_symbols = assemble_rendered(asm, obj, binary)
        render_binary = binary.read_bytes()
        expected = expected_slices(rows, render_symbols, render_binary)
        elf_symbols, elf_binary, text_base = read_elf(args.elf)
        failures = compare(rows, expected, elf_symbols, elf_binary, text_base)
        if failures:
            print(f"check-guest-image-program-bytes: FAIL — {len(failures)} mismatch(es)", file=sys.stderr)
            for failure in failures:
                print(f"  ✗ {failure}", file=sys.stderr)
            return 1
        print(f"check-guest-image-program-bytes: PASS — {len(rows)} registered Programs byte-match linked ELF")

        if args.self_test:
            # Use a different rendered Program as the injected registration.
            # This is the same failure mode as pointing a row at a parallel
            # String: the linked image remains unchanged while the registry
            # expectation changes.
            target = next(
                (
                    i
                    for i in range(1, len(rows))
                    if rendered[rows[i][0]] != rendered[rows[0][0]]
                ),
                None,
            )
            if target is None:
                print(
                    "check-guest-image-program-bytes: SELF-TEST failed — "
                    "no distinct Program",
                    file=sys.stderr,
                )
                return 1
            injected = dict(expected)
            injected[rows[0][0]] = expected[rows[target][0]]
            injected_failures = compare(rows, injected, elf_symbols, elf_binary, text_base)
            if not injected_failures:
                print(
                    "check-guest-image-program-bytes: SELF-TEST failed — "
                    "injected Program passed",
                    file=sys.stderr,
                )
                return 1
            print(
                f"check-guest-image-program-bytes: SELF-TEST passed — replacing "
                f"{rows[0][0]} with {rows[target][0]} fails"
            )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except RuntimeError as exc:
        print(f"check-guest-image-program-bytes: ERROR — {exc}", file=sys.stderr)
        sys.exit(1)
