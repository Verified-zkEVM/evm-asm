#!/usr/bin/env python3
"""
hed_arity_guard.py — GH #12462 structural guard.

Assert from the *linked* guest ELF disassembly (never Lean source, never
GuestAddrs literals) that every `jal` targeting `header_extended_decode` is
preceded, in the same function, by a `jal` to
`header_extended_decode_arity_check`.

Why: `header_extended_decode` accepts a canonical 20-field list (a0=0) while
execution-specs rejects it. Production is safe only because both linked JALs
sit behind the arity check. That safety is a call-site convention; this gate
enforces it. This is the check that would have caught #12438 (linked checker,
zero callers).

Scope of the reverse scan: linear backward walk within the enclosing .text
symbol, stopping at the previous `jal` to decode (must not share one check)
or the function entry. Does not prove full CFG dominance across arbitrary
branches that skip the check — that is a stronger property; the linear
convention matches the known call sites and catches an unguarded third caller.

Usage:
  python3 scripts/hed_arity_guard.py                  # enforce on guest ELF
  python3 scripts/hed_arity_guard.py --self-test      # synthetic FAIL then PASS
  python3 scripts/hed_arity_guard.py --elf PATH
"""
from __future__ import annotations

import argparse
import hashlib
import pathlib
import re
import subprocess
import sys
import tempfile
from shutil import which

ROOT = pathlib.Path(__file__).resolve().parents[1]
DEFAULT_ELF = ROOT / "gen-out" / "regionmap" / "stateless_guest.elf"

DECODE = "header_extended_decode"
ARITY = "header_extended_decode_arity_check"

OBJDUMP_CANDIDATES = (
    "riscv64-unknown-elf-objdump",
    "riscv64-elf-objdump",
)
NM_CANDIDATES = (
    "riscv64-unknown-elf-nm",
    "riscv64-elf-nm",
)
AS_CANDIDATES = (
    "riscv64-unknown-elf-as",
    "riscv64-elf-as",
)
LD_CANDIDATES = (
    "riscv64-unknown-elf-ld",
    "riscv64-elf-ld",
)


def die(msg: str, code: int = 1) -> None:
    print(f"hed_arity_guard: {msg}", file=sys.stderr)
    raise SystemExit(code)


def pick_tool(cands: tuple[str, ...], env_key: str | None = None) -> str:
    if env_key:
        import os

        override = os.environ.get(env_key)
        if override:
            return override
    for c in cands:
        if which(c):
            return c
    die(f"missing toolchain tool; tried {', '.join(cands)}")


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_nm(elf: pathlib.Path, nm: str) -> dict[str, int]:
    out = subprocess.check_output([nm, str(elf)], text=True)
    syms: dict[str, int] = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) >= 3 and parts[1] in ("t", "T"):
            syms.setdefault(parts[2], int(parts[0], 16))
    return syms


def parse_objdump(elf: pathlib.Path, objdump: str) -> list[tuple[int, str, str]]:
    dump = subprocess.check_output([objdump, "-d", str(elf)], text=True)
    instrs: list[tuple[int, str, str]] = []
    for line in dump.splitlines():
        m = re.match(r"\s*([0-9a-f]+):\s+[0-9a-f]+\s+(\S+)(?:\s+(.*))?", line)
        if not m:
            continue
        addr = int(m.group(1), 16)
        op = m.group(2)
        rest = (m.group(3) or "").strip()
        instrs.append((addr, op, rest))
    return instrs


def jal_target(rest: str) -> int | None:
    # Linked: `jal ra,8000b45c <header_extended_decode>` or `jal 8000b45c <...>`
    m = re.search(r"(?:^|[\s,])([0-9a-f]{4,})(?:\s*<|$)", rest)
    return int(m.group(1), 16) if m else None


def enclosing_symbol(addr: int, sym_addrs: dict[str, int]) -> tuple[str, int] | None:
    """Largest symbol start ≤ addr (standard nm 'enclosing function' heuristic)."""
    best: tuple[str, int] | None = None
    for name, start in sym_addrs.items():
        if start <= addr and (best is None or start > best[1]):
            best = (name, start)
    return best


def check_elf(elf: pathlib.Path) -> list[str]:
    objdump = pick_tool(OBJDUMP_CANDIDATES, "RISCV_OBJDUMP")
    nm = pick_tool(NM_CANDIDATES, "RISCV_NM")
    digest = sha256_file(elf)
    print(f"hed_arity_guard: elf={elf}")
    print(f"hed_arity_guard: elf_sha256={digest}")

    syms = parse_nm(elf, nm)
    if DECODE not in syms:
        return [f"symbol {DECODE!r} missing from linked ELF"]
    if ARITY not in syms:
        return [f"symbol {ARITY!r} missing from linked ELF"]

    decode_addr = syms[DECODE]
    arity_addr = syms[ARITY]
    print(f"hed_arity_guard: {DECODE}=0x{decode_addr:x}")
    print(f"hed_arity_guard: {ARITY}=0x{arity_addr:x}")

    instrs = parse_objdump(elf, objdump)
    by_addr = {a: (op, rest) for a, op, rest in instrs}
    ordered = sorted(by_addr)

    decode_jals: list[int] = []
    for addr, op, rest in instrs:
        if op not in ("jal", "jalr"):
            # Only direct `jal` encodes a fixed target we can resolve.
            continue
        if op == "jalr":
            continue
        tgt = jal_target(rest)
        if tgt == decode_addr:
            decode_jals.append(addr)

    print(f"hed_arity_guard: jal_to_{DECODE} count={len(decode_jals)}")
    if not decode_jals:
        return [f"no jal targeting {DECODE} — unexpected (expected ≥1 production caller)"]

    failures: list[str] = []
    for daddr in decode_jals:
        enc = enclosing_symbol(daddr, syms)
        if enc is None:
            failures.append(f"0x{daddr:x}: jal to {DECODE} has no enclosing .text symbol")
            continue
        fname, fstart = enc
        # Walk backward within the function.
        idx = ordered.index(daddr)
        found_arity = False
        while idx > 0:
            idx -= 1
            a = ordered[idx]
            if a < fstart:
                break
            op, rest = by_addr[a]
            if op != "jal":
                continue
            tgt = jal_target(rest)
            if tgt == decode_addr:
                failures.append(
                    f"0x{daddr:x} in {fname}: previous jal to {DECODE} at 0x{a:x} "
                    f"with no intervening jal to {ARITY}"
                )
                found_arity = True  # stop; already failed
                break
            if tgt == arity_addr:
                found_arity = True
                print(
                    f"hed_arity_guard: OK 0x{daddr:x} in {fname} "
                    f"preceded by {ARITY} at 0x{a:x}"
                )
                break
        if not found_arity:
            failures.append(
                f"0x{daddr:x} in {fname}: jal to {DECODE} with no preceding "
                f"jal to {ARITY} in the same function"
            )
    return failures


def assemble_link(name: str, body: str, work: pathlib.Path) -> pathlib.Path:
    """Assemble+link a tiny ELF so nm/objdump see real symbols and jal targets."""
    as_ = pick_tool(AS_CANDIDATES)
    ld = pick_tool(LD_CANDIDATES)
    # Provide both symbols so jal relocs resolve; arity may be unreferenced.
    full = f"""
.option norvc
.section .text
.globl _start
.globl {DECODE}
.globl {ARITY}
_start:
{body}
{ARITY}:
  ret
{DECODE}:
  ret
"""
    sfile = work / f"{name}.s"
    ofile = work / f"{name}.o"
    elf = work / f"{name}.elf"
    sfile.write_text(full)
    subprocess.check_call([as_, "-o", str(ofile), str(sfile)])
    subprocess.check_call(
        [ld, "-o", str(elf), str(ofile), "-e", "_start", "--section-start=.text=0x80000000"]
    )
    return elf


def self_test() -> None:
    as_ = pick_tool(AS_CANDIDATES)
    _ = as_  # presence only; assemble_link picks tools
    with tempfile.TemporaryDirectory() as td:
        work = pathlib.Path(td)
        # Unguarded caller must FAIL.
        bad = assemble_link(
            "unguarded",
            f"""
  jal ra, {DECODE}
  ret
""",
            work,
        )
        bad_fails = check_elf(bad)
        if not bad_fails:
            die("self-test: unguarded jal to decode did not fail")
        print("hed_arity_guard: self-test unguarded → FAIL (expected)")

        # Guarded caller must PASS.
        good = assemble_link(
            "guarded",
            f"""
  jal ra, {ARITY}
  bnez a0, 1f
  jal ra, {DECODE}
1:
  ret
""",
            work,
        )
        good_fails = check_elf(good)
        if good_fails:
            die("self-test: guarded jal unexpectedly failed:\n  " + "\n  ".join(good_fails))
        print("hed_arity_guard: self-test guarded → PASS (expected)")
    print("hed_arity_guard: self-test OK")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--elf", type=pathlib.Path, default=None)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        self_test()
        return
    elf = args.elf or DEFAULT_ELF
    if not elf.is_file():
        die(f"ELF not found: {elf} (emit via lake exe codegen --program stateless_guest)")
    fails = check_elf(elf)
    if fails:
        for f in fails:
            print(f"hed_arity_guard: FAIL {f}", file=sys.stderr)
        die(
            f"{len(fails)} unguarded jal(s) to {DECODE}. "
            "Every jal must be preceded by jal to "
            f"{ARITY} in the same function (#12462)."
        )
    print(f"hed_arity_guard: PASS ({DECODE} callers all arity-guarded)")


if __name__ == "__main__":
    main()
