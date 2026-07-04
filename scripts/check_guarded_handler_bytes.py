#!/usr/bin/env python3
"""Byte-tie drift guard for bead evm-asm-vgyg9 (invoked by
scripts/check-guarded-handler-bytes.sh).

Checks that the *verified* guarded ADD handler Program
(EvmAsm/Codegen/Proofs/GuardedHandlerSpecs.lean:guardedCleanRetHandlerProgram,
the CodeReq the byte-tie theorem pins) is byte-identical to the EMITTED
h_ADD subroutine at the address the dispatch table jumps to:

  1. read h_ADD / evm_cur_stack_top / evm_halt_flag from the ELF-derived
     symbol table scripts/asm-fixtures/symbol-addresses.tsv;
  2. compute the auipc/addi (la) immediate pairs GNU as/ld resolved;
  3. render the Lean Program at those immediates via the real elaborator
     (scripts/emit_guarded_handler_driver.lean), assemble it;
  4. byte-compare with the linked guest ELF's .text at addr(h_ADD).

Any divergence means the verified bytes are not the bytes the guest
dispatches to (the exact gap vgyg9 exposed at the spec level).
"""

import os
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TSV = os.path.join(REPO, "scripts", "asm-fixtures", "symbol-addresses.tsv")
ELF = os.path.join(REPO, "gen-out", "regionmap", "stateless_guest.elf")
DRIVER = os.path.join(REPO, "scripts", "emit_guarded_handler_driver.lean")
AS = "riscv64-unknown-elf-as"
OBJCOPY = "riscv64-unknown-elf-objcopy"
READELF = "riscv64-unknown-elf-readelf"

N_INSTRS = 42  # 10 guard + 30 evm_add + addi + ret (pinned by #guard in Lean)


def die(msg: str) -> None:
    print(f"check-guarded-handler-bytes: FAIL — {msg}", file=sys.stderr)
    sys.exit(1)


def sym_addr(name: str) -> int:
    with open(TSV) as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 3 and parts[0] == "stateless_guest" and parts[1] == name:
                return int(parts[2], 16)
    die(f"symbol {name} not in {TSV}")
    raise AssertionError


def la_split(delta: int) -> tuple[int, int]:
    """auipc hi20 / addi lo12 split for a pc-relative delta (R_RISCV_PCREL)."""
    lo = ((delta + 0x800) & 0xFFF) - 0x800
    hi = (delta - lo) >> 12
    assert (hi << 12) + lo == delta, (hex(delta), hex(hi), lo)
    assert 0 <= hi < (1 << 20), f"hi20 out of range for delta {delta:#x}"
    return hi, lo


def text_bytes(asm_text: str, d: str) -> bytes:
    s = os.path.join(d, "g.s")
    o = os.path.join(d, "g.o")
    b = os.path.join(d, "g.bin")
    with open(s, "w") as f:
        f.write(".text\n_f:\n" + asm_text + "\n")
    subprocess.run([AS, "-march=rv64im", "-mno-relax", "-o", o, s], check=True)
    subprocess.run([OBJCOPY, "-O", "binary", "-j", ".text", o, b], check=True)
    with open(b, "rb") as f:
        return f.read()


def elf_text_window(addr: int, n: int) -> bytes:
    out = subprocess.run(
        [READELF, "-S", "-W", ELF], check=True, capture_output=True, text=True
    ).stdout
    for line in out.splitlines():
        if ".text" in line:
            cols = line.replace("[", " ").replace("]", " ").split()
            # name type vaddr fileoff size ...
            i = cols.index(".text")
            vaddr = int(cols[i + 2], 16)
            fileoff = int(cols[i + 3], 16)
            break
    else:
        die(".text section not found in ELF")
    with open(ELF, "rb") as f:
        f.seek(fileoff + (addr - vaddr))
        return f.read(n)


def main() -> None:
    if not os.path.exists(ELF):
        die(f"{ELF} missing — run scripts/gen-symbol-addresses.py --build first")
    h_add = sym_addr("h_ADD")
    cell = sym_addr("evm_cur_stack_top")
    flag = sym_addr("evm_halt_flag")
    hi1, lo1 = la_split(cell - h_add)          # la x14 pair at h_ADD+0
    hi2, lo2 = la_split(flag - (h_add + 24))   # la x6 pair at h_ADD+24

    render = subprocess.run(
        ["lake", "env", "lean", "--run", DRIVER,
         str(hi1), str(lo1), str(hi2), str(lo2)],
        check=True, capture_output=True, text=True, cwd=REPO,
    ).stdout

    with tempfile.TemporaryDirectory() as d:
        lean_bytes = text_bytes(render, d)
    if len(lean_bytes) != 4 * N_INSTRS:
        die(f"Lean render assembled to {len(lean_bytes)} bytes, expected {4 * N_INSTRS}")

    emitted = elf_text_window(h_add, 4 * N_INSTRS)
    if lean_bytes != emitted:
        for k in range(0, 4 * N_INSTRS, 4):
            a, b = lean_bytes[k:k + 4], emitted[k:k + 4]
            marker = "  <-- DIFF" if a != b else ""
            print(f"  +{k:3d}: lean {a.hex()}  emitted {b.hex()}{marker}",
                  file=sys.stderr)
        die(f"verified Program != emitted h_ADD bytes at {h_add:#x}")

    print(f"check-guarded-handler-bytes: OK — verified guarded ADD Program is "
          f"byte-identical to emitted h_ADD @ {h_add:#x} ({4 * N_INSTRS} bytes)")


if __name__ == "__main__":
    main()
