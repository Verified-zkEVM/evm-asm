/-
  EvmAsm.Codegen.Probes.HashProbes

  Hash-bridge probe BuildUnits carved out of
  `EvmAsm.Codegen.Programs` per the file-size hard cap.
  Hosts:

    K1   zisk_keccak_probe

  The standalone probe ELF exercising the keccak hash bridge; the
  function strings themselves live in `Programs/HashBridge.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## zisk_keccak_probe — PR-K1 ziskemu Keccak-f[1600] intrinsic probe

    Emits a raw-asm probe that triggers ziskemu's built-in
    Keccak-f[1600] accelerator (`_opcode_keccak` in
    `~/.zisk/zisk/emulator-asm/src/emu.c:507`). The accelerator is
    invoked by writing the state pointer into a non-standard CSR at
    address 0x800 -- which is the syscall ID the Zisk compiler
    expects, per `ziskos/entrypoint/src/syscalls/keccakf.rs` (uses
    `csrs 0x800, <reg>` via the `ziskos_syscall!` macro).

    GNU-as `csrs csr, rs1` expands to `csrrs x0, csr, rs1`. The
    32-bit encoding for `csrs 0x800, a0`:

      csr(0x800)    rs1(x10=01010)  f3(010)  rd(x0)    op(0x73)
      [31..20]      [19..15]        [14..12] [11..7]   [6..0]
      = 0x80052073

    We emit this as a raw `.4byte` directive rather than the
    `csrs` mnemonic so the existing
    `riscv64-unknown-elf-as -march=rv64imac` toolchain string
    works without enabling the `Zicsr` extension. The 32-bit value
    is what `as -march=rv64imac_zicsr` produces for the same
    mnemonic; pinning it here is the whole point of PR-K1.

    Probe sequence:
      la a0, zisk_keccak_state    # state pointer
      .4byte 0x80052073           # csrs 0x800, a0 -> _opcode_keccak
      <copy 200 bytes to OUTPUT_ADDR>
      <halt>

    Verified Program body is a single NOP -- everything observable
    happens in raw asm, so the verified semantics carry no claim
    about the probe yet. PR-K2 wires this through verified Instrs
    once the CSR instruction is added to `Rv64.Instr`. -/

/-- Asm prologue: probe the keccak intrinsic and stream the
    post-permutation 200-byte state to ziskemu's public-output
    region. Hard-codes `OUTPUT_ADDR = 0xa0010000` (mirrors the
    constant above). -/
def ziskKeccakProbePrologue : String :=
  "  la a0, zisk_keccak_state\n" ++
  "  .4byte 0x80052073           # csrs 0x800, a0\n" ++
  "  li t0, 0xa0010000\n" ++
  "  li t1, 25\n" ++
  ".Lzkp_copy_loop:\n" ++
  "  ld t2, 0(a0)\n" ++
  "  sd t2, 0(t0)\n" ++
  "  addi a0, a0, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lzkp_copy_loop"

/-- `.data` section: 200 zero bytes labeled `zisk_keccak_state`.
    Lands in ziskemu RAM (0xa0000000..0xc0000000) via the standard
    `-Tdata=0xa0000000` link flag from `Codegen/Driver.lean`. -/
def ziskKeccakProbeDataSection : String :=
  ".section .data\n" ++
  "zisk_keccak_state:\n" ++
  "  .zero 200"

def ziskKeccakProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccakProbePrologue
  dataAsm     := ziskKeccakProbeDataSection
}

end EvmAsm.Codegen
