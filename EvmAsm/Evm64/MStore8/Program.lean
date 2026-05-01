/-
  EvmAsm.Evm64.MStore8.Program

  256-bit EVM MSTORE8 in two layers:

  * `evm_mstore8_kernel` (slice 5 of #99) — single-instruction byte-write
    kernel. Caller has already computed `memBase + offset` into `addrReg`
    and holds the 256-bit value in `dataReg`; the kernel just performs
    the `SB` of the low byte. Stack pop and memory-expansion bookkeeping
    are caller responsibilities here.

  * `evm_mstore8` (slice 5a of #99) — full EVM-level MSTORE8 program.
    Pops two 32-byte words from the EVM stack — offset (top, at `sp`) and
    value (next, at `sp + 32`) — and writes the LOW byte of `value` to
    EVM memory at byte-address `offset`.

    Memory is byte-addressable but lives inside the dword-keyed RV64
    memory via the `extractByte` / `replaceByte` algebra in
    `Rv64/ByteOps.lean`. The RISC-V `SB` instruction handles the
    byte-level write through that layer; this slice just assembles the
    addressing and the pop.

    Per the EVM yellow paper §H.1, MSTORE8 reads only the low 8 bits of
    the value word and triggers a 1-byte memory expansion at byte
    `offset`.

    Implementation (5 instructions = 20 bytes):

      LD   offReg   x12   0     -- low limb of offset (full 64-bit byte addr)
      LD   valReg   x12   32    -- low limb of value (low byte is the relevant one)
      ADD  addrReg  memBaseReg offReg
                                -- target byte address inside the EVM memory buf
      SB   addrReg  valReg 0    -- write the low byte of valReg
      ADDI .x12     .x12  64    -- pop both 32-byte words

    Program-only — the spec proof lands in a follow-up slice. All
    scratch registers (`offReg`, `valReg`, `addrReg`, `memBaseReg`) are
    caller-chosen; the spec slice will pin down the disjointness side
    conditions (must differ from `.x0`, `.x12`, and from each other
    where required for SD/LD non-aliasing).

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- 256-bit EVM MSTORE8 byte-write kernel: a single SB at offset 0.

    `addrReg` carries the EVM memory byte address (caller has already
    computed `memBase + offset`); `dataReg` carries the 256-bit EVM word
    whose low byte is written. Caller is responsible for stack pop and
    memory-expansion bookkeeping; this kernel only performs the byte
    write itself. -/
def evm_mstore8_kernel (addrReg dataReg : Reg) : Program :=
  SB addrReg dataReg 0

abbrev evm_mstore8_kernel_code (addrReg dataReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_mstore8_kernel addrReg dataReg)

/-- 256-bit EVM MSTORE8 program parameterized over the registers used as
    scratch and the register holding the EVM memory base address.

    * `offReg` — scratch reg, receives the low 64 bits of the popped
      offset; together with `memBaseReg` it forms the target byte
      address.
    * `valReg` — scratch reg, receives the low 64 bits of the popped
      value (only the low 8 bits matter for `SB`).
    * `addrReg` — scratch reg, holds `memBaseReg + offReg` (the actual
      byte address fed to `SB`).
    * `memBaseReg` — caller-chosen register holding the base address of
      the EVM memory buffer.

    5 instructions = 20 bytes. -/
def evm_mstore8 (offReg valReg addrReg memBaseReg : Reg) : Program :=
  LD offReg .x12 0 ;;
  LD valReg .x12 32 ;;
  ADD addrReg memBaseReg offReg ;;
  SB addrReg valReg 0 ;;
  ADDI .x12 .x12 64

/-- `CodeReq` for `evm_mstore8` placed at `base`. -/
abbrev evm_mstore8_code (offReg valReg addrReg memBaseReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_mstore8 offReg valReg addrReg memBaseReg)

end EvmAsm.Evm64
