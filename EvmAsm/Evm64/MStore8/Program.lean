/-
  EvmAsm.Evm64.MStore8.Program

  256-bit EVM MSTORE8: write the LOW byte of a 256-bit value to a single
  byte of EVM memory at a caller-prepared byte address.

  The slice 5 issue body (issue #99) calls this a "single SB spec", so we
  expose just the SB kernel here (one instruction). Full EVM-level MSTORE8
  also pops `(offset, value)` from the EVM stack and updates the MSIZE
  high-water mark; those layers compose on top of this kernel in later
  slices and are intentionally out of scope for this slice. The pure
  helper `evmMemExpand_one_byte` in `Evm64/Memory.lean` consumers can use
  to discharge the size update is provided in `Spec.lean`.

  Implementation (1 instruction = 4 bytes):

    SB addrReg dataReg 0    -- write low byte of `dataReg` at addr `addrReg`

  `addrReg` holds the byte address (already the EVM memory base + offset)
  and `dataReg` holds the 256-bit EVM word whose low byte is the byte to
  write. (The EVM yellow paper specifies that MSTORE8 writes only the
  least significant byte of the popped 256-bit operand, which on RV64
  matches taking the low 8 bits of the low limb.)

  Slice 5 of issue #99. Authored by @pirapira; implemented by Hermes-bot
  (evm-hermes).
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

end EvmAsm.Evm64
