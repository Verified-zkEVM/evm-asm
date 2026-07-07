/-
  EvmAsm.Evm64.GasOpcode.Program

  RISC-V program implementing the EVM `GAS` opcode (0x5a).

  GAS pushes the amount of gas remaining *after* this instruction's own base
  cost has been charged. The dispatcher's per-opcode gas loop decrements the
  running `gasRemaining` cell (env block, offset 568) before the handler body
  runs, so GAS is a pure read of that cell followed by a stack push — the same
  shape as CALLDATASIZE/CODESIZE/MSIZE, differing only in the offset loaded.

  The value fits in 64 bits, so it goes in the LOW limb of the pushed word and
  the upper three limbs are zero.

  Implementation (6 instructions = 24 bytes), ordered ADDI-then-LD to match the
  running `h_GAS` dispatcher handler emission byte-for-byte:

    ADDI x12    x12        -32              -- decrement EVM stack pointer
    LD   tmpReg envBaseReg gasRemainingOff  -- load gasRemaining into tmpReg
    SD   x12    tmpReg     0                -- write low limb (gas value)
    SD   x12    x0         8                -- zero upper three limbs
    SD   x12    x0         16
    SD   x12    x0         24
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64
namespace GasOpcode

open EvmAsm.Rv64

/-- Byte offset of the `gasRemaining` cell within the dispatcher env block.
    The per-opcode gas loop maintains this cell (seeded at env+568 by the
    dispatcher prologue, decremented by each opcode's cost before its handler
    body runs); GAS reads it. -/
def gasRemainingOff : Nat := 568

/-- Parameterized RISC-V program implementing `GAS`.
    `envBaseReg` holds the env-block base; `tmpReg` is a caller-saved
    temporary distinct from `x0`, `x12`, and `envBaseReg`.
    6 instructions = 24 bytes. -/
def evm_gas (envBaseReg tmpReg : Reg) : Program :=
  ADDI .x12 .x12 (-32) ;;
  LD tmpReg envBaseReg (BitVec.ofNat 12 gasRemainingOff) ;;
  SD .x12 tmpReg 0 ;;
  SD .x12 .x0 8 ;;
  SD .x12 .x0 16 ;;
  SD .x12 .x0 24

abbrev evm_gas_code (envBaseReg tmpReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_gas envBaseReg tmpReg)

/-- `evm_gas` is exactly 6 RISC-V instructions = 24 bytes. -/
theorem evm_gas_length (envBaseReg tmpReg : Reg) :
    (evm_gas envBaseReg tmpReg).length = 6 := by
  simp [evm_gas, LD, ADDI, SD, single, seq, Program.length_append]

theorem evm_gas_byte_length (envBaseReg tmpReg : Reg) :
    4 * (evm_gas envBaseReg tmpReg).length = 24 := by
  rw [evm_gas_length]

end GasOpcode
end EvmAsm.Evm64
