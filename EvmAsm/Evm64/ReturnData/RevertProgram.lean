/-
  EvmAsm.Evm64.ReturnData.RevertProgram

  RISC-V program image of the EVM `RETURNDATACOPY` (0x3e) handler's
  bounds-check / revert prefix. This prefix is the opcode-specific behavior
  CALLDATACOPY/CODECOPY do not have: RETURNDATACOPY routes to `.exit_invalid`
  when `start + size` wraps or exceeds the stored return-data length. (The old
  256-byte `evm_precompile_frame` cap guard was dropped in #10160 once the guest
  staged the full child return data, so `start + size ≤ retlen` alone keeps the
  copy loop inside the staged bytes.)

  Layout (9 instructions = 36 bytes), byte offsets relative to the prefix:

     +0   LD    x14 x12 0
     +4   LD    x15 x12 32
     +8   LD    x16 x12 64
     +12  AUIPC x17 frameHi
     +16  ADDI  x17 x17 frameLo
     +20  LD    x18 x17 8
     +24  ADD   x19 x15 x16
     +28  BLTU  x19 x15 off1
     +32  BLTU  x18 x19 off2
     +36  fall-through to memory-gas / copy glue
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64
namespace ReturnData

open EvmAsm.Rv64

/-- Bounds-check / revert prefix of the emitted `h_RETURNDATACOPY` handler. -/
def evm_returndatacopy_revert
    (frameHi : BitVec 20) (frameLo : BitVec 12)
    (off1 off2 : BitVec 13) : Program :=
  LD .x14 .x12 0 ;;
  LD .x15 .x12 (BitVec.ofNat 12 32) ;;
  LD .x16 .x12 (BitVec.ofNat 12 64) ;;
  single (.AUIPC .x17 frameHi) ;;
  ADDI .x17 .x17 frameLo ;;
  LD .x18 .x17 (BitVec.ofNat 12 8) ;;
  ADD .x19 .x15 .x16 ;;
  single (.BLTU .x19 .x15 off1) ;;
  single (.BLTU .x18 .x19 off2)

/-- `CodeReq` for the RETURNDATACOPY revert prefix placed at `base`. -/
abbrev evm_returndatacopy_revert_code
    (frameHi : BitVec 20) (frameLo : BitVec 12) (off1 off2 : BitVec 13)
    (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_returndatacopy_revert frameHi frameLo off1 off2)

/-- The RETURNDATACOPY bounds prefix is exactly 9 RISC-V instructions. -/
theorem evm_returndatacopy_revert_length
    (frameHi : BitVec 20) (frameLo : BitVec 12) (off1 off2 : BitVec 13) :
    (evm_returndatacopy_revert frameHi frameLo off1 off2).length = 9 := by
  simp [evm_returndatacopy_revert, LD, ADDI, ADD, single, seq,
    Program.length_append]

/-- The RETURNDATACOPY bounds prefix occupies 36 bytes in RV64 code memory. -/
theorem evm_returndatacopy_revert_byte_length
    (frameHi : BitVec 20) (frameLo : BitVec 12) (off1 off2 : BitVec 13) :
    4 * (evm_returndatacopy_revert frameHi frameLo off1 off2).length = 36 := by
  rw [evm_returndatacopy_revert_length]

end ReturnData
end EvmAsm.Evm64
