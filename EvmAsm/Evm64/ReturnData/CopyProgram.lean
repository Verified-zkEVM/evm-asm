/-
  EvmAsm.Evm64.ReturnData.CopyProgram

  RISC-V program implementing the copy loop of the EVM `RETURNDATACOPY` opcode
  (0x3e; see `EvmAsm/Codegen/Programs/NoopReturnData.lean`, `h_RETURNDATACOPY`).

  Unlike CALLDATACOPY/CODECOPY (which zero-fill out-of-range source bytes),
  RETURNDATACOPY **reverts** (`OutOfBoundsRead`) when `start + size >
  len(return_data)` — so the emitted handler bounds-checks up front and then runs
  an **unconditional** in-bounds byte copy (no zero-fill arm). The source is the
  runtime `evm_precompile_frame` (return-data bytes at `frame+16`, length at
  `frame+8`, 256-byte cap); the destination is EVM memory.

  This program is the **la-free copy loop** (handler labels `1:`→`2:`), a
  bottom-tested `do { copy byte; advance; dec } while (cnt != 0)`. The size-zero
  skip (`beqz x16, 2f`), the symbolic `la evm_precompile_frame` + pointer setup,
  the `start+size > retlen` revert guard, the 256-byte cap, and the dynamic-gas /
  MSIZE bookkeeping stay in the handler `preBody`/glue (unverified per DRIFT,
  exactly as CALLDATACOPY/CODECOPY carry their gas/MSIZE glue). The loop spec
  therefore covers `size ≥ 1` (size = 0 is the glue `beqz` skip).

  Register roles (matching the emitted handler):
    `srcReg`     (x17) — running source pointer (`frame+16+start`, then +i).
    `dstReg`     (x18) — running destination pointer (`memBase+destOffset`, +i).
    `cntReg`     (x16) — remaining byte count, decremented each iteration.
    `scratchReg` (x19) — per-iteration byte scratch.

  Layout (6 instructions = 24 bytes), byte offsets relative to the loop entry.
  Verified byte-identical against `riscv64-elf-as` + `objdump`:

     +0   LBU  scratch src 0
     +4   SB   dst scratch 0
     +8   ADDI src src 1
     +12  ADDI dst dst 1
     +16  ADDI cnt cnt -1
     +20  BNE  cnt x0 -20         ; cnt != 0 → back to +0
     +24  (exit; label 2:)
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64
namespace ReturnData

open EvmAsm.Rv64

/-- Copy loop of the EVM `RETURNDATACOPY` opcode (bottom-tested `do..while`).
    See the file header for register roles and the byte layout.

    6 instructions = 24 bytes. -/
def evm_returndatacopy_loop
    (dstReg srcReg cntReg scratchReg : Reg) : Program :=
  LBU scratchReg srcReg 0 ;;                     -- +0
  SB dstReg scratchReg 0 ;;                      -- +4
  ADDI srcReg srcReg 1 ;;                        -- +8
  ADDI dstReg dstReg 1 ;;                        -- +12
  ADDI cntReg cntReg (-1 : BitVec 12) ;;         -- +16
  single (.BNE cntReg .x0 (-20 : BitVec 13))     -- +20 → +0

/-- `CodeReq` for `evm_returndatacopy_loop` placed at `base`. -/
abbrev evm_returndatacopy_loop_code
    (dstReg srcReg cntReg scratchReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_returndatacopy_loop dstReg srcReg cntReg scratchReg)

/-- `evm_returndatacopy_loop` is exactly 6 RISC-V instructions. -/
theorem evm_returndatacopy_loop_length
    (dstReg srcReg cntReg scratchReg : Reg) :
    (evm_returndatacopy_loop dstReg srcReg cntReg scratchReg).length = 6 := by
  simp [evm_returndatacopy_loop, LBU, SB, ADDI, single, seq, Program.length_append]

/-- `evm_returndatacopy_loop` occupies 24 bytes in RV64 code memory. -/
theorem evm_returndatacopy_loop_byte_length
    (dstReg srcReg cntReg scratchReg : Reg) :
    4 * (evm_returndatacopy_loop dstReg srcReg cntReg scratchReg).length = 24 := by
  rw [evm_returndatacopy_loop_length]

end ReturnData
end EvmAsm.Evm64
