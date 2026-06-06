/-
  EvmAsm.Evm64.Code.CopyProgram

  RISC-V program implementing the EVM `CODECOPY` opcode for the codegen
  runtime interpreter.

  CODECOPY pops `(destOffset, dataOffset, size)` and copies `size` bytes of
  the *currently executing* bytecode `code[dataOffset .. dataOffset+size)`
  into EVM memory at `memory[destOffset ..]`, zero-filling any source byte
  at or beyond `len(code)`.

  This is the sibling of `Calldata.evm_calldatacopy`; the only differences
  are the source region and its length:

    - source base   : caller-supplied `codeBaseReg` (the dispatcher's
                       preserved code-base register `x21`), instead of
                       `env.callDataPtr`.
    - source length : `env.codeSize` at `env + 496` (the M33 cell the
                       dispatcher prologue seeds with the running bytecode
                       length), instead of `env.callDataLen`.

  The loop body (the trailing 10 instructions) is byte-for-byte identical to
  `evm_calldatacopy`, including the PC-relative branch offsets, so the same
  zero-fill semantics apply.

  18 instructions = 72 bytes.

  Register convention (all caller-saved temporaries per LP64):
    `envBaseReg`  — environment-block base (`x20`); only `env+496` is read.
    `memBaseReg`  — EVM memory buffer base (`x13`).
    `codeBaseReg` — running-bytecode base (`x21`); never written.
    `destReg`     — destOffset low limb → running absolute dest pointer.
    `srcReg`      — dataOffset low limb → running absolute source pointer.
    `cntReg`      — size low limb; loop guard, decremented each iteration.
    `endReg`      — `codeBase + codeSize` (one past the last in-bounds byte).
    `byteReg`     — per-iteration scratch byte.

  Only the low limb of each popped word is read (matching the MSTORE /
  CALLDATACOPY conventions). Memory-expansion (`evmMemSizeIs`) bookkeeping is
  handled by the handler `preBody` (`updateActiveMemorySizeAsm`), not here —
  same arrangement as `Calldata.evm_calldatacopy`.
-/

import EvmAsm.Evm64.Code.Basic
import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64
namespace Code

open EvmAsm.Rv64

/-- Top-level RISC-V program implementing the EVM `CODECOPY` opcode. See the
    file header for the stack convention, register roles, and the byte-by-byte
    loop layout (shared with `Calldata.evm_calldatacopy`).

    18 instructions = 72 bytes. -/
def evm_codecopy
    (envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg
      byteReg : Reg) : Program :=
  -- Preamble: pop 3 stack words and compute absolute pointers.
  LD destReg .x12 0 ;;
  LD srcReg  .x12 32 ;;
  LD cntReg  .x12 64 ;;
  ADDI .x12 .x12 (BitVec.ofNat 12 96) ;;
  LD endReg envBaseReg (BitVec.ofNat 12 codeSizeOff) ;;   -- endReg := len(code)
  ADD endReg endReg codeBaseReg ;;                         -- endReg := codeBase + len
  ADD destReg memBaseReg destReg ;;                        -- dest := memBase + destOff
  ADD srcReg codeBaseReg srcReg ;;                         -- src  := codeBase + srcOff
  -- Loop body (identical to evm_calldatacopy).
  single (.BEQ cntReg .x0 (BitVec.ofNat 13 40)) ;;
  single (.BGEU srcReg endReg (BitVec.ofNat 13 12)) ;;
  LBU byteReg srcReg 0 ;;
  single (.JAL .x0 (BitVec.ofNat 21 8)) ;;
  ADDI byteReg .x0 0 ;;
  SB destReg byteReg 0 ;;
  ADDI srcReg srcReg 1 ;;
  ADDI destReg destReg 1 ;;
  ADDI cntReg cntReg (-1 : BitVec 12) ;;
  single (.JAL .x0 (-36 : BitVec 21))

/-- `CodeReq` for `evm_codecopy` placed at `base`. -/
abbrev evm_codecopy_code
    (envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg
      byteReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_codecopy envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg
      endReg byteReg)

/-- `evm_codecopy` is exactly 18 RISC-V instructions. -/
theorem evm_codecopy_length
    (envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg
      byteReg : Reg) :
    (evm_codecopy envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg
        endReg byteReg).length = 18 := by
  simp [evm_codecopy, LD, ADDI, ADD, LBU, SB, single, seq,
    Program.length_append]

/-- `evm_codecopy` occupies 72 bytes in RV64 code memory. -/
theorem evm_codecopy_byte_length
    (envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg
      byteReg : Reg) :
    4 * (evm_codecopy envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg
        endReg byteReg).length = 72 := by
  rw [evm_codecopy_length]

end Code
end EvmAsm.Evm64
