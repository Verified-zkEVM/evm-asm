/-
  EvmAsm.Evm64.Calldata.StageProgram

  The ARENA-FREE (staged) CALLDATALOAD program (bead evm-asm-t1iqb, phase B).

  Rather than trusting a 32-byte zero pad on the (aliased, unpadded) calldata
  region — which #9871 established with a 16 MiB per-frame copy arena — this
  materializes the 32-byte CALLDATALOAD window into a small fixed staging
  buffer with a per-byte out-of-bounds zero-fill, then re-runs the verified
  window ladder over that buffer at offset 0.  No arena, no per-frame copy,
  no overflow flag: the straddle / out-of-bounds cases are handled by the
  copy's own zero-fill, so the real calldata region needs no pad.

  Registers (concrete, matching the dispatcher handler; `x14` = staging buffer
  base is set by `la x14, bv_cdl_stage` glue in the handler preBody, `x20` =
  env base, `x12` = EVM stack pointer):

    x5  cdpReal   — env.callDataPtr (real calldata base)
    x6  len/end   — env.callDataLen, then repurposed to `cdp + len` (end ptr)
    x7  offLo     — offset low limb, normalized to `len` on the skip path
    x28 flag/byte — OOB skip flag (setup), then per-iteration byte (loop)
    x29 cnt       — 32-countdown loop counter
    x30 src/tmp   — running source pointer / setup scratch
    x31 dst       — running destination pointer into the buffer
    x14 bufReg    — staging buffer base (preserved for the window read)

  Layout (27 instructions = 108 bytes staging, then the 94-instruction window):

    setup (17 instrs, bytes 0..67):
      [0]  LD    x5  x20 416     -- cdpReal
      [1]  LD    x6  x20 424     -- len
      [2]  LD    x7  x12 0       -- offset low limb
      [3]  LD    x28 x12 8       -- offset limb 1
      [4]  LD    x30 x12 16      -- offset limb 2
      [5]  OR    x28 x28 x30
      [6]  LD    x30 x12 24      -- offset limb 3
      [7]  OR    x28 x28 x30     -- x28 = limb1 | limb2 | limb3
      [8]  SLTU  x30 x7  x6      -- offLo <u len
      [9]  SLTIU x30 x30 1       -- offLo >=u len  (seqz)
      [10] OR    x28 x28 x30     -- x28 = skip-all flag
      [11] BEQ   x28 x0 +8       -- flag == 0 -> keep offLo
      [12] ADDI  x7  x6  0       -- flag != 0 -> offLo := len (force all OOB)
      [13] ADD   x30 x5  x7      -- srcPtr = cdp + offLo(normalized)
      [14] ADD   x6  x5  x6      -- endPtr = cdp + len
      [15] ADDI  x31 x14 0       -- dstPtr = buf
      [16] ADDI  x29 x0  32      -- cnt = 32

    copy loop (9 instrs, bytes 68..103; loop_top = byte 68):
      [17] BEQ   x29 x0 +36      -- cnt == 0 -> done
      [18] ADDI  x28 x0  0       -- byte = 0 (default pad)
      [19] BGEU  x30 x6 +8       -- srcPtr >= end -> keep 0 (OOB)
      [20] LBU   x28 x30 0       -- byte = cdp[srcPtr]
      [21] SB    x31 x28 0       -- buf[dst] = byte
      [22] ADDI  x30 x30 1       -- srcPtr++
      [23] ADDI  x31 x31 1       -- dstPtr++
      [24] ADDI  x29 x29 -1      -- cnt--
      [25] JAL   x0 -32          -- back to loop_top

    finalize (1 instr, bytes 104..107):
      [26] SD    x12 x0 0        -- offset low limb := 0 (window reads buf+0)

  Branch offsets (relative to the branch PC, in bytes):
    [11] BEQ  +8   : 52 − 44 = 8      (skip [12])
    [17] BEQ  +36  : 104 − 68 = 36    (loop_top -> done)
    [19] BGEU +8   : 84 − 76 = 8      (skip [20])
    [25] JAL  −32  : 68 − 100 = −32   (back to loop_top)
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic
import EvmAsm.Evm64.Calldata.LoadProgram
import EvmAsm.Evm64.Environment.Layout

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64
open EvmAsm.Evm64.EvmEnv (callDataPtrOff callDataLenOff)

/-- Setup + copy-loop + finalize staging block (27 instructions).  Reads the
    real calldata pointer/length and the offset, normalizes the source offset
    for the all-OOB case, copies the 32-byte window into the buffer with
    per-byte zero-fill, and zeroes the offset low-limb stack cell so the
    following window read starts at buffer offset 0. -/
def evm_calldataload_stage : Program :=
  -- setup
  LD .x5 .x20 (BitVec.ofNat 12 callDataPtrOff) ;;
  LD .x6 .x20 (BitVec.ofNat 12 callDataLenOff) ;;
  LD .x7 .x12 0 ;;
  LD .x28 .x12 8 ;;
  LD .x30 .x12 16 ;;
  OR' .x28 .x28 .x30 ;;
  LD .x30 .x12 24 ;;
  OR' .x28 .x28 .x30 ;;
  SLTU .x30 .x7 .x6 ;;
  SLTIU .x30 .x30 1 ;;
  OR' .x28 .x28 .x30 ;;
  single (.BEQ .x28 .x0 (BitVec.ofNat 13 8)) ;;
  ADDI .x7 .x6 0 ;;
  ADD .x30 .x5 .x7 ;;
  ADD .x6 .x5 .x6 ;;
  ADDI .x31 .x14 0 ;;
  ADDI .x29 .x0 (BitVec.ofNat 12 32) ;;
  -- loop
  single (.BEQ .x29 .x0 (BitVec.ofNat 13 36)) ;;
  ADDI .x28 .x0 0 ;;
  single (.BGEU .x30 .x6 (BitVec.ofNat 13 8)) ;;
  LBU .x28 .x30 0 ;;
  SB .x31 .x28 0 ;;
  ADDI .x30 .x30 1 ;;
  ADDI .x31 .x31 1 ;;
  ADDI .x29 .x29 (-1 : BitVec 12) ;;
  single (.JAL .x0 (-32 : BitVec 21)) ;;
  -- finalize
  SD .x12 .x0 0

/-- The full arena-free CALLDATALOAD program: staging block followed by the
    (program-identical to MLOAD) 32-byte window read at buffer offset 0, with
    `x14` as the buffer base and `x15..x18` the window scratch. -/
def evm_calldataload_staged : Program :=
  evm_calldataload_stage ;;
  evm_calldataload_window .x15 .x16 .x17 .x18 .x14

/-- `CodeReq` for `evm_calldataload_staged` at `base`. -/
abbrev evm_calldataload_staged_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_calldataload_staged

theorem evm_calldataload_stage_length :
    evm_calldataload_stage.length = 27 := by
  simp [evm_calldataload_stage, LD, OR', SLTU, SLTIU, ADDI, ADD, LBU, SB, SD,
    single, seq, Program.length_append]

theorem evm_calldataload_staged_length :
    evm_calldataload_staged.length = 121 := by
  simp [evm_calldataload_staged, seq, Program.length_append,
    evm_calldataload_stage_length, evm_calldataload_window_program_length]

theorem evm_calldataload_staged_byte_length :
    4 * evm_calldataload_staged.length = 484 := by
  rw [evm_calldataload_staged_length]

/-- Executable instruction lookup for the `#guard` sanity checks. -/
private def instrAt (p : Program) (k : Nat) : Option Instr :=
  (List.drop k p).head?

-- Structural pins (a layout edit fails here rather than silently downstream).
#guard evm_calldataload_stage.length = 27
#guard evm_calldataload_staged.length = 121
-- loop guard BEQ at index 17 (byte 68), targets done (byte 104): +36
#guard instrAt evm_calldataload_staged 17 = some (Instr.BEQ .x29 .x0 (BitVec.ofNat 13 36))
-- the OOB BGEU at index 19 (byte 76), skips the LBU: +8
#guard instrAt evm_calldataload_staged 19 = some (Instr.BGEU .x30 .x6 (BitVec.ofNat 13 8))
-- the back-edge JAL at index 25 (byte 100), targets loop_top (byte 68): -32
#guard instrAt evm_calldataload_staged 25 = some (Instr.JAL .x0 (-32 : BitVec 21))
-- the finalize SD at index 26 (byte 104)
#guard instrAt evm_calldataload_staged 26 = some (Instr.SD .x12 .x0 0)
-- the window read starts at index 27 (byte 108)
#guard instrAt evm_calldataload_staged 27 = instrAt (evm_calldataload_window .x15 .x16 .x17 .x18 .x14) 0

end Calldata
end EvmAsm.Evm64
