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
import EvmAsm.Evm64.ReturnData.RevertProgram

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

/-! ## Pointer setup

    The block the emitted handler runs between the bounds guards and the copy
    loop: pop the three stack operands, take the size-zero skip, and materialize
    the running source/destination pointers.

    Layout (5 instructions = 20 bytes), byte offsets relative to the setup entry:

       +0   ADDI x12 x12 96      ; pop destOffset/dataOffset/size
       +4   BEQ  x16 x0 40       ; size == 0 → skip the loop (label `2:`)
       +8   ADDI x17 x17 16      ; x17 = frame + 16   (return-data window)
       +12  ADD  x17 x17 x15     ; x17 = frame + 16 + start
       +16  ADD  x18 x13 x14     ; x18 = memBase + destOffset
       +20  fall-through to the copy loop

    The emitted handler re-issues `la x17, evm_precompile_frame` here because the
    intervening dynamic-gas / MSIZE glue clobbers `x17`. That glue is framed out
    of this proof (the DRIFT TCB boundary CALLDATACOPY/CODECOPY also use), so in
    the idealized image `x17` still holds the frame address the guard prefix
    materialized and the reload is not modeled. -/
def evm_returndatacopy_setup : Program :=
  ADDI .x12 .x12 (BitVec.ofNat 12 96) ;;            -- +0
  single (.BEQ .x16 .x0 (BitVec.ofNat 13 40)) ;;    -- +4
  ADDI .x17 .x17 (BitVec.ofNat 12 16) ;;            -- +8
  ADD .x17 .x17 .x15 ;;                             -- +12
  ADD .x18 .x13 .x14                                -- +16

/-- `CodeReq` for `evm_returndatacopy_setup` placed at `base`. -/
abbrev evm_returndatacopy_setup_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_returndatacopy_setup

/-- `evm_returndatacopy_setup` is exactly 5 RISC-V instructions. -/
theorem evm_returndatacopy_setup_length :
    evm_returndatacopy_setup.length = 5 := by
  simp [evm_returndatacopy_setup, ADDI, ADD, single, seq, Program.length_append]

/-- `evm_returndatacopy_setup` occupies 20 bytes in RV64 code memory. -/
theorem evm_returndatacopy_setup_byte_length :
    4 * evm_returndatacopy_setup.length = 20 := by
  rw [evm_returndatacopy_setup_length]

/-! ## The RETURNDATACOPY body

    Bounds guards, pointer setup, and the copy loop as one contiguous image —
    the RETURNDATACOPY counterpart of `evm_calldatacopy`.  This is the scope the
    registered `.proven` witness covers; the dynamic-gas / OOG / MSIZE glue the
    handler interleaves is framed out (the DRIFT TCB boundary CALLDATACOPY,
    CODECOPY and MCOPY also use).

    Layout (20 instructions = 80 bytes):

       +0    bounds guards      (9 instrs, `RevertProgram`)
       +36   pointer setup      (5 instrs)
       +56   copy loop          (6 instrs)
       +80   exit (label `2:`, also the size-zero skip target) -/
def evm_returndatacopy
    (frameHi : BitVec 20) (frameLo : BitVec 12) (off1 off2 : BitVec 13) : Program :=
  evm_returndatacopy_revert frameHi frameLo off1 off2 ;;
  evm_returndatacopy_setup ;;
  evm_returndatacopy_loop .x18 .x17 .x16 .x19

/-- `CodeReq` for the whole RETURNDATACOPY body placed at `base`. -/
abbrev evm_returndatacopy_code
    (frameHi : BitVec 20) (frameLo : BitVec 12) (off1 off2 : BitVec 13)
    (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_returndatacopy frameHi frameLo off1 off2)

/-- The RETURNDATACOPY body is exactly 20 RISC-V instructions. -/
theorem evm_returndatacopy_length
    (frameHi : BitVec 20) (frameLo : BitVec 12) (off1 off2 : BitVec 13) :
    (evm_returndatacopy frameHi frameLo off1 off2).length = 20 := by
  simp [evm_returndatacopy, seq, Program.length_append,
    evm_returndatacopy_revert_length, evm_returndatacopy_setup_length,
    evm_returndatacopy_loop_length]

/-- The RETURNDATACOPY body occupies 80 bytes in RV64 code memory. -/
theorem evm_returndatacopy_byte_length
    (frameHi : BitVec 20) (frameLo : BitVec 12) (off1 off2 : BitVec 13) :
    4 * (evm_returndatacopy frameHi frameLo off1 off2).length = 80 := by
  rw [evm_returndatacopy_length]

end ReturnData
end EvmAsm.Evm64
