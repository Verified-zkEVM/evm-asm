/-
  EvmAsm.Evm64.Calldata.LoadFullProgram

  Full bounds-checked RISC-V program for the EVM `CALLDATALOAD` opcode
  (GH #104): the verified replacement for the hand-written staging-loop
  handler.  Wraps the in-bounds byte-window core
  (`evm_calldataload_window`, program-identical to MLOAD) in a runtime
  out-of-bounds dispatch, under the padded-region contract
  (`Calldata.calldataRegionIs` — calldata bytes backed in memory with a
  32-zero-byte tail, so any window starting in bounds is fully
  cell-backed and the straddle case `offset < len < offset + 32` needs
  no partial-fill arm).

  Stack convention: CALLDATALOAD pops one EVM word (the 256-bit offset,
  at `x12 + 0..31`) and pushes one word (the loaded 32 bytes) to the
  same slot; the EVM stack pointer `x12` is unchanged.

  Layout (111 instructions = 444 bytes):

    Dispatch (12 instructions, bytes 0..47):
      [0]  LD    cdpReg  envBaseReg 416   -- env.callDataPtr
      [1]  LD    lenReg  envBaseReg 424   -- env.callDataLen
      [2]  LD    flagReg x12 8            -- offset limb 1
      [3]  LD    tmpReg  x12 16           -- offset limb 2
      [4]  OR    flagReg flagReg tmpReg
      [5]  LD    tmpReg  x12 24           -- offset limb 3
      [6]  OR    flagReg flagReg tmpReg   -- flag = l1 | l2 | l3
      [7]  LD    tmpReg  x12 0            -- offset low limb
      [8]  SLTU  tmpReg  tmpReg lenReg    -- (off_lo <u len) ? 1 : 0
      [9]  SLTIU tmpReg  tmpReg 1         -- seqz: (off_lo ≥u len) ? 1 : 0
      [10] OR    flagReg flagReg tmpReg   -- flag ≠ 0 ⟺ out of bounds
      [11] BNE   flagReg x0 +384          -- OOB → zero arm (byte 428)

    Window arm (95 instructions, bytes 48..427):
      [12..105] evm_calldataload_window offReg byteReg accReg addrReg cdpReg
                (94 instructions = 376 bytes; re-loads the low offset
                limb from `x12 + 0` itself, packs the big-endian
                32-byte window at `cdpReg + off_lo`, stores the result
                to the stack slot)
      [106] JAL x0 +20                    -- byte 424 → exit (byte 444)

    Zero arm (4 instructions, bytes 428..443):
      [107] SD x12 x0 0                   -- result := 0 (all four limbs)
      [108] SD x12 x0 8
      [109] SD x12 x0 16
      [110] SD x12 x0 24
      -- falls through to the exit at byte 444

  Branch offsets are relative to the branch instruction's PC, in bytes:
    [11]  BNE zero arm:  428 − 44 = 384   (fits BitVec 13: |384| < 4096)
    [106] JAL exit:      444 − 424 = 20   (fits BitVec 21)

  Register roles (all caller-saved temporaries; the spec slices pin
  down distinctness side conditions):

    `envBaseReg` — environment-block base address.
    `offReg` / `byteReg` / `accReg` / `addrReg`
                 — the window core's scratch (offset, byte, accumulator,
                   source address), as in `evm_calldataload_window`.
    `cdpReg`     — `env.callDataPtr`; doubles as the window core's base
                   pointer register.
    `lenReg`     — `env.callDataLen`.
    `flagReg`    — OOB dispatch flag (OR-reduced upper limbs + bound bit).
    `tmpReg`     — dispatch scratch.

  Intended handler instantiation (Codegen dispatcher swap):
    `evm_calldataload .x20 .x15 .x16 .x17 .x18 .x14 .x5 .x28 .x29`.

  This slice is **program-only** — the dispatch/arm/merge specs land in
  the follow-up slices.
-/

import EvmAsm.Evm64.Calldata.LoadProgram
import EvmAsm.Evm64.Environment.Layout

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64
open EvmAsm.Evm64.EvmEnv (callDataPtrOff callDataLenOff)

/-- OOB dispatch block of the full CALLDATALOAD program: load
    `callDataPtr`/`callDataLen`, OR-reduce the three upper offset limbs
    with the `off_lo ≥u len` bit into `flagReg`, and branch to the zero
    arm when the flag is nonzero.  12 instructions = 48 bytes. -/
def evm_calldataload_dispatch
    (envBaseReg cdpReg lenReg flagReg tmpReg : Reg) : Program :=
  LD cdpReg envBaseReg (BitVec.ofNat 12 callDataPtrOff) ;;
  LD lenReg envBaseReg (BitVec.ofNat 12 callDataLenOff) ;;
  LD flagReg .x12 8 ;;
  LD tmpReg .x12 16 ;;
  OR' flagReg flagReg tmpReg ;;
  LD tmpReg .x12 24 ;;
  OR' flagReg flagReg tmpReg ;;
  LD tmpReg .x12 0 ;;
  SLTU tmpReg tmpReg lenReg ;;
  SLTIU tmpReg tmpReg 1 ;;
  OR' flagReg flagReg tmpReg ;;
  single (.BNE flagReg .x0 (BitVec.ofNat 13 384))

/-- Zero arm of the full CALLDATALOAD program: write the zero word to
    the popped stack slot in place.  4 instructions = 16 bytes. -/
def evm_calldataload_zero_arm : Program :=
  SD .x12 .x0 0 ;;
  SD .x12 .x0 8 ;;
  SD .x12 .x0 16 ;;
  SD .x12 .x0 24

/-- Full bounds-checked CALLDATALOAD program.  See the file header for
    the layout, branch-offset arithmetic, and register roles.
    111 instructions = 444 bytes. -/
def evm_calldataload
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg) : Program :=
  evm_calldataload_dispatch envBaseReg cdpReg lenReg flagReg tmpReg ;;
  evm_calldataload_window offReg byteReg accReg addrReg cdpReg ;;
  single (.JAL .x0 (BitVec.ofNat 21 20)) ;;
  evm_calldataload_zero_arm

/-- `CodeReq` for `evm_calldataload` placed at `base`. -/
abbrev evm_calldataload_code
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_calldataload envBaseReg offReg byteReg accReg addrReg cdpReg
      lenReg flagReg tmpReg)

/-! ## Block byte offsets (with drift checks) -/

/-- Byte offset of the window arm within `evm_calldataload`. -/
abbrev calldataloadWindowOff : Nat := 48

/-- Byte offset of the zero arm within `evm_calldataload`. -/
abbrev calldataloadZeroArmOff : Nat := 428

/-- Byte offset of the common exit (one past the program). -/
abbrev calldataloadExitOff : Nat := 444

/-! ### Lengths -/

theorem evm_calldataload_dispatch_length
    (envBaseReg cdpReg lenReg flagReg tmpReg : Reg) :
    (evm_calldataload_dispatch envBaseReg cdpReg lenReg flagReg
        tmpReg).length = 12 := by
  simp [evm_calldataload_dispatch, LD, OR', SLTU, SLTIU, single, seq,
    Program.length_append]

theorem evm_calldataload_zero_arm_length :
    evm_calldataload_zero_arm.length = 4 := by
  simp [evm_calldataload_zero_arm, SD, single, seq, Program.length_append]

/-- `evm_calldataload` is exactly 111 RISC-V instructions. -/
theorem evm_calldataload_length
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg) :
    (evm_calldataload envBaseReg offReg byteReg accReg addrReg cdpReg
        lenReg flagReg tmpReg).length = 111 := by
  simp [evm_calldataload, seq, Program.length_append,
    evm_calldataload_dispatch_length, evm_calldataload_zero_arm_length,
    evm_calldataload_window_program_length, single]

/-- `evm_calldataload` occupies 444 bytes in RV64 code memory. -/
theorem evm_calldataload_byte_length
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg) :
    4 * (evm_calldataload envBaseReg offReg byteReg accReg addrReg cdpReg
        lenReg flagReg tmpReg).length = 444 := by
  rw [evm_calldataload_length]

/-! ### Drift checks

    Tie the named byte offsets to the block lengths so a layout edit
    fails here rather than silently invalidating downstream address
    arithmetic (OPCODE_TEMPLATE §2.4). -/

example : calldataloadWindowOff =
    4 * (evm_calldataload_dispatch .x20 .x14 .x5 .x28 .x29).length := by
  rw [evm_calldataload_dispatch_length]

example : calldataloadZeroArmOff = calldataloadWindowOff +
    4 * (evm_calldataload_window .x15 .x16 .x17 .x18 .x14).length + 4 := by
  rw [evm_calldataload_window_program_length]

example : calldataloadExitOff = calldataloadZeroArmOff +
    4 * evm_calldataload_zero_arm.length := by
  rw [evm_calldataload_zero_arm_length]

example : calldataloadExitOff =
    4 * (evm_calldataload .x20 .x15 .x16 .x17 .x18 .x14 .x5 .x28
      .x29).length := by
  rw [evm_calldataload_length]

-- Branch-offset arithmetic: BNE (at byte 44) reaches the zero arm and
-- JAL (at byte 424) reaches the exit.
example : 44 + 384 = calldataloadZeroArmOff := by decide
example : (calldataloadWindowOff + 376) + 20 = calldataloadExitOff := by decide

/-! ## Executable sanity guards (concrete handler registers) -/

/-- Executable instruction lookup for the `#guard` sanity checks below
    (`Program` is a plain `def`, so the `GetElem` instances of `List`
    do not fire on it directly). -/
private def instrAt (p : Program) (k : Nat) : Option Instr :=
  (List.drop k p).head?

#guard (evm_calldataload .x20 .x15 .x16 .x17 .x18 .x14 .x5 .x28
    .x29).length = 111
#guard (evm_calldataload_dispatch .x20 .x14 .x5 .x28 .x29).length = 12
#guard evm_calldataload_zero_arm.length = 4
-- The BNE sits at instruction index 11 (byte 44) and targets byte 428.
#guard instrAt (evm_calldataload .x20 .x15 .x16 .x17 .x18 .x14 .x5 .x28
    .x29) 11 = some (Instr.BNE .x28 .x0 (BitVec.ofNat 13 384))
-- The window arm starts at index 12 (byte 48) with the window's
-- offset-load instruction.
#guard instrAt (evm_calldataload .x20 .x15 .x16 .x17 .x18 .x14 .x5 .x28
    .x29) 12 = instrAt (evm_calldataload_window .x15 .x16 .x17 .x18 .x14) 0
-- The JAL sits at index 106 (byte 424) and targets byte 444.
#guard instrAt (evm_calldataload .x20 .x15 .x16 .x17 .x18 .x14 .x5 .x28
    .x29) 106 = some (Instr.JAL .x0 (BitVec.ofNat 21 20))
-- The zero arm starts at index 107 (byte 428).
#guard instrAt (evm_calldataload .x20 .x15 .x16 .x17 .x18 .x14 .x5 .x28
    .x29) 107 = some (Instr.SD .x12 .x0 0)
#guard instrAt (evm_calldataload .x20 .x15 .x16 .x17 .x18 .x14 .x5 .x28
    .x29) 110 = some (Instr.SD .x12 .x0 24)

/-! ## Code subsumption lemmas

    The bridges the spec slices compose against: each block's own
    `CodeReq` (at its byte offset) is subsumed by the full program's
    code requirement. -/

/-- The dispatch block is the prefix of the full CALLDATALOAD code. -/
theorem evm_calldataload_dispatch_code_sub_full
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg) (base : Word) :
    ∀ a i,
      (CodeReq.ofProg base
        (evm_calldataload_dispatch envBaseReg cdpReg lenReg flagReg
          tmpReg)) a = some i →
      (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg base) a = some i := by
  exact CodeReq.ofProg_mono_sub base base
    (evm_calldataload envBaseReg offReg byteReg accReg addrReg cdpReg
      lenReg flagReg tmpReg)
    (evm_calldataload_dispatch envBaseReg cdpReg lenReg flagReg tmpReg)
    0
    (by simp)
    (by
      unfold evm_calldataload evm_calldataload_dispatch
      rfl)
    (by
      rw [evm_calldataload_dispatch_length, evm_calldataload_length]
      omega)
    (by
      rw [evm_calldataload_length]
      omega)

/-- The window arm (at `base + calldataloadWindowOff`) is subsumed by the
    full CALLDATALOAD code. -/
theorem evm_calldataload_window_code_sub_full
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg) (base : Word) :
    ∀ a i,
      (evm_calldataload_window_code offReg byteReg accReg addrReg cdpReg
        (base + BitVec.ofNat 64 calldataloadWindowOff)) a = some i →
      (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg base) a = some i := by
  exact CodeReq.ofProg_mono_sub base
    (base + BitVec.ofNat 64 calldataloadWindowOff)
    (evm_calldataload envBaseReg offReg byteReg accReg addrReg cdpReg
      lenReg flagReg tmpReg)
    (evm_calldataload_window offReg byteReg accReg addrReg cdpReg)
    12
    (by rfl)
    (by
      unfold evm_calldataload evm_calldataload_dispatch
      rfl)
    (by
      rw [evm_calldataload_window_program_length, evm_calldataload_length]
      omega)
    (by
      rw [evm_calldataload_length]
      omega)

/-- The zero arm (at `base + calldataloadZeroArmOff`) is subsumed by the
    full CALLDATALOAD code. -/
theorem evm_calldataload_zero_arm_code_sub_full
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg) (base : Word) :
    ∀ a i,
      (CodeReq.ofProg (base + BitVec.ofNat 64 calldataloadZeroArmOff)
        evm_calldataload_zero_arm) a = some i →
      (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg base) a = some i := by
  exact CodeReq.ofProg_mono_sub base
    (base + BitVec.ofNat 64 calldataloadZeroArmOff)
    (evm_calldataload envBaseReg offReg byteReg accReg addrReg cdpReg
      lenReg flagReg tmpReg)
    evm_calldataload_zero_arm
    107
    (by rfl)
    (by
      unfold evm_calldataload evm_calldataload_dispatch
        evm_calldataload_window evm_calldataload_zero_arm
      rfl)
    (by
      rw [evm_calldataload_zero_arm_length, evm_calldataload_length]
      omega)
    (by
      rw [evm_calldataload_length]
      omega)

/-- The BNE dispatch branch sits at `base + 44` in the full code. -/
theorem evm_calldataload_lookup_bne
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg) (base : Word) :
    (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg base) (base + 44) =
      some (.BNE flagReg .x0 (BitVec.ofNat 13 384)) := by
  exact CodeReq.ofProg_lookup_addr base
    (evm_calldataload envBaseReg offReg byteReg accReg addrReg cdpReg
      lenReg flagReg tmpReg)
    11 (base + 44)
    (by rw [evm_calldataload_length]; omega)
    (by rw [evm_calldataload_length]; omega)
    (by rfl)

/-- The window-arm exit JAL sits at `base + 424` in the full code. -/
theorem evm_calldataload_lookup_jal
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg) (base : Word) :
    (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg base) (base + 424) =
      some (.JAL .x0 (BitVec.ofNat 21 20)) := by
  exact CodeReq.ofProg_lookup_addr base
    (evm_calldataload envBaseReg offReg byteReg accReg addrReg cdpReg
      lenReg flagReg tmpReg)
    106 (base + 424)
    (by rw [evm_calldataload_length]; omega)
    (by rw [evm_calldataload_length]; omega)
    (by rfl)

end Calldata
end EvmAsm.Evm64
