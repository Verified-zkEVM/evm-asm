/-
  EvmAsm.Evm64.SignExtend

  256-bit EVM SIGNEXTEND as a 64-bit RISC-V program.
  SIGNEXTEND(b, x) pops b and x, pushes sign-extended x.
  If b >= 31, the result is x (unchanged).

  For b in 0..30:
    limb_idx = b / 8       (0..3, from LSB)
    shift_amount = 56 - (b%8)*8
    Sign bit at position b*8+7 in the 256-bit value.
    Within limb: SLL by shift_amount, SRA by shift_amount (sign-extends in place).
    Higher limbs filled with SRAI result, 63 (all-zeros or all-ones).

  Memory layout (before pop):
    sp+0..sp+24:  b (4 LE limbs)
    sp+32..sp+56: x (4 LE limbs, limb 0 = LSB at sp+32)

  Register allocation:
    x12 = EVM stack pointer
    x5  = temp (b value, then limb value)
    x6  = shift_amount
    x10 = temp (OR-reduce, dispatch, sign fill)

  Program layout (48 instructions = 192 bytes):
    Phase A (9 instrs, offset 0):    Check b >= 31
    Phase B (5 instrs, offset 36):   Compute shift_amount and limb_idx
    Phase C (5 instrs, offset 56):   Cascade dispatch on limb_idx
    body_3 (5 instrs, offset 76):    Sign-extend limb 3, JAL to done
    body_2 (7 instrs, offset 96):    Sign-extend limb 2, fill limb 3, JAL
    body_1 (8 instrs, offset 124):   Sign-extend limb 1, fill limbs 2-3, JAL
    body_0 (8 instrs, offset 156):   Sign-extend limb 0, fill limbs 1-3
    done   (1 instr,  offset 188):   ADDI x12, x12, 32 (pop b)
    Exit point: offset 192
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Sub-program definitions
-- ============================================================================

/-- Phase A: Check b >= 31 (9 instructions).
    OR-reduce b limbs 1-3. BNE to done if nonzero.
    Then check b[0] < 31. BEQ to done if not. -/
def signext_phase_a : Program :=
  LD .x5  .x12 8  ;;                          -- x5  = b[1]
  LD .x10 .x12 16 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= b[2]
  LD .x10 .x12 24 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= b[3]
  single (.BNE .x5 .x0 168) ;;               -- high limbs nonzero → done (188-20=168)
  LD .x5  .x12 0  ;;                          -- x5 = b[0]
  single (.SLTIU .x10 .x5 31) ;;             -- x10 = (b[0] < 31)
  single (.BEQ .x10 .x0 156)                  -- b[0] >= 31 → done (188-32=156)

/-- Phase B: Compute shift_amount and limb_idx (5 instructions).
    shift_amount = 56 - (b%8)*8, stored in x6.
    limb_idx = b/8, stored in x5. -/
def signext_phase_b : Program :=
  single (.ANDI .x10 .x5 7) ;;               -- x10 = b % 8
  single (.SLLI .x10 .x10 3) ;;              -- x10 = (b % 8) * 8
  ADDI .x6 .x0 56 ;;                         -- x6 = 56
  single (.SUB .x6 .x6 .x10) ;;              -- x6 = 56 - (b%8)*8
  single (.SRLI .x5 .x5 3)                   -- x5 = b / 8

/-- Phase C: Cascade dispatch on limb_idx (5 instructions). -/
def signext_phase_c : Program :=
  single (.BEQ .x5 .x0 100) ;;              -- body_0 (156-56=100)
  ADDI .x10 .x0 1 ;;
  single (.BEQ .x5 .x10 60) ;;              -- body_1 (124-64=60)
  ADDI .x10 .x0 2 ;;
  single (.BEQ .x5 .x10 24)                 -- body_2 (96-72=24)

/-- body_3: limb_idx=3, sign-extend limb 3 at sp+56 (5 instrs).
    No higher limbs to fill. -/
def signext_body_3 : Program :=
  LD .x5 .x12 56 ;;                          -- load x[3]
  single (.SLL .x5 .x5 .x6) ;;              -- shift left
  single (.SRA .x5 .x5 .x6) ;;              -- arithmetic shift right (sign-extends)
  SD .x12 .x5 56 ;;                          -- store modified x[3]
  single (.JAL .x0 96)                       -- done (188-92=96)

/-- body_2: limb_idx=2, sign-extend limb 2, fill limb 3 (7 instrs). -/
def signext_body_2 : Program :=
  LD .x5 .x12 48 ;;                          -- load x[2]
  single (.SLL .x5 .x5 .x6) ;;
  single (.SRA .x5 .x5 .x6) ;;
  SD .x12 .x5 48 ;;                          -- store modified x[2]
  single (.SRAI .x10 .x5 63) ;;             -- sign fill value
  SD .x12 .x10 56 ;;                         -- fill x[3]
  single (.JAL .x0 68)                       -- done (188-120=68)

/-- body_1: limb_idx=1, sign-extend limb 1, fill limbs 2-3 (8 instrs). -/
def signext_body_1 : Program :=
  LD .x5 .x12 40 ;;                          -- load x[1]
  single (.SLL .x5 .x5 .x6) ;;
  single (.SRA .x5 .x5 .x6) ;;
  SD .x12 .x5 40 ;;                          -- store modified x[1]
  single (.SRAI .x10 .x5 63) ;;             -- sign fill value
  SD .x12 .x10 48 ;; SD .x12 .x10 56 ;;    -- fill x[2], x[3]
  single (.JAL .x0 36)                       -- done (188-152=36)

/-- body_0: limb_idx=0, sign-extend limb 0, fill limbs 1-3 (8 instrs).
    Falls through to done. -/
def signext_body_0 : Program :=
  LD .x5 .x12 32 ;;                          -- load x[0]
  single (.SLL .x5 .x5 .x6) ;;
  single (.SRA .x5 .x5 .x6) ;;
  SD .x12 .x5 32 ;;                          -- store modified x[0]
  single (.SRAI .x10 .x5 63) ;;             -- sign fill value
  SD .x12 .x10 40 ;; SD .x12 .x10 48 ;; SD .x12 .x10 56  -- fill x[1], x[2], x[3]

/-- Parameterized inplace sign-extension (4 instructions). -/
def signext_inplace_prog (off : BitVec 12) : Program :=
  [.LD .x5 .x12 off, .SLL .x5 .x5 .x6, .SRA .x5 .x5 .x6, .SD .x12 .x5 off]

/-- Parameterized body_3: sign-extend limb 3 + JAL (5 instrs). -/
def signext_body_3_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 56, .SLL .x5 .x5 .x6, .SRA .x5 .x5 .x6, .SD .x12 .x5 56, .JAL .x0 jal_off]

/-- Parameterized body_2: sign-extend limb 2, fill limb 3 + JAL (7 instrs). -/
def signext_body_2_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 48, .SLL .x5 .x5 .x6, .SRA .x5 .x5 .x6, .SD .x12 .x5 48,
   .SRAI .x10 .x5 63, .SD .x12 .x10 56, .JAL .x0 jal_off]

/-- Parameterized body_1: sign-extend limb 1, fill limbs 2-3 + JAL (8 instrs). -/
def signext_body_1_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 40, .SLL .x5 .x5 .x6, .SRA .x5 .x5 .x6, .SD .x12 .x5 40,
   .SRAI .x10 .x5 63, .SD .x12 .x10 48, .SD .x12 .x10 56, .JAL .x0 jal_off]

/-- done: pop b word (1 instruction). -/
def signext_done : Program :=
  ADDI .x12 .x12 32

/-- LD/OR accumulator (2 instructions): LD x10 x12 off; OR x5 x5 x10. -/
def signext_ld_or_acc_prog (off : BitVec 12) : Program :=
  [.LD .x10 .x12 off, .OR .x5 .x5 .x10]

/-- Cascade step: ADDI x10,x0,k; BEQ x5,x10,off (2 instructions). -/
def signext_cascade_step_prog (k : BitVec 12) (offset : BitVec 13) : Program :=
  [.ADDI .x10 .x0 k, .BEQ .x5 .x10 offset]

-- ============================================================================
-- Full SIGNEXTEND program
-- ============================================================================

/-- 256-bit EVM SIGNEXTEND: binary (pop 2, push 1, sp += 32).
    SIGNEXTEND(b, x) = sign-extend x from byte b. 48 instructions total. -/
def evm_signextend : Program :=
  signext_phase_a ;;
  signext_phase_b ;;
  signext_phase_c ;;
  signext_body_3 ;; signext_body_2 ;; signext_body_1 ;; signext_body_0 ;;
  signext_done
  -- Exit: offset 192 (instruction 48)

-- ============================================================================
-- Instruction count verification
-- ============================================================================

/-- evm_signextend has exactly 48 instructions. -/
example : evm_signextend.length = 48 := by decide

-- ============================================================================
-- Test infrastructure
-- ============================================================================

/-- Create a test state for SIGNEXTEND with b and x on the stack. -/
def mkSignExtTestState (sp : Word)
    (b0 b1 b2 b3 : Word)  -- b limbs (LE)
    (x0 x1 x2 x3 : Word)  -- value limbs (LE)
    : MachineState where
  regs := fun r =>
    match r with
    | .x12 => sp
    | _    => 0
  mem := fun a =>
    if a == sp      then b0
    else if a == sp + 8  then b1
    else if a == sp + 16 then b2
    else if a == sp + 24 then b3
    else if a == sp + 32 then x0
    else if a == sp + 40 then x1
    else if a == sp + 48 then x2
    else if a == sp + 56 then x3
    else 0
  code := loadProgram 0 evm_signextend
  pc := 0

/-- Run evm_signextend and extract 4 result limbs. -/
def runSignExtResult (sp : Word)
    (b0 b1 b2 b3 : Word)
    (x0 x1 x2 x3 : Word)
    (steps : Nat) : Option (List Word) :=
  let s := mkSignExtTestState sp b0 b1 b2 b3 x0 x1 x2 x3
  match stepN steps s with
  | some s' =>
    let rsp := s'.getReg .x12
    some [s'.getMem rsp, s'.getMem (rsp + 8), s'.getMem (rsp + 16), s'.getMem (rsp + 24)]
  | none => none

/-- Run evm_signextend and check PC and x12. -/
def runSignExtCheck (sp : Word)
    (b0 b1 b2 b3 : Word)
    (x0 x1 x2 x3 : Word)
    (steps : Nat) : Option (Word × Word) :=
  let s := mkSignExtTestState sp b0 b1 b2 b3 x0 x1 x2 x3
  match stepN steps s with
  | some s' => some (s'.pc, s'.getReg .x12)
  | none => none

-- ============================================================================
-- Concrete tests via decide
-- ============================================================================

-- Step counts by path:
-- body_0 (b 0-7,   limb 0): 9+5+1+8+1 = 24 steps
-- body_1 (b 8-15,  limb 1): 9+5+3+8+1 = 26 steps
-- body_2 (b 16-23, limb 2): 9+5+5+7+1 = 27 steps
-- body_3 (b 24-30, limb 3): 9+5+5+5+1 = 25 steps
-- no_change (high limbs nonzero): 6+1 = 7 steps
-- no_change (b[0] >= 31): 9+1 = 10 steps

-- Test 1: SIGNEXTEND(0, 0x7F) = 0x7F (byte 0, positive, no sign extension)
/-- SIGNEXTEND(0, 0x7F): positive byte 0, result unchanged. -/
example : runSignExtResult 1024 0 0 0 0  0x7F 0 0 0  24 =
    some [0x7F, 0, 0, 0] := by decide

-- Test 2: SIGNEXTEND(0, 0x80) = sign-extends to all-ones upper
/-- SIGNEXTEND(0, 0x80): negative byte 0, sign extends to 256 bits. -/
example : runSignExtResult 1024 0 0 0 0  0x80 0 0 0  24 =
    some [0xFFFFFFFFFFFFFF80, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 3: SIGNEXTEND(0, 0xFF) = all-ones
/-- SIGNEXTEND(0, 0xFF): byte 0 = 0xFF, extends to -1. -/
example : runSignExtResult 1024 0 0 0 0  0xFF 0 0 0  24 =
    some [0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 4: SIGNEXTEND(1, 0x7FFF) = 0x7FFF (byte 1, positive)
/-- SIGNEXTEND(1, 0x7FFF): positive byte 1, result unchanged. -/
example : runSignExtResult 1024 1 0 0 0  0x7FFF 0 0 0  24 =
    some [0x7FFF, 0, 0, 0] := by decide

-- Test 5: SIGNEXTEND(1, 0x8000) = sign-extends from bit 15
/-- SIGNEXTEND(1, 0x8000): negative byte 1, sign extends. -/
example : runSignExtResult 1024 1 0 0 0  0x8000 0 0 0  24 =
    some [0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 6: SIGNEXTEND(7, x) where bit 63 of limb 0 is 0 — limbs 1-3 zeroed
/-- SIGNEXTEND(7, ...): positive bit 63, higher limbs zeroed. -/
example : runSignExtResult 1024 7 0 0 0  0x0102030405060708 0xAAAA 0xBBBB 0xCCCC  24 =
    some [0x0102030405060708, 0, 0, 0] := by decide

-- Test 7: SIGNEXTEND(7, x) where bit 63 of limb 0 is 1 — limbs 1-3 filled
/-- SIGNEXTEND(7, ...): negative bit 63, higher limbs set to all-ones. -/
example : runSignExtResult 1024 7 0 0 0  0x8102030405060708 0 0 0  24 =
    some [0x8102030405060708, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 8: SIGNEXTEND(8, x) — byte 8, limb 1, positive
/-- SIGNEXTEND(8, ...): byte 8, positive, x[0] unchanged. -/
example : runSignExtResult 1024 8 0 0 0  0xABCD 0x7F 0xEEEE 0xDDDD  26 =
    some [0xABCD, 0x7F, 0, 0] := by decide

-- Test 9: SIGNEXTEND(8, x) — byte 8, limb 1, negative
/-- SIGNEXTEND(8, ...): byte 8, negative, x[0] unchanged, upper filled. -/
example : runSignExtResult 1024 8 0 0 0  0xABCD 0xFF 0xEEEE 0xDDDD  26 =
    some [0xABCD, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 10: SIGNEXTEND(16, x) — byte 16, limb 2
/-- SIGNEXTEND(16, ...): byte 16, positive, x[0-1] unchanged. -/
example : runSignExtResult 1024 16 0 0 0  0x1111 0x2222 0x7F 0x3333  27 =
    some [0x1111, 0x2222, 0x7F, 0] := by decide

-- Test 11: SIGNEXTEND(30, x) — byte 30, limb 3, positive
/-- SIGNEXTEND(30, ...): byte 30, positive, x[3] unchanged. -/
example : runSignExtResult 1024 30 0 0 0  0x1111 0x2222 0x3333 0x007FFFFFFFFFFFFF  25 =
    some [0x1111, 0x2222, 0x3333, 0x007FFFFFFFFFFFFF] := by decide

-- Test 12: SIGNEXTEND(30, x) — byte 30, limb 3, negative
/-- SIGNEXTEND(30, ...): byte 30, negative, x[3] sign-extended in MSB. -/
example : runSignExtResult 1024 30 0 0 0  0x1111 0x2222 0x3333 0x0080000000000000  25 =
    some [0x1111, 0x2222, 0x3333, 0xFF80000000000000] := by decide

-- Test 13: SIGNEXTEND(31, x) = x (no change, b >= 31)
/-- SIGNEXTEND(31, ...): b=31, no change. -/
example : runSignExtResult 1024 31 0 0 0  0x1111 0x2222 0x3333 0x4444  10 =
    some [0x1111, 0x2222, 0x3333, 0x4444] := by decide

-- Test 14: SIGNEXTEND with high b limbs nonzero — no change
/-- SIGNEXTEND with large b: no change. -/
example : runSignExtResult 1024 0 1 0 0  0x80 0 0 0  7 =
    some [0x80, 0, 0, 0] := by decide

-- Test 15: Verify PC and sp are correct after execution
/-- After SIGNEXTEND(0, ...), PC = 192 and x12 = sp + 32. -/
example : runSignExtCheck 1024 0 0 0 0  0x7F 0 0 0  24 =
    some (192, 1056) := by decide

/-- After SIGNEXTEND(31, ...), PC = 192 and x12 = sp + 32. -/
example : runSignExtCheck 1024 31 0 0 0  0xFF 0 0 0  10 =
    some (192, 1056) := by decide

end EvmAsm.Evm64
