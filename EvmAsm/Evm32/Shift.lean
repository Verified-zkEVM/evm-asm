/-
  EvmAsm.Evm32.Shift

  256-bit EVM SHR (logical shift right) as a RISC-V program.
  SHR(shift, value) pops shift and value, pushes value >> shift.
  If shift >= 256, the result is 0.

  The 256-bit value is stored as 8 little-endian 32-bit limbs.
  A shift by s bits decomposes into:
    limb_shift = s / 32  (skip whole limbs, 0-7)
    bit_shift  = s % 32  (shift within/across limbs, 0-31)

  For output limb i:
    result[i] = (value[i + limb_shift] >>> bit_shift) |
                ((value[i + limb_shift + 1] <<< (32 - bit_shift)) &&& mask)
  where mask = 0xFFFFFFFF if bit_shift > 0, else 0.

  Register allocation:
    x12 = EVM stack pointer
    x6  = bit_shift (0-31), preserved during limb processing
    x7  = anti_shift = 32 - bit_shift, preserved
    x11 = mask (0 or 0xFFFFFFFF), preserved
    x5  = temp: current limb during processing, limb_shift during dispatch
    x10 = temp: next limb during processing

  Program layout (302 instructions):
    Phase A (17 instrs): Check shift >= 256
    Phase B (7 instrs):  Extract bit_shift, limb_shift, mask, anti_shift
    Phase C (13 instrs): Cascade dispatch on limb_shift (0-7)
    Phase D (256 instrs): 8 shift bodies (ls7 through ls0)
    Phase E (9 instrs):  Zero path (shift >= 256)
    Exit point
-/

import EvmAsm.Evm32.Stack
import EvmAsm.Rv32.CPSSpec

namespace EvmAsm

-- ============================================================================
-- Sub-program definitions (to avoid maxRecDepth issues with deep ;; chains)
-- ============================================================================

/-- Phase A: Check shift >= 256 (17 instructions).
    OR-reduce shift limbs 1-7. BNE to zero_path if nonzero.
    Then check limb 0 < 256. BEQ to zero_path if not. -/
def shr_phase_a : Program :=
  LW .x5  .x12 4  ;;                          -- x5  = shift[1]
  LW .x10 .x12 8  ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= shift[2]
  LW .x10 .x12 12 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= shift[3]
  LW .x10 .x12 16 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= shift[4]
  LW .x10 .x12 20 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= shift[5]
  LW .x10 .x12 24 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= shift[6]
  LW .x10 .x12 28 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= shift[7]
  single (.BNE .x5 .x0 1120) ;;               -- high limbs nonzero → zero_path (1172-52=1120)
  LW .x5  .x12 0  ;;                          -- x5 = shift[0]
  single (.SLTIU .x10 .x5 256) ;;             -- x10 = (shift[0] < 256)
  single (.BEQ .x10 .x0 1108)                 -- shift[0] >= 256 → zero_path (1172-64=1108)

/-- Phase B: Extract parameters (7 instructions). -/
def shr_phase_b : Program :=
  single (.ANDI .x6 .x5 31) ;;                -- x6 = bit_shift
  single (.SRLI .x5 .x5 5)  ;;                -- x5 = limb_shift
  single (.SLTU .x11 .x0 .x6) ;;             -- x11 = (bit_shift > 0)
  single (.SUB .x11 .x0 .x11) ;;             -- x11 = mask
  LI .x7 32 ;;                                -- x7 = 32
  single (.SUB .x7 .x7 .x6) ;;               -- x7 = anti_shift
  ADDI .x12 .x12 32                           -- pop shift word

/-- Phase C: Cascade dispatch (13 instructions). -/
def shr_phase_c : Program :=
  single (.BEQ .x5 .x0 864) ;;               -- ls0 (960-96=864)
  ADDI .x10 .x0 1 ;;
  single (.BEQ .x5 .x10 668) ;;              -- ls1 (772-104=668)
  ADDI .x10 .x0 2 ;;
  single (.BEQ .x5 .x10 496) ;;              -- ls2 (608-112=496)
  ADDI .x10 .x0 3 ;;
  single (.BEQ .x5 .x10 348) ;;              -- ls3 (468-120=348)
  ADDI .x10 .x0 4 ;;
  single (.BEQ .x5 .x10 224) ;;              -- ls4 (352-128=224)
  ADDI .x10 .x0 5 ;;
  single (.BEQ .x5 .x10 124) ;;              -- ls5 (260-136=124)
  ADDI .x10 .x0 6 ;;
  single (.BEQ .x5 .x10 48)                  -- ls6 (192-144=48)

/-- Helper: 7-instruction merge block for one middle limb.
    LW x5, src_off(x12); SRL x5,x5,x6; LW x10, next_off(x12);
    SLL x10,x10,x7; AND x10,x10,x11; OR x5,x5,x10; SW x12,x5,dst_off -/
def shr_merge_limb (src_off next_off dst_off : BitVec 12) : Program :=
  LW .x5 .x12 src_off ;;
  single (.SRL .x5 .x5 .x6) ;;
  LW .x10 .x12 next_off ;;
  single (.SLL .x10 .x10 .x7) ;;
  single (.AND .x10 .x10 .x11) ;;
  single (.OR .x5 .x5 .x10) ;;
  SW .x12 .x5 dst_off

/-- Helper: 3-instruction last-limb block.
    LW x5, 28(x12); SRL x5,x5,x6; SW x12,x5,dst_off -/
def shr_last_limb (dst_off : BitVec 12) : Program :=
  LW .x5 .x12 28 ;;
  single (.SRL .x5 .x5 .x6) ;;
  SW .x12 .x5 dst_off

/-- ls7: limb_shift=7 (11 instructions) -/
def shr_body_7 : Program :=
  shr_last_limb 0 ;;
  SW .x12 .x0 4 ;; SW .x12 .x0 8 ;; SW .x12 .x0 12 ;;
  SW .x12 .x0 16 ;; SW .x12 .x0 20 ;; SW .x12 .x0 24 ;; SW .x12 .x0 28 ;;
  single (.JAL .x0 1020)                      -- exit (1208-188=1020)

/-- ls6: limb_shift=6 (17 instructions) -/
def shr_body_6 : Program :=
  shr_merge_limb 24 28 0 ;;                   -- i=0: value[6],value[7]→result[0]
  shr_last_limb 4 ;;                          -- i=1: value[7]→result[1]
  SW .x12 .x0 8 ;; SW .x12 .x0 12 ;;
  SW .x12 .x0 16 ;; SW .x12 .x0 20 ;; SW .x12 .x0 24 ;; SW .x12 .x0 28 ;;
  single (.JAL .x0 952)                       -- exit (1208-256=952)

/-- ls5: limb_shift=5 (23 instructions) -/
def shr_body_5 : Program :=
  shr_merge_limb 20 24 0 ;;                   -- i=0
  shr_merge_limb 24 28 4 ;;                   -- i=1
  shr_last_limb 8 ;;                          -- i=2
  SW .x12 .x0 12 ;; SW .x12 .x0 16 ;;
  SW .x12 .x0 20 ;; SW .x12 .x0 24 ;; SW .x12 .x0 28 ;;
  single (.JAL .x0 860)                       -- exit (1208-348=860)

/-- ls4: limb_shift=4 (29 instructions) -/
def shr_body_4 : Program :=
  shr_merge_limb 16 20 0 ;;                   -- i=0
  shr_merge_limb 20 24 4 ;;                   -- i=1
  shr_merge_limb 24 28 8 ;;                   -- i=2
  shr_last_limb 12 ;;                         -- i=3
  SW .x12 .x0 16 ;; SW .x12 .x0 20 ;;
  SW .x12 .x0 24 ;; SW .x12 .x0 28 ;;
  single (.JAL .x0 744)                       -- exit (1208-464=744)

/-- ls3: limb_shift=3 (35 instructions) -/
def shr_body_3 : Program :=
  shr_merge_limb 12 16 0 ;;                   -- i=0
  shr_merge_limb 16 20 4 ;;                   -- i=1
  shr_merge_limb 20 24 8 ;;                   -- i=2
  shr_merge_limb 24 28 12 ;;                  -- i=3
  shr_last_limb 16 ;;                         -- i=4
  SW .x12 .x0 20 ;; SW .x12 .x0 24 ;; SW .x12 .x0 28 ;;
  single (.JAL .x0 604)                       -- exit (1208-604=604)

/-- ls2: limb_shift=2 (41 instructions) -/
def shr_body_2 : Program :=
  shr_merge_limb 8 12 0 ;;                    -- i=0
  shr_merge_limb 12 16 4 ;;                   -- i=1
  shr_merge_limb 16 20 8 ;;                   -- i=2
  shr_merge_limb 20 24 12 ;;                  -- i=3
  shr_merge_limb 24 28 16 ;;                  -- i=4
  shr_last_limb 20 ;;                         -- i=5
  SW .x12 .x0 24 ;; SW .x12 .x0 28 ;;
  single (.JAL .x0 440)                       -- exit (1208-768=440)

/-- ls1: limb_shift=1 (47 instructions) -/
def shr_body_1 : Program :=
  shr_merge_limb 4 8 0 ;;                     -- i=0
  shr_merge_limb 8 12 4 ;;                    -- i=1
  shr_merge_limb 12 16 8 ;;                   -- i=2
  shr_merge_limb 16 20 12 ;;                  -- i=3
  shr_merge_limb 20 24 16 ;;                  -- i=4
  shr_merge_limb 24 28 20 ;;                  -- i=5
  shr_last_limb 24 ;;                         -- i=6
  SW .x12 .x0 28 ;;
  single (.JAL .x0 252)                       -- exit (1208-956=252)

/-- ls0: limb_shift=0 (53 instructions) -/
def shr_body_0 : Program :=
  shr_merge_limb 0 4 0 ;;                     -- i=0
  shr_merge_limb 4 8 4 ;;                     -- i=1
  shr_merge_limb 8 12 8 ;;                    -- i=2
  shr_merge_limb 12 16 12 ;;                  -- i=3
  shr_merge_limb 16 20 16 ;;                  -- i=4
  shr_merge_limb 20 24 20 ;;                  -- i=5
  shr_merge_limb 24 28 24 ;;                  -- i=6
  shr_last_limb 28 ;;                         -- i=7
  single (.JAL .x0 40)                        -- exit (1208-1168=40)

/-- Phase E: Zero path (9 instructions). -/
def shr_zero_path : Program :=
  ADDI .x12 .x12 32 ;;
  SW .x12 .x0 0 ;; SW .x12 .x0 4 ;; SW .x12 .x0 8 ;; SW .x12 .x0 12 ;;
  SW .x12 .x0 16 ;; SW .x12 .x0 20 ;; SW .x12 .x0 24 ;; SW .x12 .x0 28

-- ============================================================================
-- Full program
-- ============================================================================

/-- 256-bit EVM SHR: binary (pop 2, push 1, sp += 32).
    SHR(shift, value) = value >> shift. 302 instructions total. -/
def evm_shr : Program :=
  shr_phase_a ;;
  shr_phase_b ;;
  shr_phase_c ;;
  shr_body_7 ;; shr_body_6 ;; shr_body_5 ;; shr_body_4 ;;
  shr_body_3 ;; shr_body_2 ;; shr_body_1 ;; shr_body_0 ;;
  shr_zero_path
  -- Exit: offset 1208 (instruction 302)

-- ============================================================================
-- Instruction count verification
-- ============================================================================

/-- evm_shr has exactly 302 instructions. -/
example : evm_shr.length = 302 := by native_decide

-- ============================================================================
-- Test infrastructure
-- ============================================================================

/-- Create a test state for SHR with 8 shift limbs and 8 value limbs.
    Memory layout: sp → [s0..s7, v0..v7] (16 words). -/
def mkShrTestState (sp : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)   -- shift limbs (LE)
    (v0 v1 v2 v3 v4 v5 v6 v7 : Word)   -- value limbs (LE)
    : MachineState where
  regs := fun r =>
    match r with
    | .x12 => sp
    | _    => 0
  mem := fun a =>
    if a == sp      then s0
    else if a == sp + 4  then s1
    else if a == sp + 8  then s2
    else if a == sp + 12 then s3
    else if a == sp + 16 then s4
    else if a == sp + 20 then s5
    else if a == sp + 24 then s6
    else if a == sp + 28 then s7
    else if a == sp + 32 then v0
    else if a == sp + 36 then v1
    else if a == sp + 40 then v2
    else if a == sp + 44 then v3
    else if a == sp + 48 then v4
    else if a == sp + 52 then v5
    else if a == sp + 56 then v6
    else if a == sp + 60 then v7
    else 0
  code := loadProgram 0 evm_shr
  pc := 0

/-- Run evm_shr and check the final PC and x12 register. -/
def runShrCheck (sp : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (v0 v1 v2 v3 v4 v5 v6 v7 : Word)
    (steps : Nat) : Option (Word × Word) :=
  let s := mkShrTestState sp s0 s1 s2 s3 s4 s5 s6 s7 v0 v1 v2 v3 v4 v5 v6 v7
  match stepN steps s with
  | some s' => some (s'.pc, s'.getReg .x12)
  | none => none

/-- Run evm_shr and extract 8 result limbs. -/
def runShrResult (sp : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (v0 v1 v2 v3 v4 v5 v6 v7 : Word)
    (steps : Nat) : Option (List Word) :=
  let s := mkShrTestState sp s0 s1 s2 s3 s4 s5 s6 s7 v0 v1 v2 v3 v4 v5 v6 v7
  match stepN steps s with
  | some s' =>
    let rsp := s'.getReg .x12
    some [s'.getMem rsp, s'.getMem (rsp + 4), s'.getMem (rsp + 8), s'.getMem (rsp + 12),
          s'.getMem (rsp + 16), s'.getMem (rsp + 20), s'.getMem (rsp + 24), s'.getMem (rsp + 28)]
  | none => none

-- ============================================================================
-- Concrete tests via native_decide
-- ============================================================================

-- Step counts by path:
-- ls0 (shift 0-31): 17+7+1+53 = 78 steps
-- ls1 (shift 32-63): 17+7+3+47 = 74
-- ls2 (shift 64-95): 17+7+5+41 = 70
-- ls3 (shift 96-127): 17+7+7+35 = 66
-- ls4 (shift 128-159): 17+7+9+29 = 62
-- ls5 (shift 160-191): 17+7+11+23 = 58
-- ls6 (shift 192-223): 17+7+13+17 = 54  (note: phase_c is 13 for ls6 dispatch via last BEQ)
-- Actually for ls6: BEQ@96 not taken, ADDI@100, BEQ@104 not taken, ..., ADDI@140, BEQ@144 taken = 13 steps
-- ls7 (shift 224-255): 17+7+13+11 = 48 (fall through all of phase C)
-- zero_path (shift >= 256, high limbs nonzero): 14+9 = 23
-- zero_path (shift >= 256, limb0 >= 256): 17+9 = 26

-- Test 1: SHR(0, value) = value (no shift, ls0 path, 78 steps)
/-- SHR by 0: result equals input value. -/
example : runShrResult 1024 0 0 0 0 0 0 0 0  0xDEADBEEF 0 0 0 0 0 0 1  78 =
    some [0xDEADBEEF, 0, 0, 0, 0, 0, 0, 1] := by native_decide

-- Test 2: SHR(1, value) (ls0 path, 78 steps)
-- result[0] = (0xDEADBEEF >>> 1) | ((0 <<< 31) & mask) = 0x6F56DF77
-- result[6] = (0 >>> 1) | ((1 <<< 31) & mask) = 0x80000000
-- result[7] = 1 >>> 1 = 0
/-- SHR by 1 bit. -/
example : runShrResult 1024 1 0 0 0 0 0 0 0  0xDEADBEEF 0 0 0 0 0 0 1  78 =
    some [0x6F56DF77, 0, 0, 0, 0, 0, 0x80000000, 0] := by native_decide

-- Test 3: SHR(32, value) (ls1 path, 74 steps)
-- limb_shift=1, bit_shift=0
-- result[i] = value[i+1] for i=0..6, result[7]=0
/-- SHR by 32 bits (one full limb). -/
example : runShrResult 1024 32 0 0 0 0 0 0 0  0xDEADBEEF 0 0 0 0 0 0 1  74 =
    some [0, 0, 0, 0, 0, 0, 1, 0] := by native_decide

-- Test 4: SHR(255, value) (ls7 path, 48 steps)
-- limb_shift=7, bit_shift=31
-- result[0] = value[7] >>> 31 = 1 >>> 31 = 0
/-- SHR by 255 bits. -/
example : runShrResult 1024 255 0 0 0 0 0 0 0  0xDEADBEEF 0 0 0 0 0 0 1  48 =
    some [0, 0, 0, 0, 0, 0, 0, 0] := by native_decide

-- Test 5: SHR(256, value) = 0 (zero path via limb0, 26 steps)
/-- SHR by 256: result is all zeros. -/
example : runShrResult 1024 256 0 0 0 0 0 0 0  0xDEADBEEF 0 0 0 0 0 0 1  26 =
    some [0, 0, 0, 0, 0, 0, 0, 0] := by native_decide

-- Test 6: SHR with nonzero high shift limb (zero path via BNE, 23 steps)
/-- SHR with shift having nonzero high limbs: result is all zeros. -/
example : runShrResult 1024 0 1 0 0 0 0 0 0  0xDEADBEEF 0 0 0 0 0 0 1  23 =
    some [0, 0, 0, 0, 0, 0, 0, 0] := by native_decide

-- Test 7: SHR(4, 0xFF) = 0x0F (ls0 path)
/-- SHR(4, 0xFF) = 0x0F. -/
example : runShrResult 1024 4 0 0 0 0 0 0 0  0xFF 0 0 0 0 0 0 0  78 =
    some [0x0F, 0, 0, 0, 0, 0, 0, 0] := by native_decide

-- Test 8: SHR(33, all-F value) (ls1 path, 74 steps)
-- limb_shift=1, bit_shift=1
-- result[i] = (0xFFFFFFFF >>> 1) | ((0xFFFFFFFF <<< 31) & mask) = 0xFFFFFFFF (for i=0..5)
-- result[6] = (0xFFFFFFFF >>> 1) = 0x7FFFFFFF (last non-zero limb)
-- result[7] = 0
/-- SHR(33, all-F value): shift by 1 limb + 1 bit. -/
example : runShrResult 1024 33 0 0 0 0 0 0 0
    0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
    0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF  74 =
    some [0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF,
          0xFFFFFFFF, 0xFFFFFFFF, 0x7FFFFFFF, 0] := by native_decide

-- Test 9: SHR(224, ...) with v7 = 0xABCD1234 (ls7 path, 48 steps)
-- limb_shift=7, bit_shift=0
-- result[0] = value[7] >>> 0 = 0xABCD1234
/-- SHR by 224 bits (7 full limbs). -/
example : runShrResult 1024 224 0 0 0 0 0 0 0  1 2 3 4 5 6 7 0xABCD1234  48 =
    some [0xABCD1234, 0, 0, 0, 0, 0, 0, 0] := by native_decide

-- Test 10: Verify PC and sp are correct after execution
/-- After SHR(0, ...), PC = 1208 and x12 = sp + 32. -/
example : runShrCheck 1024 0 0 0 0 0 0 0 0  0xDEADBEEF 0 0 0 0 0 0 1  78 =
    some (1208, 1056) := by native_decide

/-- After SHR(256, ...), PC = 1208 and x12 = sp + 32. -/
example : runShrCheck 1024 256 0 0 0 0 0 0 0  0xDEADBEEF 0 0 0 0 0 0 1  26 =
    some (1208, 1056) := by native_decide

end EvmAsm
