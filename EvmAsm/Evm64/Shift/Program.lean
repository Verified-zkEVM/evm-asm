/-
  EvmAsm.Evm64.Shift

  256-bit EVM SHR (logical shift right) as a 64-bit RISC-V program.
  SHR(shift, value) pops shift and value, pushes value >> shift.
  If shift >= 256, the result is 0.

  The 256-bit value is stored as 4 little-endian 64-bit limbs.
  A shift by s bits decomposes into:
    limb_shift = s / 64  (skip whole limbs, 0-3)
    bit_shift  = s % 64  (shift within/across limbs, 0-63)

  For output limb i:
    result[i] = (value[i + limb_shift] >>> bit_shift) |
                ((value[i + limb_shift + 1] <<< (64 - bit_shift)) &&& mask)
  where mask = 0xFFFFFFFFFFFFFFFF if bit_shift > 0, else 0.

  Register allocation:
    x12 = EVM stack pointer
    x6  = bit_shift (0-63), preserved during limb processing
    x7  = antiShift = 64 - bit_shift, preserved
    x11 = mask (0 or 0xFFFFFFFFFFFFFFFF), preserved
    x5  = temp: current limb during processing, limb_shift during dispatch
    x10 = temp: next limb during processing

  Program layout (90 instructions = 360 bytes):
    Phase A (9 instrs):  Check shift >= 256
    Phase B (7 instrs):  Extract bit_shift, limb_shift, mask, antiShift
    Phase C (5 instrs):  Cascade dispatch on limb_shift (0-3)
    Phase D (64 instrs): 4 shift bodies (ls3 through ls0)
    Phase E (5 instrs):  Zero path (shift >= 256)
    Exit point: offset 360
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Sub-program definitions
-- ============================================================================

/-- Phase A: Check shift >= 256 (9 instructions).
    OR-reduce shift limbs 1-3. BNE to zero_path if nonzero.
    Then check limb 0 < 256. BEQ to zero_path if not. -/
def shr_phase_a : Program :=
  LD .x5  .x12 8  ;;                          -- x5  = shift[1]
  LD .x10 .x12 16 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= shift[2]
  LD .x10 .x12 24 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= shift[3]
  single (.BNE .x5 .x0 320) ;;               -- high limbs nonzero → zero_path (340-20=320)
  LD .x5  .x12 0  ;;                          -- x5 = shift[0]
  single (.SLTIU .x10 .x5 256) ;;             -- x10 = (shift[0] < 256)
  single (.BEQ .x10 .x0 308)                  -- shift[0] >= 256 → zero_path (340-32=308)

/-- Phase B: Extract parameters (7 instructions). -/
def shr_phase_b : Program :=
  single (.ANDI .x6 .x5 63) ;;               -- x6 = bit_shift
  single (.SRLI .x5 .x5 6)  ;;               -- x5 = limb_shift
  single (.SLTU .x11 .x0 .x6) ;;            -- x11 = (bit_shift > 0)
  single (.SUB .x11 .x0 .x11) ;;            -- x11 = mask
  LI .x7 64 ;;                               -- x7 = 64
  single (.SUB .x7 .x7 .x6) ;;              -- x7 = antiShift
  ADDI .x12 .x12 32                          -- pop shift word

/-- Phase C: Cascade dispatch (5 instructions). -/
def shr_phase_c : Program :=
  single (.BEQ .x5 .x0 176) ;;              -- ls0 (240-64=176)
  ADDI .x10 .x0 1 ;;
  single (.BEQ .x5 .x10 92) ;;              -- ls1 (164-72=92)
  ADDI .x10 .x0 2 ;;
  single (.BEQ .x5 .x10 32)                 -- ls2 (112-80=32)

/-- Helper: 7-instruction merge block for one middle limb (64-bit).
    LD x5, src_off(x12); SRL x5,x5,x6; LD x10, next_off(x12);
    SLL x10,x10,x7; AND x10,x10,x11; OR x5,x5,x10; SD x12,x5,dst_off -/
def shr_merge_limb (src_off next_off dst_off : BitVec 12) : Program :=
  LD .x5 .x12 src_off ;;
  single (.SRL .x5 .x5 .x6) ;;
  LD .x10 .x12 next_off ;;
  single (.SLL .x10 .x10 .x7) ;;
  single (.AND .x10 .x10 .x11) ;;
  single (.OR .x5 .x5 .x10) ;;
  SD .x12 .x5 dst_off

/-- Helper: 3-instruction last-limb block (64-bit).
    LD x5, 24(x12); SRL x5,x5,x6; SD x12,x5,dst_off -/
def shr_last_limb (dst_off : BitVec 12) : Program :=
  LD .x5 .x12 24 ;;
  single (.SRL .x5 .x5 .x6) ;;
  SD .x12 .x5 dst_off

/-- ls3: limb_shift=3 (7 instructions) -/
def shr_body_3 : Program :=
  shr_last_limb 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24 ;;
  single (.JAL .x0 252)                      -- exit (360-108=252)

/-- ls2: limb_shift=2 (13 instructions) -/
def shr_body_2 : Program :=
  shr_merge_limb 16 24 0 ;;                  -- i=0: value[2],value[3]→result[0]
  shr_last_limb 8 ;;                         -- i=1: value[3]→result[1]
  SD .x12 .x0 16 ;; SD .x12 .x0 24 ;;
  single (.JAL .x0 200)                      -- exit (360-160=200)

/-- ls1: limb_shift=1 (19 instructions) -/
def shr_body_1 : Program :=
  shr_merge_limb 8 16 0 ;;                   -- i=0: value[1],value[2]→result[0]
  shr_merge_limb 16 24 8 ;;                  -- i=1: value[2],value[3]→result[1]
  shr_last_limb 16 ;;                        -- i=2: value[3]→result[2]
  SD .x12 .x0 24 ;;
  single (.JAL .x0 124)                      -- exit (360-236=124)

/-- ls0: limb_shift=0 (25 instructions) -/
def shr_body_0 : Program :=
  shr_merge_limb 0 8 0 ;;                    -- i=0: value[0],value[1]→result[0]
  shr_merge_limb 8 16 8 ;;                   -- i=1: value[1],value[2]→result[1]
  shr_merge_limb 16 24 16 ;;                 -- i=2: value[2],value[3]→result[2]
  shr_last_limb 24 ;;                        -- i=3: value[3]→result[3]
  single (.JAL .x0 24)                       -- exit (360-336=24)

/-- Phase E: Zero path (5 instructions). -/
def shr_zero_path : Program :=
  ADDI .x12 .x12 32 ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

-- ============================================================================
-- Full SHR program
-- ============================================================================

/-- 256-bit EVM SHR: binary (pop 2, push 1, sp += 32).
    SHR(shift, value) = value >> shift. 90 instructions total. -/
def evm_shr : Program :=
  shr_phase_a ;;
  shr_phase_b ;;
  shr_phase_c ;;
  shr_body_3 ;; shr_body_2 ;; shr_body_1 ;; shr_body_0 ;;
  shr_zero_path
  -- Exit: offset 360 (instruction 90)

-- ============================================================================
-- SHL (Shift Left) sub-program definitions
-- ============================================================================

/-
  SHL(shift, value) = value << shift.
  Same phases A (check >= 256), B (extract params), C (dispatch), zero_path.
  Only the 4 bodies differ: SLL/SRL swapped, limbs processed top-down.

  For output limb i (with limb_shift L):
    result[i] = (value[i - L] <<< bit_shift) |
                ((value[i - L - 1] >>> antiShift) &&& mask)
  where undefined indices → 0.

  Register allocation: same as SHR.
  Program layout: 90 instructions = 360 bytes (same as SHR).
-/

/-- SHL merge limb: (src <<< bs) | ((prev >>> as) & mask).
    7 instructions. Mirror of shr_merge_limb with SLL/SRL swapped. -/
def shl_merge_limb (src_off prev_off dst_off : BitVec 12) : Program :=
  LD .x5 .x12 src_off ;;
  single (.SLL .x5 .x5 .x6) ;;
  LD .x10 .x12 prev_off ;;
  single (.SRL .x10 .x10 .x7) ;;
  single (.AND .x10 .x10 .x11) ;;
  single (.OR .x5 .x5 .x10) ;;
  SD .x12 .x5 dst_off

/-- SHL first limb: v[0] <<< bs.
    3 instructions. Mirror of shr_last_limb. -/
def shl_first_limb (dst_off : BitVec 12) : Program :=
  LD .x5 .x12 0 ;;
  single (.SLL .x5 .x5 .x6) ;;
  SD .x12 .x5 dst_off

/-- ls3: limb_shift=3 (7 instructions).
    result[3] = v[0] <<< bs; result[0..2] = 0 -/
def shl_body_3 : Program :=
  shl_first_limb 24 ;;
  SD .x12 .x0 16 ;; SD .x12 .x0 8 ;; SD .x12 .x0 0 ;;
  single (.JAL .x0 252)                      -- exit (360-108=252)

/-- ls2: limb_shift=2 (13 instructions).
    result[3] = merge(v[1],v[0]); result[2] = v[0]<<<bs; result[0..1] = 0 -/
def shl_body_2 : Program :=
  shl_merge_limb 8 0 24 ;;                   -- result[3] = merge(v[1],v[0])
  shl_first_limb 16 ;;                       -- result[2] = v[0] <<< bs
  SD .x12 .x0 8 ;; SD .x12 .x0 0 ;;
  single (.JAL .x0 200)                      -- exit (360-160=200)

/-- ls1: limb_shift=1 (19 instructions).
    result[3] = merge(v[2],v[1]); result[2] = merge(v[1],v[0]);
    result[1] = v[0]<<<bs; result[0] = 0 -/
def shl_body_1 : Program :=
  shl_merge_limb 16 8 24 ;;                  -- result[3] = merge(v[2],v[1])
  shl_merge_limb 8 0 16 ;;                   -- result[2] = merge(v[1],v[0])
  shl_first_limb 8 ;;                        -- result[1] = v[0] <<< bs
  SD .x12 .x0 0 ;;
  single (.JAL .x0 124)                      -- exit (360-236=124)

/-- ls0: limb_shift=0 (25 instructions).
    result[i] = merge(v[i], v[i-1]) for i=3..1; result[0] = v[0]<<<bs -/
def shl_body_0 : Program :=
  shl_merge_limb 24 16 24 ;;                 -- result[3] = merge(v[3],v[2])
  shl_merge_limb 16 8 16 ;;                  -- result[2] = merge(v[2],v[1])
  shl_merge_limb 8 0 8 ;;                    -- result[1] = merge(v[1],v[0])
  shl_first_limb 0 ;;                        -- result[0] = v[0] <<< bs
  single (.JAL .x0 24)                       -- exit (360-336=24)

-- ============================================================================
-- Full SHL program
-- ============================================================================

/-- 256-bit EVM SHL: binary (pop 2, push 1, sp += 32).
    SHL(shift, value) = value << shift. 90 instructions total.
    Reuses SHR phases A/B/C/zero_path (identical logic). -/
def evm_shl : Program :=
  shr_phase_a ;;
  shr_phase_b ;;
  shr_phase_c ;;
  shl_body_3 ;; shl_body_2 ;; shl_body_1 ;; shl_body_0 ;;
  shr_zero_path
  -- Exit: offset 360 (instruction 90)

-- ============================================================================
-- Instruction count verification
-- ============================================================================

/-- evm_shr has exactly 90 instructions. -/
example : evm_shr.length = 90 := by decide

-- ============================================================================
-- Test infrastructure
-- ============================================================================

/-- Create a test state for SHR with 4 shift limbs and 4 value limbs.
    Memory layout: sp → [s0..s3, v0..v3] (8 doublewords). -/
def mkShrTestState (sp : Word)
    (s0 s1 s2 s3 : Word)   -- shift limbs (LE)
    (v0 v1 v2 v3 : Word)   -- value limbs (LE)
    : MachineState where
  regs := fun r =>
    match r with
    | .x12 => sp
    | _    => 0
  mem := fun a =>
    if a == sp      then s0
    else if a == sp + 8  then s1
    else if a == sp + 16 then s2
    else if a == sp + 24 then s3
    else if a == sp + 32 then v0
    else if a == sp + 40 then v1
    else if a == sp + 48 then v2
    else if a == sp + 56 then v3
    else 0
  code := loadProgram 0 evm_shr
  pc := 0

/-- Run evm_shr and check the final PC and x12 register. -/
def runShrCheck (sp : Word)
    (s0 s1 s2 s3 : Word)
    (v0 v1 v2 v3 : Word)
    (steps : Nat) : Option (Word × Word) :=
  let s := mkShrTestState sp s0 s1 s2 s3 v0 v1 v2 v3
  match stepN steps s with
  | some s' => some (s'.pc, s'.getReg .x12)
  | none => none

/-- Run evm_shr and extract 4 result limbs. -/
def runShrResult (sp : Word)
    (s0 s1 s2 s3 : Word)
    (v0 v1 v2 v3 : Word)
    (steps : Nat) : Option (List Word) :=
  let s := mkShrTestState sp s0 s1 s2 s3 v0 v1 v2 v3
  match stepN steps s with
  | some s' =>
    let rsp := s'.getReg .x12
    some [s'.getMem rsp, s'.getMem (rsp + 8), s'.getMem (rsp + 16), s'.getMem (rsp + 24)]
  | none => none

-- ============================================================================
-- Concrete tests via decide
-- ============================================================================

-- Step counts by path:
-- ls0 (shift 0-63):  9+7+1+25 = 42 steps
-- ls1 (shift 64-127): 9+7+3+19 = 38
-- ls2 (shift 128-191): 9+7+5+13 = 34
-- ls3 (shift 192-255): 9+7+5+7 = 28
-- zero_path (high limbs nonzero): 6+5 = 11
-- zero_path (limb0 >= 256): 9+5 = 14

-- Test 1: SHR(0, value) = value (no shift, ls0 path, 42 steps)
/-- SHR by 0: result equals input value. -/
example : runShrResult 1024 0 0 0 0  0xDEADBEEFCAFE0000 0 0 1  42 =
    some [0xDEADBEEFCAFE0000, 0, 0, 1] := by decide

-- Test 2: SHR(1, value) (ls0 path, 42 steps)
-- result[0] = (0xDEADBEEFCAFE0000 >>> 1) | (0 <<< 63) = 0x6F56DF77E57F0000
-- result[2] = (0 >>> 1) | ((1 <<< 63) & mask) = 0x8000000000000000
-- result[3] = 1 >>> 1 = 0
/-- SHR by 1 bit. -/
example : runShrResult 1024 1 0 0 0  0xDEADBEEFCAFE0000 0 0 1  42 =
    some [0x6F56DF77E57F0000, 0, 0x8000000000000000, 0] := by decide

-- Test 3: SHR(64, value) (ls1 path, 38 steps)
-- limb_shift=1, bit_shift=0
-- result[i] = value[i+1] for i=0..2, result[3]=0
/-- SHR by 64 bits (one full limb). -/
example : runShrResult 1024 64 0 0 0  0xDEADBEEFCAFE0000 0 0 1  38 =
    some [0, 0, 1, 0] := by decide

-- Test 4: SHR(255, value) (ls3 path, 28 steps)
-- limb_shift=3, bit_shift=63
-- result[0] = value[3] >>> 63 = 1 >>> 63 = 0
/-- SHR by 255 bits. -/
example : runShrResult 1024 255 0 0 0  0xDEADBEEFCAFE0000 0 0 1  28 =
    some [0, 0, 0, 0] := by decide

-- Test 5: SHR(256, value) = 0 (zero path via limb0, 14 steps)
/-- SHR by 256: result is all zeros. -/
example : runShrResult 1024 256 0 0 0  0xDEADBEEFCAFE0000 0 0 1  14 =
    some [0, 0, 0, 0] := by decide

-- Test 6: SHR with nonzero high shift limb (zero path via BNE, 11 steps)
/-- SHR with shift having nonzero high limbs: result is all zeros. -/
example : runShrResult 1024 0 1 0 0  0xDEADBEEFCAFE0000 0 0 1  11 =
    some [0, 0, 0, 0] := by decide

-- Test 7: SHR(4, 0xFF) = 0x0F (ls0 path)
/-- SHR(4, 0xFF) = 0x0F. -/
example : runShrResult 1024 4 0 0 0  0xFF 0 0 0  42 =
    some [0x0F, 0, 0, 0] := by decide

-- Test 8: SHR(65, all-F value) (ls1 path, 38 steps)
-- limb_shift=1, bit_shift=1
-- result[0] = (allF >>> 1) | ((allF <<< 63) & mask) = allF
-- result[1] = (allF >>> 1) | ((allF <<< 63) & mask) = allF
-- result[2] = allF >>> 1 = 0x7FFFFFFFFFFFFFFF
-- result[3] = 0
/-- SHR(65, all-F value): shift by 1 limb + 1 bit. -/
example : runShrResult 1024 65 0 0 0
    0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF  38 =
    some [0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0] := by decide

-- Test 9: SHR(192, ...) with v3 = 0xABCD1234 (ls3 path, 28 steps)
-- limb_shift=3, bit_shift=0
-- result[0] = value[3] >>> 0 = 0xABCD1234
/-- SHR by 192 bits (3 full limbs). -/
example : runShrResult 1024 192 0 0 0  1 2 3 0xABCD1234  28 =
    some [0xABCD1234, 0, 0, 0] := by decide

-- Test 10: Verify PC and sp are correct after execution
/-- After SHR(0, ...), PC = 360 and x12 = sp + 32. -/
example : runShrCheck 1024 0 0 0 0  0xDEADBEEFCAFE0000 0 0 1  42 =
    some (360, 1056) := by decide

/-- After SHR(256, ...), PC = 360 and x12 = sp + 32. -/
example : runShrCheck 1024 256 0 0 0  0xDEADBEEFCAFE0000 0 0 1  14 =
    some (360, 1056) := by decide

-- ============================================================================
-- SHL: Instruction count verification + tests
-- ============================================================================

/-- evm_shl has exactly 90 instructions. -/
example : evm_shl.length = 90 := by decide

/-- Create a test state for SHL. -/
def mkShlTestState (sp : Word)
    (s0 s1 s2 s3 : Word) (v0 v1 v2 v3 : Word) : MachineState where
  regs := fun r => match r with | .x12 => sp | _ => 0
  mem := fun a =>
    if a == sp      then s0
    else if a == sp + 8  then s1
    else if a == sp + 16 then s2
    else if a == sp + 24 then s3
    else if a == sp + 32 then v0
    else if a == sp + 40 then v1
    else if a == sp + 48 then v2
    else if a == sp + 56 then v3
    else 0
  code := loadProgram 0 evm_shl
  pc := 0

/-- Run evm_shl and extract 4 result limbs. -/
def runShlResult (sp : Word) (s0 s1 s2 s3 : Word) (v0 v1 v2 v3 : Word)
    (steps : Nat) : Option (List Word) :=
  let s := mkShlTestState sp s0 s1 s2 s3 v0 v1 v2 v3
  match stepN steps s with
  | some s' =>
    let rsp := s'.getReg .x12
    some [s'.getMem rsp, s'.getMem (rsp + 8), s'.getMem (rsp + 16), s'.getMem (rsp + 24)]
  | none => none

/-- Run evm_shl and check PC and x12. -/
def runShlCheck (sp : Word) (s0 s1 s2 s3 : Word) (v0 v1 v2 v3 : Word)
    (steps : Nat) : Option (Word × Word) :=
  let s := mkShlTestState sp s0 s1 s2 s3 v0 v1 v2 v3
  match stepN steps s with
  | some s' => some (s'.pc, s'.getReg .x12)
  | none => none

-- SHL step counts (same as SHR):
-- ls0 (shift 0-63):  42 steps
-- ls1 (shift 64-127): 38 steps
-- ls2 (shift 128-191): 34 steps
-- ls3 (shift 192-255): 28 steps
-- zero_path (high limbs nonzero): 11 steps
-- zero_path (limb0 >= 256): 14 steps

-- Test 1: SHL(0, value) = value
/-- SHL by 0: result equals input value. -/
example : runShlResult 1024 0 0 0 0  0xDEADBEEF 0 0 1  42 =
    some [0xDEADBEEF, 0, 0, 1] := by decide

-- Test 2: SHL(1, 0xFF) = 0x1FE (ls0 path)
/-- SHL by 1 bit. -/
example : runShlResult 1024 1 0 0 0  0xFF 0 0 0  42 =
    some [0x1FE, 0, 0, 0] := by decide

-- Test 3: SHL(4, 0xFF) = 0xFF0 (ls0 path)
/-- SHL(4, 0xFF) = 0xFF0. -/
example : runShlResult 1024 4 0 0 0  0xFF 0 0 0  42 =
    some [0xFF0, 0, 0, 0] := by decide

-- Test 4: SHL(64, value) (ls1 path, 38 steps)
-- limb_shift=1, bit_shift=0: result[i] = value[i-1]
/-- SHL by 64 bits (one full limb). -/
example : runShlResult 1024 64 0 0 0  0xDEADBEEF 0 0 1  38 =
    some [0, 0xDEADBEEF, 0, 0] := by decide

-- Test 5: SHL(65, all-F value) (ls1 path, 38 steps)
/-- SHL(65, all-F value): shift by 1 limb + 1 bit. -/
example : runShlResult 1024 65 0 0 0
    0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF  38 =
    some [0, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 6: SHL(192, ...) with v0 = 0xABCD1234 (ls3 path, 28 steps)
/-- SHL by 192 bits (3 full limbs). -/
example : runShlResult 1024 192 0 0 0  0xABCD1234 2 3 4  28 =
    some [0, 0, 0, 0xABCD1234] := by decide

-- Test 7: SHL(128, value) (ls2 path, 34 steps)
/-- SHL by 128 bits (2 full limbs). -/
example : runShlResult 1024 128 0 0 0  0xA 0xB 0xC 0xD  34 =
    some [0, 0, 0xA, 0xB] := by decide

-- Test 8: SHL(256, value) = 0 (zero path, 14 steps)
/-- SHL by 256: result is all zeros. -/
example : runShlResult 1024 256 0 0 0  0xDEADBEEF 0 0 1  14 =
    some [0, 0, 0, 0] := by decide

-- Test 9: SHL with nonzero high shift limb (zero path, 11 steps)
/-- SHL with shift having nonzero high limbs: result is all zeros. -/
example : runShlResult 1024 0 1 0 0  0xDEADBEEF 0 0 1  11 =
    some [0, 0, 0, 0] := by decide

-- Test 10: SHL(1, ...) with carry across limb boundary
-- v0 = 0x8000000000000000, SHL 1 → result[0] = 0, result[1] = 1
/-- SHL by 1 with carry across limb boundary. -/
example : runShlResult 1024 1 0 0 0  0x8000000000000000 0 0 0  42 =
    some [0, 1, 0, 0] := by decide

-- Test 11: Verify PC and sp are correct after execution
/-- After SHL(0, ...), PC = 360 and x12 = sp + 32. -/
example : runShlCheck 1024 0 0 0 0  0xFF 0 0 0  42 =
    some (360, 1056) := by decide

-- ============================================================================
-- SAR (Shift Arithmetic Right) sub-program definitions
-- ============================================================================

/-
  SAR(shift, value) = arithmetic right shift.
  Like SHR but fills vacated bits with the sign bit (bit 255 of value).
  - Merge limbs: identical to SHR (SRL + SLL + AND + OR)
  - Last limb: SRA instead of SRL (sign-preserving)
  - Vacated upper limbs: filled with sign extension (SRAI result, 63)
  - Sign-fill path (shift >= 256): all limbs = sign extension of value[3]

  Register allocation: same as SHR/SHL.
  Program layout: 95 instructions = 380 bytes.
    Phase A (9 instrs):  Check shift >= 256 → sign_fill path
    Phase B (7 instrs):  Extract bit_shift, limb_shift, mask, antiShift (reuses shr_phase_b)
    Phase C (5 instrs):  Cascade dispatch on limb_shift (0-3)
    Phase D (67 instrs): 4 shift bodies (ls3=8, ls2=14, ls1=20, ls0=25)
    Phase E (7 instrs):  Sign-fill path (shift >= 256)
    Exit point: offset 380
-/

/-- SAR Phase A: Check shift >= 256 (9 instructions).
    Same logic as SHR but branches to sign_fill (byte 352) instead of zero_path. -/
def sar_phase_a : Program :=
  LD .x5  .x12 8  ;;
  LD .x10 .x12 16 ;; single (.OR .x5 .x5 .x10) ;;
  LD .x10 .x12 24 ;; single (.OR .x5 .x5 .x10) ;;
  single (.BNE .x5 .x0 332) ;;               -- high limbs nonzero → sign_fill (352-20=332)
  LD .x5  .x12 0  ;;
  single (.SLTIU .x10 .x5 256) ;;
  single (.BEQ .x10 .x0 320)                  -- shift[0] >= 256 → sign_fill (352-32=320)

/-- SAR Phase C: Cascade dispatch (5 instructions).
    Same structure as SHR but with different offsets for SAR bodies. -/
def sar_phase_c : Program :=
  single (.BEQ .x5 .x0 188) ;;              -- ls0 (252-64=188)
  ADDI .x10 .x0 1 ;;
  single (.BEQ .x5 .x10 100) ;;             -- ls1 (172-72=100)
  ADDI .x10 .x0 2 ;;
  single (.BEQ .x5 .x10 36)                 -- ls2 (116-80=36)

/-- SAR last limb: LD x5, 24(x12); SRA x5,x5,x6; SD x12,x5,dst_off
    Mirror of shr_last_limb with SRA (arithmetic shift right). -/
def sar_last_limb (dst_off : BitVec 12) : Program :=
  LD .x5 .x12 24 ;;
  single (.SRA .x5 .x5 .x6) ;;
  SD .x12 .x5 dst_off

/-- ls3: limb_shift=3 (8 instructions).
    result[0] = value[3] SRA bs; result[1..3] = sign_ext -/
def sar_body_3 : Program :=
  sar_last_limb 0 ;;
  single (.SRAI .x10 .x5 63) ;;
  SD .x12 .x10 8 ;; SD .x12 .x10 16 ;; SD .x12 .x10 24 ;;
  single (.JAL .x0 268)                      -- exit (380-112=268)

/-- ls2: limb_shift=2 (14 instructions).
    result[0] = merge(value[2],value[3]); result[1] = value[3] SRA bs;
    result[2..3] = sign_ext -/
def sar_body_2 : Program :=
  shr_merge_limb 16 24 0 ;;                  -- same merge as SHR
  sar_last_limb 8 ;;
  single (.SRAI .x10 .x5 63) ;;
  SD .x12 .x10 16 ;; SD .x12 .x10 24 ;;
  single (.JAL .x0 212)                      -- exit (380-168=212)

/-- ls1: limb_shift=1 (20 instructions).
    result[0] = merge(value[1],value[2]); result[1] = merge(value[2],value[3]);
    result[2] = value[3] SRA bs; result[3] = sign_ext -/
def sar_body_1 : Program :=
  shr_merge_limb 8 16 0 ;;
  shr_merge_limb 16 24 8 ;;
  sar_last_limb 16 ;;
  single (.SRAI .x10 .x5 63) ;;
  SD .x12 .x10 24 ;;
  single (.JAL .x0 132)                      -- exit (380-248=132)

/-- ls0: limb_shift=0 (25 instructions).
    result[i] = merge(value[i],value[i+1]) for i=0..2;
    result[3] = value[3] SRA bs. No vacated limbs. -/
def sar_body_0 : Program :=
  shr_merge_limb 0 8 0 ;;
  shr_merge_limb 8 16 8 ;;
  shr_merge_limb 16 24 16 ;;
  sar_last_limb 24 ;;
  single (.JAL .x0 32)                       -- exit (380-348=32)

/-- SAR sign-fill path (7 instructions).
    Compute sign extension from value[3], fill all 4 result limbs.
    Entered when shift >= 256 (before phase B, so shift not yet popped). -/
def sar_sign_fill_path : Program :=
  LD .x5 .x12 56 ;;                          -- value[3] at sp+56 (before pop)
  single (.SRAI .x5 .x5 63) ;;               -- sign extend: 0 or all-1s
  ADDI .x12 .x12 32 ;;                       -- pop shift word
  SD .x12 .x5 0 ;; SD .x12 .x5 8 ;; SD .x12 .x5 16 ;; SD .x12 .x5 24

-- ============================================================================
-- Full SAR program
-- ============================================================================

/-- 256-bit EVM SAR: binary (pop 2, push 1, sp += 32).
    SAR(shift, value) = arithmetic right shift. 95 instructions total.
    Reuses SHR phase B (parameter extraction). -/
def evm_sar : Program :=
  sar_phase_a ;;
  shr_phase_b ;;
  sar_phase_c ;;
  sar_body_3 ;; sar_body_2 ;; sar_body_1 ;; sar_body_0 ;;
  sar_sign_fill_path
  -- Exit: offset 380 (instruction 95)

-- ============================================================================
-- SAR: Instruction count verification + tests
-- ============================================================================

/-- evm_sar has exactly 95 instructions. -/
example : evm_sar.length = 95 := by decide

/-- Create a test state for SAR. -/
def mkSarTestState (sp : Word)
    (s0 s1 s2 s3 : Word) (v0 v1 v2 v3 : Word) : MachineState where
  regs := fun r => match r with | .x12 => sp | _ => 0
  mem := fun a =>
    if a == sp      then s0
    else if a == sp + 8  then s1
    else if a == sp + 16 then s2
    else if a == sp + 24 then s3
    else if a == sp + 32 then v0
    else if a == sp + 40 then v1
    else if a == sp + 48 then v2
    else if a == sp + 56 then v3
    else 0
  code := loadProgram 0 evm_sar
  pc := 0

/-- Run evm_sar and extract 4 result limbs. -/
def runSarResult (sp : Word) (s0 s1 s2 s3 : Word) (v0 v1 v2 v3 : Word)
    (steps : Nat) : Option (List Word) :=
  let s := mkSarTestState sp s0 s1 s2 s3 v0 v1 v2 v3
  match stepN steps s with
  | some s' =>
    let rsp := s'.getReg .x12
    some [s'.getMem rsp, s'.getMem (rsp + 8), s'.getMem (rsp + 16), s'.getMem (rsp + 24)]
  | none => none

/-- Run evm_sar and check PC and x12. -/
def runSarCheck (sp : Word) (s0 s1 s2 s3 : Word) (v0 v1 v2 v3 : Word)
    (steps : Nat) : Option (Word × Word) :=
  let s := mkSarTestState sp s0 s1 s2 s3 v0 v1 v2 v3
  match stepN steps s with
  | some s' => some (s'.pc, s'.getReg .x12)
  | none => none

-- SAR step counts:
-- ls0 (shift 0-63):  9+7+1+25 = 42 steps
-- ls1 (shift 64-127): 9+7+3+20 = 39 steps
-- ls2 (shift 128-191): 9+7+5+14 = 35 steps
-- ls3 (shift 192-255): 9+7+5+8 = 29 steps
-- sign_fill (high limbs nonzero): 6+7 = 13 steps
-- sign_fill (limb0 >= 256): 9+7 = 16 steps

-- Test 1: SAR(0, positive) = identity
/-- SAR by 0 on positive value: result equals input. -/
example : runSarResult 1024 0 0 0 0  0xFF 0 0 0  42 =
    some [0xFF, 0, 0, 0] := by decide

-- Test 2: SAR(1, 0xFF) = 0x7F (positive, ls0)
/-- SAR(1, 0xFF) = 0x7F (positive value, logical shift). -/
example : runSarResult 1024 1 0 0 0  0xFF 0 0 0  42 =
    some [0x7F, 0, 0, 0] := by decide

-- Test 3: SAR(1, negative value) — MSB limb has sign bit set
-- value = [0, 0, 0, 0x8000000000000000] (= -2^255 in signed)
-- SAR(1): result[3] = SRA(0x8000000000000000, 1) = 0xC000000000000000
-- result[2] = (0>>>1) | ((0x8000000000000000 <<< 63) & mask) = 0
-- Actually antiShift = 63, value[3] <<< 63 = 0x8000000000000000 <<< 63 = 0
-- Hmm, let me think more carefully...
-- bit_shift=1, antiShift=63
-- merge(16,24,16): SRL value[2] by 1 | (SLL value[3] by 63) & mask
-- value[2]=0, value[3]=0x8000000000000000
-- SRL 0 by 1 = 0, SLL 0x8000000000000000 by 63 = 0 (bit 63 shifted out)
-- result[2] = 0
-- sar_last(24): SRA 0x8000000000000000 by 1 = 0xC000000000000000
/-- SAR(1, -2^255): sign bit preserved. -/
example : runSarResult 1024 1 0 0 0  0 0 0 0x8000000000000000  42 =
    some [0, 0, 0, 0xC000000000000000] := by decide

-- Test 4: SAR(64, negative) (ls1, 39 steps)
-- value = [0, 0, 0, 0xFFFFFFFFFFFFFFFF]
-- limb_shift=1, bit_shift=0: merge(8,16,0), merge(16,24,8), sar_last(16), fill(24)
-- result[0] = merge(value[1],value[2]) = 0
-- result[1] = merge(value[2],value[3]) = (0>>>0)|((0xFFFF...<<<64)&mask) = 0 (bs=0, mask=0)
-- Actually: bit_shift=0, so mask = 0 (SLTU x0 < x6=0 → false → mask=0)
-- result[0] = value[1] >>> 0 = 0
-- result[1] = value[2] >>> 0 = 0
-- result[2] = value[3] SRA 0 = 0xFFFFFFFFFFFFFFFF
-- result[3] = sign_ext = SRAI(0xFFFFFFFFFFFFFFFF, 63) = 0xFFFFFFFFFFFFFFFF
/-- SAR(64, negative): shift by 1 full limb, sign extends. -/
example : runSarResult 1024 64 0 0 0  0 0 0 0xFFFFFFFFFFFFFFFF  39 =
    some [0, 0, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 5: SAR(192, negative) (ls3, 29 steps)
-- value = [1, 2, 3, 0x8000000000000000]
-- result[0] = value[3] SRA 0 = 0x8000000000000000
-- result[1..3] = sign_ext = 0xFFFFFFFFFFFFFFFF
/-- SAR(192, negative): shift by 3 limbs, sign-fills upper. -/
example : runSarResult 1024 192 0 0 0  1 2 3 0x8000000000000000  29 =
    some [0x8000000000000000, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 6: SAR(256, negative) = all-1s (sign-fill path, 16 steps)
/-- SAR(256, negative): result is all-1s (sign extension). -/
example : runSarResult 1024 256 0 0 0  0 0 0 0x8000000000000000  16 =
    some [0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 7: SAR(256, positive) = all-0s
/-- SAR(256, positive): result is all zeros. -/
example : runSarResult 1024 256 0 0 0  0xFF 0 0 0  16 =
    some [0, 0, 0, 0] := by decide

-- Test 8: SAR with nonzero high shift limb, negative value (13 steps)
/-- SAR with shift > 256 on negative: result is all-1s. -/
example : runSarResult 1024 0 1 0 0  0 0 0 0xFFFFFFFFFFFFFFFF  13 =
    some [0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 9: SAR(128, value) (ls2, 35 steps)
-- value = [0xA, 0xB, 0xC, 0x8000000000000001]
-- merge(16,24,0): result[0] = (value[2]>>>0)|((value[3]<<<64)&mask)
--   bit_shift=0 → mask=0 → result[0] = 0xC
-- sar_last(8): result[1] = value[3] SRA 0 = 0x8000000000000001
-- sign_ext = SRAI(0x8000000000000001, 63) = 0xFFFFFFFFFFFFFFFF
-- result[2] = result[3] = 0xFFFFFFFFFFFFFFFF
/-- SAR(128, negative): shift by 2 limbs. -/
example : runSarResult 1024 128 0 0 0  0xA 0xB 0xC 0x8000000000000001  35 =
    some [0xC, 0x8000000000000001, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 10: SAR(4, all-1s) = all-1s (arithmetic shift preserves sign)
/-- SAR(4, -1) = -1 (all bits 1). -/
example : runSarResult 1024 4 0 0 0
    0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF  42 =
    some [0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF] := by decide

-- Test 11: Verify PC and sp after SAR
/-- After SAR(0, ...), PC = 380 and x12 = sp + 32. -/
example : runSarCheck 1024 0 0 0 0  0xFF 0 0 0  42 =
    some (380, 1056) := by decide

/-- After SAR(256, negative), PC = 380 and x12 = sp + 32. -/
example : runSarCheck 1024 256 0 0 0  0 0 0 0x8000000000000000  16 =
    some (380, 1056) := by decide

-- ============================================================================
-- Parametric program definitions (for specs with symbolic offsets)
-- ============================================================================

/-- Parametric SHR merge limb (7 instructions). -/
def shr_merge_limb_prog (src_off next_off dst_off : BitVec 12) : Program :=
  [.LD .x5 .x12 src_off, .SRL .x5 .x5 .x6, .LD .x10 .x12 next_off,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 dst_off]

/-- Parametric SHR last limb (3 instructions). -/
def shr_last_limb_prog (dst_off : BitVec 12) : Program :=
  [.LD .x5 .x12 24, .SRL .x5 .x5 .x6, .SD .x12 .x5 dst_off]

/-- Parametric SHR merge limb in-place (7 instructions). -/
def shr_merge_limb_inplace_prog (off next_off : BitVec 12) : Program :=
  [.LD .x5 .x12 off, .SRL .x5 .x5 .x6, .LD .x10 .x12 next_off,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 off]

/-- SHR last limb in-place (3 instructions). -/
def shr_last_limb_inplace_prog : Program :=
  [.LD .x5 .x12 24, .SRL .x5 .x5 .x6, .SD .x12 .x5 24]

/-- LD+OR accumulator (2 instructions). -/
def shr_ld_or_acc_prog (off : BitVec 12) : Program :=
  [.LD .x10 .x12 off, .OR .x5 .x5 .x10]

/-- Cascade step: ADDI + BEQ (2 instructions). -/
def shr_cascade_step_prog (k : BitVec 12) (offset : BitVec 13) : Program :=
  [.ADDI .x10 .x0 k, .BEQ .x5 .x10 offset]

/-- Parametric SHR body 3 (7 instructions). -/
def shr_body_3_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 24, .SRL .x5 .x5 .x6, .SD .x12 .x5 0,
   .SD .x12 .x0 8, .SD .x12 .x0 16, .SD .x12 .x0 24, .JAL .x0 jal_off]

/-- Parametric SHR body 2 (13 instructions). -/
def shr_body_2_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 16, .SRL .x5 .x5 .x6, .LD .x10 .x12 24,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 0,
   .LD .x5 .x12 24, .SRL .x5 .x5 .x6, .SD .x12 .x5 8,
   .SD .x12 .x0 16, .SD .x12 .x0 24, .JAL .x0 jal_off]

/-- Parametric SHR body 1 (19 instructions). -/
def shr_body_1_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 8, .SRL .x5 .x5 .x6, .LD .x10 .x12 16,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 0,
   .LD .x5 .x12 16, .SRL .x5 .x5 .x6, .LD .x10 .x12 24,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 8,
   .LD .x5 .x12 24, .SRL .x5 .x5 .x6, .SD .x12 .x5 16,
   .SD .x12 .x0 24, .JAL .x0 jal_off]

/-- Parametric SHR body 0 (25 instructions). -/
def shr_body_0_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 0, .SRL .x5 .x5 .x6, .LD .x10 .x12 8,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 0,
   .LD .x5 .x12 8, .SRL .x5 .x5 .x6, .LD .x10 .x12 16,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 8,
   .LD .x5 .x12 16, .SRL .x5 .x5 .x6, .LD .x10 .x12 24,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 16,
   .LD .x5 .x12 24, .SRL .x5 .x5 .x6, .SD .x12 .x5 24,
   .JAL .x0 jal_off]

/-- Parametric SHL body 3 (7 instructions). -/
def shl_body_3_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 0, .SLL .x5 .x5 .x6, .SD .x12 .x5 24,
   .SD .x12 .x0 16, .SD .x12 .x0 8, .SD .x12 .x0 0, .JAL .x0 jal_off]

/-- Parametric SHL body 2 (13 instructions). -/
def shl_body_2_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 8, .SLL .x5 .x5 .x6, .LD .x10 .x12 0,
   .SRL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 24,
   .LD .x5 .x12 0, .SLL .x5 .x5 .x6, .SD .x12 .x5 16,
   .SD .x12 .x0 8, .SD .x12 .x0 0, .JAL .x0 jal_off]

/-- Parametric SHL body 1 (19 instructions). -/
def shl_body_1_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 16, .SLL .x5 .x5 .x6, .LD .x10 .x12 8,
   .SRL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 24,
   .LD .x5 .x12 8, .SLL .x5 .x5 .x6, .LD .x10 .x12 0,
   .SRL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 16,
   .LD .x5 .x12 0, .SLL .x5 .x5 .x6, .SD .x12 .x5 8,
   .SD .x12 .x0 0, .JAL .x0 jal_off]

/-- Parametric SHL body 0 (25 instructions). -/
def shl_body_0_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 24, .SLL .x5 .x5 .x6, .LD .x10 .x12 16,
   .SRL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 24,
   .LD .x5 .x12 16, .SLL .x5 .x5 .x6, .LD .x10 .x12 8,
   .SRL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 16,
   .LD .x5 .x12 8, .SLL .x5 .x5 .x6, .LD .x10 .x12 0,
   .SRL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 8,
   .LD .x5 .x12 0, .SLL .x5 .x5 .x6, .SD .x12 .x5 0,
   .JAL .x0 jal_off]

/-- Parametric SAR body 3 (8 instructions). -/
def sar_body_3_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 24, .SRA .x5 .x5 .x6, .SD .x12 .x5 0,
   .SRAI .x10 .x5 63, .SD .x12 .x10 8, .SD .x12 .x10 16, .SD .x12 .x10 24,
   .JAL .x0 jal_off]

/-- Parametric SAR body 2 (14 instructions). -/
def sar_body_2_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 16, .SRL .x5 .x5 .x6, .LD .x10 .x12 24,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 0,
   .LD .x5 .x12 24, .SRA .x5 .x5 .x6, .SD .x12 .x5 8,
   .SRAI .x10 .x5 63, .SD .x12 .x10 16, .SD .x12 .x10 24, .JAL .x0 jal_off]

/-- Parametric SAR body 1 (20 instructions). -/
def sar_body_1_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 8, .SRL .x5 .x5 .x6, .LD .x10 .x12 16,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 0,
   .LD .x5 .x12 16, .SRL .x5 .x5 .x6, .LD .x10 .x12 24,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 8,
   .LD .x5 .x12 24, .SRA .x5 .x5 .x6, .SD .x12 .x5 16,
   .SRAI .x10 .x5 63, .SD .x12 .x10 24, .JAL .x0 jal_off]

/-- Parametric SAR body 0 (25 instructions). -/
def sar_body_0_prog (jal_off : BitVec 21) : Program :=
  [.LD .x5 .x12 0, .SRL .x5 .x5 .x6, .LD .x10 .x12 8,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 0,
   .LD .x5 .x12 8, .SRL .x5 .x5 .x6, .LD .x10 .x12 16,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 8,
   .LD .x5 .x12 16, .SRL .x5 .x5 .x6, .LD .x10 .x12 24,
   .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SD .x12 .x5 16,
   .LD .x5 .x12 24, .SRA .x5 .x5 .x6, .SD .x12 .x5 24,
   .JAL .x0 jal_off]

end EvmAsm.Evm64
