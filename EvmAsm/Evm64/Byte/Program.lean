/-
  EvmAsm.Evm64.Byte

  256-bit EVM BYTE (extract byte from word) as a 64-bit RISC-V program.
  BYTE(index, value) pops index and value, pushes byte at position index.
  If index >= 32, the result is 0.

  EVM byte numbering is big-endian: byte 0 = MSB, byte 31 = LSB.
  With little-endian 64-bit limb layout:
    limb 0 (sp+32): bits 0-63,   EVM bytes 31-24
    limb 1 (sp+40): bits 64-127, EVM bytes 23-16
    limb 2 (sp+48): bits 128-191,EVM bytes 15-8
    limb 3 (sp+56): bits 192-255,EVM bytes 7-0

  For EVM byte i (0-31):
    limb_from_msb = i / 8   (0=limb3, 1=limb2, 2=limb1, 3=limb0)
    byte_within_limb = i % 8 (0=MSB byte of limb, 7=LSB byte)
    bit_shift = 56 - (i % 8) * 8

  Register allocation:
    x12 = EVM stack pointer
    x5  = temp (index, then limb value, then byte result)
    x6  = bit_shift amount
    x10 = temp

  Program layout (45 instructions = 180 bytes):
    Phase A (9 instrs):   Check index >= 32
    Phase B (5 instrs):   Compute bit_shift and limb_from_msb
    Phase C (5 instrs):   Cascade dispatch on limb_from_msb
    body_3 (4 instrs):    Extract from limb 0 (sp+32)
    body_2 (4 instrs):    Extract from limb 1 (sp+40)
    body_1 (4 instrs):    Extract from limb 2 (sp+48)
    body_0 (3 instrs):    Extract from limb 3 (sp+56)
    Store  (6 instrs):    Pop index, store result + zeros
    Zero   (5 instrs):    Pop index, store zeros
    Exit point: offset 180
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Sub-program definitions
-- ============================================================================

/-- Phase A: Check index >= 32 (9 instructions).
    OR-reduce index limbs 1-3. BNE to zero_path if nonzero.
    Then check limb 0 < 32. BEQ to zero_path if not. -/
def byte_phase_a : Program :=
  LD .x5  .x12 8  ;;                          -- x5  = index[1]
  LD .x10 .x12 16 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= index[2]
  LD .x10 .x12 24 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= index[3]
  single (.BNE .x5 .x0 140) ;;               -- high limbs nonzero → zero_path (160-20=140)
  LD .x5  .x12 0  ;;                          -- x5 = index[0]
  single (.SLTIU .x10 .x5 32) ;;             -- x10 = (index[0] < 32)
  single (.BEQ .x10 .x0 128)                  -- index[0] >= 32 → zero_path (160-32=128)

/-- Phase B: Compute bit_shift and limb_from_msb (5 instructions).
    bit_shift = 56 - (index % 8) * 8, stored in x6.
    limb_from_msb = index / 8, stored in x5. -/
def byte_phase_b : Program :=
  single (.ANDI .x10 .x5 7) ;;               -- x10 = index % 8
  single (.SLLI .x10 .x10 3) ;;              -- x10 = (index % 8) * 8
  ADDI .x6 .x0 56 ;;                         -- x6 = 56
  single (.SUB .x6 .x6 .x10) ;;              -- x6 = 56 - (index%8)*8
  single (.SRLI .x5 .x5 3)                   -- x5 = index / 8

/-- Phase C: Cascade dispatch (5 instructions).
    Branch on x5 (limb_from_msb) to load the correct limb. -/
def byte_phase_c : Program :=
  single (.BEQ .x5 .x0 68) ;;               -- body_0 (124-56=68)
  ADDI .x10 .x0 1 ;;
  single (.BEQ .x5 .x10 44) ;;              -- body_1 (108-64=44)
  ADDI .x10 .x0 2 ;;
  single (.BEQ .x5 .x10 20)                 -- body_2 (92-72=20)

/-- body_3: limb_from_msb=3, extract from limb 0 at sp+32 (4 instrs). -/
def byte_body_3 : Program :=
  LD .x5 .x12 32 ;;
  single (.SRL .x5 .x5 .x6) ;;
  single (.ANDI .x5 .x5 255) ;;
  single (.JAL .x0 48)                       -- store (136-88=48)

/-- body_2: limb_from_msb=2, extract from limb 1 at sp+40 (4 instrs). -/
def byte_body_2 : Program :=
  LD .x5 .x12 40 ;;
  single (.SRL .x5 .x5 .x6) ;;
  single (.ANDI .x5 .x5 255) ;;
  single (.JAL .x0 32)                       -- store (136-104=32)

/-- body_1: limb_from_msb=1, extract from limb 2 at sp+48 (4 instrs). -/
def byte_body_1 : Program :=
  LD .x5 .x12 48 ;;
  single (.SRL .x5 .x5 .x6) ;;
  single (.ANDI .x5 .x5 255) ;;
  single (.JAL .x0 16)                       -- store (136-120=16)

/-- body_0: limb_from_msb=0, extract from limb 3 at sp+56 (3 instrs).
    Falls through to store. -/
def byte_body_0 : Program :=
  LD .x5 .x12 56 ;;
  single (.SRL .x5 .x5 .x6) ;;
  single (.ANDI .x5 .x5 255)

/-- Store path: pop index word, write byte result + 3 zero limbs (6 instrs). -/
def byte_store : Program :=
  ADDI .x12 .x12 32 ;;                       -- pop index word
  SD .x12 .x5 0 ;;                           -- result[0] = byte value
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24 ;;  -- result[1..3] = 0
  single (.JAL .x0 24)                       -- exit (180-156=24)

/-- Zero path: pop index word, write all zeros (5 instrs). -/
def byte_zero_path : Program :=
  ADDI .x12 .x12 32 ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

-- ============================================================================
-- Full BYTE program
-- ============================================================================

/-- 256-bit EVM BYTE: binary (pop 2, push 1, sp += 32).
    BYTE(index, value) = byte at big-endian position index. 45 instructions total. -/
def evm_byte : Program :=
  byte_phase_a ;;
  byte_phase_b ;;
  byte_phase_c ;;
  byte_body_3 ;; byte_body_2 ;; byte_body_1 ;; byte_body_0 ;;
  byte_store ;;
  byte_zero_path
  -- Exit: offset 180 (instruction 45)

-- ============================================================================
-- Instruction count verification
-- ============================================================================

/-- evm_byte has exactly 45 instructions. -/
example : evm_byte.length = 45 := by decide

-- ============================================================================
-- Test infrastructure
-- ============================================================================

/-- Create a test state for BYTE with index and value on the stack.
    Memory layout: sp → [idx0..idx3, v0..v3] (8 doublewords). -/
def mkByteTestState (sp : Word)
    (idx0 idx1 idx2 idx3 : Word)  -- index limbs (LE)
    (v0 v1 v2 v3 : Word)         -- value limbs (LE)
    : MachineState where
  regs := fun r =>
    match r with
    | .x12 => sp
    | _    => 0
  mem := fun a =>
    if a == sp      then idx0
    else if a == sp + 8  then idx1
    else if a == sp + 16 then idx2
    else if a == sp + 24 then idx3
    else if a == sp + 32 then v0
    else if a == sp + 40 then v1
    else if a == sp + 48 then v2
    else if a == sp + 56 then v3
    else 0
  code := loadProgram 0 evm_byte
  pc := 0

/-- Run evm_byte and extract 4 result limbs. -/
def runByteResult (sp : Word)
    (idx0 idx1 idx2 idx3 : Word)
    (v0 v1 v2 v3 : Word)
    (steps : Nat) : Option (List Word) :=
  let s := mkByteTestState sp idx0 idx1 idx2 idx3 v0 v1 v2 v3
  match stepN steps s with
  | some s' =>
    let rsp := s'.getReg .x12
    some [s'.getMem rsp, s'.getMem (rsp + 8), s'.getMem (rsp + 16), s'.getMem (rsp + 24)]
  | none => none

/-- Run evm_byte and check PC and x12. -/
def runByteCheck (sp : Word)
    (idx0 idx1 idx2 idx3 : Word)
    (v0 v1 v2 v3 : Word)
    (steps : Nat) : Option (Word × Word) :=
  let s := mkByteTestState sp idx0 idx1 idx2 idx3 v0 v1 v2 v3
  match stepN steps s with
  | some s' => some (s'.pc, s'.getReg .x12)
  | none => none

-- ============================================================================
-- Concrete tests via decide
-- ============================================================================

-- Step counts by path:
-- body_0 (byte 0-7,   limb 3): 9+5+1+3+6 = 24 steps
-- body_1 (byte 8-15,  limb 2): 9+5+3+4+6 = 27 steps
-- body_2 (byte 16-23, limb 1): 9+5+5+4+6 = 29 steps
-- body_3 (byte 24-31, limb 0): 9+5+5+4+6 = 29 steps
-- zero_path (high limbs nonzero): 6+5 = 11 steps
-- zero_path (index >= 32): 9+5 = 14 steps

-- Test 1: BYTE(31, 0xFF) = 0xFF (byte 31 = LSB of limb 0, body_3 path)
-- limb 0 = 0xFF, shift = 56 - (31%8)*8 = 56 - 56 = 0, mask 0xFF → 0xFF
/-- BYTE(31, 0xFF): extract LSB. -/
example : runByteResult 1024 31 0 0 0  0xFF 0 0 0  29 =
    some [0xFF, 0, 0, 0] := by decide

-- Test 2: BYTE(0, value) where value has MSB = 0xAB (byte 0 = MSB of limb 3)
-- limb 3 = 0xAB00000000000000, shift = 56 - 0 = 56, (0xAB00000000000000 >>> 56) & 0xFF = 0xAB
/-- BYTE(0, ...): extract MSB. -/
example : runByteResult 1024 0 0 0 0  0 0 0 0xAB00000000000000  24 =
    some [0xAB, 0, 0, 0] := by decide

-- Test 3: BYTE(32, value) = 0 (index out of range, zero path via SLTIU)
/-- BYTE(32, ...): out of range, result is 0. -/
example : runByteResult 1024 32 0 0 0  0xFF 0 0 0  14 =
    some [0, 0, 0, 0] := by decide

-- Test 4: BYTE with nonzero high index limb (zero path via BNE)
/-- BYTE with high index limbs: result is 0. -/
example : runByteResult 1024 0 1 0 0  0xFF 0 0 0  11 =
    some [0, 0, 0, 0] := by decide

-- Test 5: BYTE(7, value) = LSB byte of limb 3 (body_0 path)
-- limb 3 = 0x0102030405060708, byte 7 = LSB of limb 3
-- shift = 56 - 7*8 = 56-56 = 0, (0x0102030405060708 >>> 0) & 0xFF = 0x08
/-- BYTE(7, ...): last byte of MSB limb. -/
example : runByteResult 1024 7 0 0 0  0 0 0 0x0102030405060708  24 =
    some [0x08, 0, 0, 0] := by decide

-- Test 6: BYTE(8, value) = MSB byte of limb 2 (body_1 path)
-- limb 2 = 0xABCDEF0012345678, byte 8 = MSB of limb 2
-- shift = 56 - 0*8 = 56, (0xABCDEF0012345678 >>> 56) & 0xFF = 0xAB
/-- BYTE(8, ...): first byte of second-from-MSB limb. -/
example : runByteResult 1024 8 0 0 0  0 0 0xABCDEF0012345678 0  27 =
    some [0xAB, 0, 0, 0] := by decide

-- Test 7: BYTE(16, value) = MSB byte of limb 1 (body_2 path)
-- limb 1 = 0x1234567890ABCDEF, shift = 56
-- (0x1234567890ABCDEF >>> 56) & 0xFF = 0x12
/-- BYTE(16, ...): first byte of limb 1. -/
example : runByteResult 1024 16 0 0 0  0 0x1234567890ABCDEF 0 0  29 =
    some [0x12, 0, 0, 0] := by decide

-- Test 8: BYTE(24, value) = MSB byte of limb 0 (body_3 path)
-- limb 0 = 0xFEDCBA9876543210, shift = 56
-- (0xFEDCBA9876543210 >>> 56) & 0xFF = 0xFE
/-- BYTE(24, ...): first byte of LSB limb. -/
example : runByteResult 1024 24 0 0 0  0xFEDCBA9876543210 0 0 0  29 =
    some [0xFE, 0, 0, 0] := by decide

-- Test 9: BYTE(0, 0) = 0
/-- BYTE(0, 0): zero value. -/
example : runByteResult 1024 0 0 0 0  0 0 0 0  24 =
    some [0, 0, 0, 0] := by decide

-- Test 10: BYTE(15, value) = LSB byte of limb 2 (body_1 path)
-- limb 2 = 0xABCDEF0012345678, byte 15 = LSB of limb 2
-- shift = 56 - 7*8 = 0, (0xABCDEF0012345678 >>> 0) & 0xFF = 0x78
/-- BYTE(15, ...): last byte of limb 2. -/
example : runByteResult 1024 15 0 0 0  0 0 0xABCDEF0012345678 0  27 =
    some [0x78, 0, 0, 0] := by decide

-- Test 11: Verify PC and sp are correct after execution
/-- After BYTE(0, ...), PC = 180 and x12 = sp + 32. -/
example : runByteCheck 1024 0 0 0 0  0 0 0 1  24 =
    some (180, 1056) := by decide

/-- After BYTE(32, ...), PC = 180 and x12 = sp + 32. -/
example : runByteCheck 1024 32 0 0 0  0xFF 0 0 0  14 =
    some (180, 1056) := by decide

-- Test 12: BYTE(3, value) with value = 0x...00112233445566778899AABBCCDDEEFF00112233
-- We set limb 3 = 0x00112233_44556677, byte 3 = 0x33
-- shift = 56 - 3*8 = 32, (0x0011223344556677 >>> 32) & 0xFF = 0x33
/-- BYTE(3, ...): byte 3 from MSB limb. -/
example : runByteResult 1024 3 0 0 0  0 0 0 0x0011223344556677  24 =
    some [0x33, 0, 0, 0] := by decide

end EvmAsm.Evm64
