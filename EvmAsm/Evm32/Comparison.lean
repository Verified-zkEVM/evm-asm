/-
  EvmAsm.Evm32.Comparison

  256-bit EVM comparison operations (ISZERO, LT) as RISC-V programs.
  ISZERO: unary, OR all 8 limbs, SLTIU to boolean, store result.
  LT: binary, multi-limb subtraction tracking only the borrow.
-/

import EvmAsm.Evm32.Stack
import EvmAsm.Rv32.CPSSpec
import EvmAsm.Rv32.SyscallSpecs
import EvmAsm.Rv32.Tactics.XSimp
import EvmAsm.Rv32.Tactics.RunBlock

open EvmAsm.Tactics

namespace EvmAsm

-- ============================================================================
-- Program Definitions
-- ============================================================================

/-- 256-bit EVM ISZERO: unary (pop 1, push 1, sp unchanged).
    OR all 8 limbs into x7, then SLTIU x7, x7, 1 (x7 = x7 == 0 ? 1 : 0).
    Store 256-bit result: limb[0] = x7, limbs[1-7] = 0 (via x0).
    24 instructions total. -/
def evm_iszero : Program :=
  -- OR reduction: load limb 0, then load & OR limbs 1-7 (15 instructions)
  LW .x7 .x12 0 ;;
  LW .x6 .x12 4  ;; single (.OR .x7 .x7 .x6) ;;
  LW .x6 .x12 8  ;; single (.OR .x7 .x7 .x6) ;;
  LW .x6 .x12 12 ;; single (.OR .x7 .x7 .x6) ;;
  LW .x6 .x12 16 ;; single (.OR .x7 .x7 .x6) ;;
  LW .x6 .x12 20 ;; single (.OR .x7 .x7 .x6) ;;
  LW .x6 .x12 24 ;; single (.OR .x7 .x7 .x6) ;;
  LW .x6 .x12 28 ;; single (.OR .x7 .x7 .x6) ;;
  -- Convert to boolean (1 instruction)
  single (.SLTIU .x7 .x7 1) ;;
  -- Store 256-bit result: limb[0] = x7, limbs[1-7] = 0 (8 instructions)
  SW .x12 .x7 0 ;;
  SW .x12 .x0 4 ;; SW .x12 .x0 8 ;; SW .x12 .x0 12 ;;
  SW .x12 .x0 16 ;; SW .x12 .x0 20 ;; SW .x12 .x0 24 ;; SW .x12 .x0 28

/-- 256-bit EVM LT: binary (pop 2, push 1, sp += 32).
    Computes a < b by tracking borrow across multi-limb subtraction.
    Final borrow = 1 iff a < b. Store boolean result as 256-bit value.
    54 instructions total. -/
def evm_lt : Program :=
  -- Limb 0 (3 instructions): borrow detection only, no store
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;; single (.SLTU .x5 .x7 .x6) ;;
  -- Limbs 1-7 (6 instructions each): borrow propagation, no store
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 2
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 3
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 4
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 5
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 6
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 7
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- sp adjustment + store 256-bit result (9 instructions)
  ADDI .x12 .x12 32 ;;
  SW .x12 .x5 0 ;;
  SW .x12 .x0 4 ;; SW .x12 .x0 8 ;; SW .x12 .x0 12 ;;
  SW .x12 .x0 16 ;; SW .x12 .x0 20 ;; SW .x12 .x0 24 ;; SW .x12 .x0 28

/-- 256-bit EVM GT: binary (pop 2, push 1, sp += 32).
    GT(a, b) = LT(b, a): swap load order vs evm_lt (b loaded first into x7, a into x6).
    Computes b < a by tracking borrow across multi-limb subtraction.
    Final borrow = 1 iff b < a, i.e. a > b. Store boolean result as 256-bit value.
    54 instructions total. -/
def evm_gt : Program :=
  -- Limb 0 (3 instructions): load b (sp+32) into x7, a (sp+0) into x6, borrow = (b < a)
  LW .x7 .x12 32 ;; LW .x6 .x12 0 ;; single (.SLTU .x5 .x7 .x6) ;;
  -- Limbs 1-7 (6 instructions each): borrow propagation (b_k - a_k with borrow_in)
  -- Limb 1: b at sp+36, a at sp+4
  LW .x7 .x12 36 ;; LW .x6 .x12 4 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 2: b at sp+40, a at sp+8
  LW .x7 .x12 40 ;; LW .x6 .x12 8 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 3: b at sp+44, a at sp+12
  LW .x7 .x12 44 ;; LW .x6 .x12 12 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 4: b at sp+48, a at sp+16
  LW .x7 .x12 48 ;; LW .x6 .x12 16 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 5: b at sp+52, a at sp+20
  LW .x7 .x12 52 ;; LW .x6 .x12 20 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 6: b at sp+56, a at sp+24
  LW .x7 .x12 56 ;; LW .x6 .x12 24 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 7: b at sp+60, a at sp+28
  LW .x7 .x12 60 ;; LW .x6 .x12 28 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- sp adjustment + store 256-bit result (9 instructions)
  ADDI .x12 .x12 32 ;;
  SW .x12 .x5 0 ;;
  SW .x12 .x0 4 ;; SW .x12 .x0 8 ;; SW .x12 .x0 12 ;;
  SW .x12 .x0 16 ;; SW .x12 .x0 20 ;; SW .x12 .x0 24 ;; SW .x12 .x0 28

/-- 256-bit EVM EQ: binary (pop 2, push 1, sp += 32).
    XOR each limb pair (a_k XOR b_k), OR-reduce all XORs, SLTIU to boolean.
    Result = 1 iff a == b as 256-bit words.
    41 instructions total: 3 (limb0) + 7×4 (limbs1-7) + 1 (SLTIU) + 1 (ADDI) + 8 (SWs). -/
def evm_eq : Program :=
  -- Limb 0 (3 instructions): load a0 into x7, b0 into x6, XOR them
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;; single (.XOR .x7 .x7 .x6) ;;
  -- Limb 1 (4 instructions): load a1 into x6, b1 into x5, XOR, OR-accumulate
  LW .x6 .x12 4 ;; LW .x5 .x12 36 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Limb 2
  LW .x6 .x12 8 ;; LW .x5 .x12 40 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Limb 3
  LW .x6 .x12 12 ;; LW .x5 .x12 44 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Limb 4
  LW .x6 .x12 16 ;; LW .x5 .x12 48 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Limb 5
  LW .x6 .x12 20 ;; LW .x5 .x12 52 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Limb 6
  LW .x6 .x12 24 ;; LW .x5 .x12 56 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Limb 7
  LW .x6 .x12 28 ;; LW .x5 .x12 60 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Convert OR-reduced XOR to boolean: x7 = (x7 == 0) ? 1 : 0
  single (.SLTIU .x7 .x7 1) ;;
  -- sp adjustment + store 256-bit result (9 instructions)
  ADDI .x12 .x12 32 ;;
  SW .x12 .x7 0 ;;
  SW .x12 .x0 4 ;; SW .x12 .x0 8 ;; SW .x12 .x0 12 ;;
  SW .x12 .x0 16 ;; SW .x12 .x0 20 ;; SW .x12 .x0 24 ;; SW .x12 .x0 28

-- ============================================================================
-- Utility: x0 always holds 0
-- ============================================================================

/-- The x0 register always reads as 0 in any machine state. -/
theorem holdsFor_regIs_x0_zero (s : MachineState) : (.x0 ↦ᵣ (0 : Word)).holdsFor s := by
  rw [holdsFor_regIs]; rfl

-- ============================================================================
-- Per-limb Specs: LT (borrow propagation without storing results)
-- ============================================================================

/-- LT limb 0 spec (3 instructions): LW, LW, SLTU.
    Computes initial borrow = (a < b ? 1 : 0). Does NOT modify memory. -/
theorem lt_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let code :=
      (base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .SLTU .x5 .x7 .x6)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a_limb) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

/-- LT carry limb spec (6 instructions): LW, LW, SLTU, SUB, SLTU, OR.
    Propagates borrow without storing result. Memory is NOT modified.
    borrow1 = (a < b), temp = a - b, borrow2 = (temp < borrow_in),
    borrow_out = borrow1 | borrow2. -/
theorem lt_limb_carry_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 borrow_in v11 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow1 := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let temp := a_limb - b_limb
    let borrow2 := if BitVec.ult temp borrow_in then (1 : Word) else 0
    let borrow_out := borrow1 ||| borrow2
    let code :=
      (base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .SLTU .x11 .x7 .x6) ** ((base + 12) ↦ᵢ .SUB .x7 .x7 .x6) **
      ((base + 16) ↦ᵢ .SLTU .x6 .x7 .x5) ** ((base + 20) ↦ᵢ .OR .x5 .x11 .x6)
    cpsTriple base (base + 24)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrow_out) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

-- ============================================================================
-- Per-limb Specs: EQ (XOR + OR accumulation)
-- ============================================================================

/-- EQ limb 0 spec (3 instructions): LW x7, LW x6, XOR x7 x7 x6.
    Loads a and b limbs, XORs them into x7. Memory unchanged. -/
theorem eq_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let code :=
      (base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ^^^ b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

/-- EQ OR-limb spec (4 instructions): LW x6, LW x5, XOR x6 x6 x5, OR x7 x7 x6.
    Loads a_k into x6, b_k into x5, XORs them (x6 := a_k XOR b_k),
    then OR-accumulates into x7 (x7 := acc ||| (a_k XOR b_k)). Memory unchanged. -/
theorem eq_or_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v6 v5 acc : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let xor_k := a_limb ^^^ b_limb
    let code :=
      (base ↦ᵢ .LW .x6 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x5 .x12 off_b) **
      ((base + 8) ↦ᵢ .XOR .x6 .x6 .x5) ** ((base + 12) ↦ᵢ .OR .x7 .x7 .x6)
    cpsTriple base (base + 16)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ acc) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (acc ||| xor_k)) ** (.x6 ↦ᵣ xor_k) ** (.x5 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

end EvmAsm
