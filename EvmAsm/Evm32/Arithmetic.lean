/-
  EvmAsm.Evm32.Arithmetic

  256-bit EVM arithmetic operations (ADD, SUB) as RISC-V programs.
  Each operates on 8 little-endian 32-bit limbs stored in memory,
  propagating carry/borrow across limbs.
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

/-- 256-bit EVM ADD: binary, pops 2, pushes 1.
    Limb 0: LW, LW, ADD, SLTU (carry), SW (5 instructions).
    Limbs 1-7: LW, LW, ADD, SLTU (carry1), ADD (carry_in), SLTU (carry2), OR (carry_out), SW (8 instructions each).
    Then ADDI sp, sp, 32.
    Registers: x12=sp, x7=acc, x6=operand, x5=carry, x11=carry1. -/
def evm_add : Program :=
  -- Limb 0 (5 instructions): carry detection via SLTU after ADD
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x5 .x7 .x6) ;; SW .x12 .x7 32 ;;
  -- Limb 1 (8 instructions)
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 36 ;;
  -- Limb 2
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 40 ;;
  -- Limb 3
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 44 ;;
  -- Limb 4
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 48 ;;
  -- Limb 5
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 52 ;;
  -- Limb 6
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 56 ;;
  -- Limb 7
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 60 ;;
  -- sp adjustment
  ADDI .x12 .x12 32

/-- 256-bit EVM SUB: binary, pops 2, pushes 1.
    Limb 0: LW, LW, SLTU (borrow), SUB, SW (5 instructions).
    Limbs 1-7: LW, LW, SLTU (borrow1), SUB, SLTU (borrow2), SUB (borrow_in), OR (borrow_out), SW (8 instructions each).
    Then ADDI sp, sp, 32. -/
def evm_sub : Program :=
  -- Limb 0 (5 instructions): borrow detection via SLTU before SUB
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;;
  single (.SLTU .x5 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;; SW .x12 .x7 32 ;;
  -- Limb 1 (8 instructions)
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 36 ;;
  -- Limb 2
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 40 ;;
  -- Limb 3
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 44 ;;
  -- Limb 4
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 48 ;;
  -- Limb 5
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 52 ;;
  -- Limb 6
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 56 ;;
  -- Limb 7
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 60 ;;
  -- sp adjustment
  ADDI .x12 .x12 32

-- ============================================================================
-- Per-limb Specs: ADD
-- ============================================================================

/-- ADD limb 0 spec (5 instructions): LW, LW, ADD, SLTU, SW.
    Computes sum = a + b (mod 2^32) and carry = (sum < b ? 1 : 0). -/
theorem add_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let sum := a_limb + b_limb
    let carry := if BitVec.ult sum b_limb then (1 : Word) else 0
    let code :=
      (base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
      ((base + 16) ↦ᵢ .SW .x12 .x7 off_b)
    cpsTriple base (base + 20)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ sum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ sum)) := by
  runBlock

-- ============================================================================
-- Per-limb Specs: ADD with carry (limbs 1-7)
-- ============================================================================

/-- ADD carry limb phase 1 (4 instructions): LW, LW, ADD, SLTU.
    Loads a_limb and b_limb, computes psum = a + b, carry1 = (psum < b ? 1 : 0). -/
theorem add_limb_carry_spec_phase1 (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 carry_in v11 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let psum := a_limb + b_limb
    let carry1 := if BitVec.ult psum b_limb then (1 : Word) else 0
    let code :=
      (base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x11 .x7 .x6)
    cpsTriple base (base + 16)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ psum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

/-- ADD carry limb phase 2 (4 instructions): ADD, SLTU, OR, SW.
    Takes psum, carry1, carry_in, computes result = psum + carry_in,
    carry2 = (result < carry_in ? 1 : 0), carry_out = carry1 ||| carry2. -/
theorem add_limb_carry_spec_phase2 (off_b : BitVec 12)
    (sp psum b_limb carry_in carry1 a_limb : Word) (mem_a : Addr) (base : Addr)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_b := sp + signExtend12 off_b
    let result := psum + carry_in
    let carry2 := if BitVec.ult result carry_in then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let code :=
      (base ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 4) ↦ᵢ .SLTU .x6 .x7 .x5) **
      ((base + 8) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 off_b)
    cpsTriple base (base + 16)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ psum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ carry2) ** (.x5 ↦ᵣ carry_out) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  runBlock

/-- ADD carry limb spec (8 instructions): LW, LW, ADD, SLTU, ADD, SLTU, OR, SW.
    Takes carry_in, produces carry_out = carry1 ||| carry2 where:
    - partial = a + b, carry1 = (partial < b ? 1 : 0)
    - result = partial + carry_in, carry2 = (result < carry_in ? 1 : 0)
    Composed from phase1 (steps 1-4) and phase2 (steps 5-8). -/
theorem add_limb_carry_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 carry_in v11 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let psum := a_limb + b_limb
    let carry1 := if BitVec.ult psum b_limb then (1 : Word) else 0
    let result := psum + carry_in
    let carry2 := if BitVec.ult result carry_in then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let code :=
      (base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x11 .x7 .x6) **
      ((base + 16) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 20) ↦ᵢ .SLTU .x6 .x7 .x5) **
      ((base + 24) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 off_b)
    cpsTriple base (base + 32)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ carry2) ** (.x5 ↦ᵣ carry_out) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  have p1 := add_limb_carry_spec_phase1 off_a off_b sp a_limb b_limb v7 v6 carry_in v11 base
    hvalid_a hvalid_b
  have p2 := add_limb_carry_spec_phase2 off_b sp (a_limb + b_limb) b_limb carry_in
    (if BitVec.ult (a_limb + b_limb) b_limb then (1 : Word) else 0)
    a_limb (sp + signExtend12 off_a) (base + 16) hvalid_b
  runBlock p1 p2

-- ============================================================================
-- Per-limb Specs: SUB
-- ============================================================================

/-- SUB limb 0 spec (5 instructions): LW, LW, SLTU, SUB, SW.
    Computes diff = a - b (mod 2^32) and borrow = (a < b ? 1 : 0). -/
theorem sub_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let diff := a_limb - b_limb
    let code :=
      (base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .SLTU .x5 .x7 .x6) ** ((base + 12) ↦ᵢ .SUB .x7 .x7 .x6) **
      ((base + 16) ↦ᵢ .SW .x12 .x7 off_b)
    cpsTriple base (base + 20)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ diff) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ diff)) := by
  runBlock

/-- SUB carry limb phase 1 (4 instructions): LW, LW, SLTU, SUB.
    Loads a_limb and b_limb, computes borrow1 = (a < b ? 1 : 0), temp = a - b. -/
theorem sub_limb_carry_spec_phase1 (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 borrow_in v11 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow1 := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let temp := a_limb - b_limb
    let code :=
      (base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .SLTU .x11 .x7 .x6) ** ((base + 12) ↦ᵢ .SUB .x7 .x7 .x6)
    cpsTriple base (base + 16)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

/-- SUB carry limb phase 2 (4 instructions): SLTU, SUB, OR, SW.
    Takes temp, borrow1, borrow_in, computes borrow2 = (temp < borrow_in ? 1 : 0),
    result = temp - borrow_in, borrow_out = borrow1 ||| borrow2. -/
theorem sub_limb_carry_spec_phase2 (off_b : BitVec 12)
    (sp temp b_limb borrow_in borrow1 a_limb : Word) (mem_a : Addr) (base : Addr)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_b := sp + signExtend12 off_b
    let borrow2 := if BitVec.ult temp borrow_in then (1 : Word) else 0
    let result := temp - borrow_in
    let borrow_out := borrow1 ||| borrow2
    let code :=
      (base ↦ᵢ .SLTU .x6 .x7 .x5) ** ((base + 4) ↦ᵢ .SUB .x7 .x7 .x5) **
      ((base + 8) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 off_b)
    cpsTriple base (base + 16)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrow_out) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  runBlock

/-- SUB carry limb spec (8 instructions): LW, LW, SLTU, SUB, SLTU, SUB, OR, SW.
    Takes borrow_in, produces borrow_out = borrow1 ||| borrow2 where:
    - borrow1 = (a < b ? 1 : 0), temp = a - b
    - borrow2 = (temp < borrow_in ? 1 : 0), result = temp - borrow_in
    Composed from phase1 (steps 1-4) and phase2 (steps 5-8). -/
theorem sub_limb_carry_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 borrow_in v11 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow1 := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let temp := a_limb - b_limb
    let borrow2 := if BitVec.ult temp borrow_in then (1 : Word) else 0
    let result := temp - borrow_in
    let borrow_out := borrow1 ||| borrow2
    let code :=
      (base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .SLTU .x11 .x7 .x6) ** ((base + 12) ↦ᵢ .SUB .x7 .x7 .x6) **
      ((base + 16) ↦ᵢ .SLTU .x6 .x7 .x5) ** ((base + 20) ↦ᵢ .SUB .x7 .x7 .x5) **
      ((base + 24) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 off_b)
    cpsTriple base (base + 32)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrow_out) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  have p1 := sub_limb_carry_spec_phase1 off_a off_b sp a_limb b_limb v7 v6 borrow_in v11 base
    hvalid_a hvalid_b
  have p2 := sub_limb_carry_spec_phase2 off_b sp (a_limb - b_limb) b_limb borrow_in
    (if BitVec.ult a_limb b_limb then (1 : Word) else 0)
    a_limb (sp + signExtend12 off_a) (base + 16) hvalid_b
  runBlock p1 p2

end EvmAsm
