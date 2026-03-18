/-
  EvmAsm.Evm64.Arithmetic

  256-bit EVM arithmetic operations (ADD, SUB) as RV64 programs.
  Each operates on 4 little-endian 64-bit limbs stored in memory,
  propagating carry/borrow across limbs.

  Per-limb specs are defined here; full composition specs are in
  Add.lean and Sub.lean (which can build in parallel).
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Program Definitions
-- ============================================================================

/-- 256-bit EVM ADD: binary, pops 2, pushes 1.
    Limb 0: LD, LD, ADD, SLTU (carry), SD (5 instructions).
    Limbs 1-3: LD, LD, ADD, SLTU (carry1), ADD (carry_in), SLTU (carry2), OR (carry_out), SD (8 each).
    Then ADDI sp, sp, 32.
    Registers: x12=sp, x7=acc, x6=operand, x5=carry, x11=carry1. -/
def evm_add : Program :=
  -- Limb 0 (5 instructions)
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x5 .x7 .x6) ;; SD .x12 .x7 32 ;;
  -- Limb 1 (8 instructions)
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SD .x12 .x7 40 ;;
  -- Limb 2 (8 instructions)
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SD .x12 .x7 48 ;;
  -- Limb 3 (8 instructions)
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SD .x12 .x7 56 ;;
  -- sp adjustment
  ADDI .x12 .x12 32

/-- 256-bit EVM SUB: binary, pops 2, pushes 1.
    Limb 0: LD, LD, SLTU (borrow), SUB, SD (5 instructions).
    Limbs 1-3: LD, LD, SLTU (borrow1), SUB, SLTU (borrow2), SUB (borrow_in), OR (borrow_out), SD (8 each).
    Then ADDI sp, sp, 32. -/
def evm_sub : Program :=
  -- Limb 0 (5 instructions)
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;;
  single (.SLTU .x5 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;; SD .x12 .x7 32 ;;
  -- Limb 1 (8 instructions)
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SD .x12 .x7 40 ;;
  -- Limb 2 (8 instructions)
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SD .x12 .x7 48 ;;
  -- Limb 3 (8 instructions)
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SD .x12 .x7 56 ;;
  -- sp adjustment
  ADDI .x12 .x12 32

-- ============================================================================
-- Per-limb Specs: ADD
-- ============================================================================

/-- ADD limb 0 spec (5 instructions): LD, LD, ADD, SLTU, SD.
    Computes sum = a + b (mod 2^64) and carry = (sum < b ? 1 : 0). -/
theorem add_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let sum := a_limb + b_limb
    let carry := if BitVec.ult sum b_limb then (1 : Word) else 0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x5 .x7 .x6))
       (CodeReq.singleton (base + 16) (.SD .x12 .x7 off_b)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ sum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ sum)) := by
  runBlock

-- ============================================================================
-- Per-limb Specs: ADD with carry (limbs 1-3)
-- ============================================================================

/-- ADD carry limb phase 1 (4 instructions): LD, LD, ADD, SLTU.
    Loads a_limb and b_limb, computes psum = a + b, carry1 = (psum < b ? 1 : 0). -/
theorem add_limb_carry_spec_phase1 (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 carry_in v11 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let psum := a_limb + b_limb
    let carry1 := if BitVec.ult psum b_limb then (1 : Word) else 0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SLTU .x11 .x7 .x6))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ psum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

/-- ADD carry limb phase 2 (4 instructions): ADD, SLTU, OR, SD.
    Takes psum, carry1, carry_in, computes result = psum + carry_in,
    carry2 = (result < carry_in ? 1 : 0), carry_out = carry1 ||| carry2. -/
theorem add_limb_carry_spec_phase2 (off_b : BitVec 12)
    (sp psum b_limb carry_in carry1 a_limb : Word) (mem_a : Addr) (base : Addr)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_b := sp + signExtend12 off_b
    let result := psum + carry_in
    let carry2 := if BitVec.ult result carry_in then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADD .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x6 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x5 .x11 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 off_b))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ psum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ carry2) ** (.x5 ↦ᵣ carry_out) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  runBlock

/-- ADD carry limb spec (8 instructions): LD, LD, ADD, SLTU, ADD, SLTU, OR, SD.
    Composed from phase1 and phase2. -/
theorem add_limb_carry_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 carry_in v11 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let psum := a_limb + b_limb
    let carry1 := if BitVec.ult psum b_limb then (1 : Word) else 0
    let result := psum + carry_in
    let carry2 := if BitVec.ult result carry_in then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x11 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 16) (.ADD .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SLTU .x6 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x5 .x11 .x6))
       (CodeReq.singleton (base + 28) (.SD .x12 .x7 off_b))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ carry2) ** (.x5 ↦ᵣ carry_out) ** (.x11 ↦ᵣ carry1) **
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

/-- SUB limb 0 spec (5 instructions): LD, LD, SLTU, SUB, SD.
    Computes diff = a - b (mod 2^64) and borrow = (a < b ? 1 : 0). -/
theorem sub_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let diff := a_limb - b_limb
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x7 .x7 .x6))
       (CodeReq.singleton (base + 16) (.SD .x12 .x7 off_b)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ diff) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ diff)) := by
  runBlock

/-- SUB carry limb phase 1 (4 instructions): LD, LD, SLTU, SUB.
    Loads a_limb and b_limb, computes borrow1 = (a < b ? 1 : 0), temp = a - b. -/
theorem sub_limb_carry_spec_phase1 (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 borrow_in v11 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow1 := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let temp := a_limb - b_limb
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x11 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SUB .x7 .x7 .x6))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

/-- SUB carry limb phase 2 (4 instructions): SLTU, SUB, OR, SD.
    Takes temp, borrow1, borrow_in, computes borrow2 = (temp < borrow_in ? 1 : 0),
    result = temp - borrow_in, borrow_out = borrow1 ||| borrow2. -/
theorem sub_limb_carry_spec_phase2 (off_b : BitVec 12)
    (sp temp b_limb borrow_in borrow1 a_limb : Word) (mem_a : Addr) (base : Addr)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_b := sp + signExtend12 off_b
    let borrow2 := if BitVec.ult temp borrow_in then (1 : Word) else 0
    let result := temp - borrow_in
    let borrow_out := borrow1 ||| borrow2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLTU .x6 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x5 .x11 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 off_b))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrow_out) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  runBlock

/-- SUB carry limb spec (8 instructions): LD, LD, SLTU, SUB, SLTU, SUB, OR, SD.
    Composed from phase1 and phase2. -/
theorem sub_limb_carry_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 borrow_in v11 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow1 := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let temp := a_limb - b_limb
    let borrow2 := if BitVec.ult temp borrow_in then (1 : Word) else 0
    let result := temp - borrow_in
    let borrow_out := borrow1 ||| borrow2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x11 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x6 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x5 .x11 .x6))
       (CodeReq.singleton (base + 28) (.SD .x12 .x7 off_b))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrow_out) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  have p1 := sub_limb_carry_spec_phase1 off_a off_b sp a_limb b_limb v7 v6 borrow_in v11 base
    hvalid_a hvalid_b
  have p2 := sub_limb_carry_spec_phase2 off_b sp (a_limb - b_limb) b_limb borrow_in
    (if BitVec.ult a_limb b_limb then (1 : Word) else 0)
    a_limb (sp + signExtend12 off_a) (base + 16) hvalid_b
  runBlock p1 p2

end EvmAsm.Rv64
