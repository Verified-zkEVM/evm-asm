/-
  EvmAsm.Evm64.MulMod.LimbSpec

  Per-block / per-limb cpsTriple specs for MULMOD sub-blocks (operand
  widening, callable-divide JAL, result narrowing).

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0). Per
  `OPCODE_TEMPLATE.md`, each sub-block will get exactly one cpsTriple
  lemma once the Compose layer pins the layout.
-/

import EvmAsm.Evm64.MulMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- evm_mulmod_product_zero
-- ============================================================================

abbrev evm_mulmod_product_zero_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod_product_zero

/-- Folded postcondition for `evm_mulmod_product_zero`.

    The block preserves the three input stack words `[a, b, N]` at `sp+0..88`
    and clears the eight-limb product window at `sp+96..152`. -/
@[irreducible]
def evmMulModProductZeroPost (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
  ((sp + 56) ↦ₘ b3) **
  ((sp + 64) ↦ₘ n0) ** ((sp + 72) ↦ₘ n1) ** ((sp + 80) ↦ₘ n2) **
  ((sp + 88) ↦ₘ n3) **
  ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ (0 : Word))

theorem evmMulModProductZeroPost_unfold (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 : Word) :
    evmMulModProductZeroPost sp a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 =
      ((.x12 ↦ᵣ sp) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
       ((sp + 56) ↦ₘ b3) **
       ((sp + 64) ↦ₘ n0) ** ((sp + 72) ↦ₘ n1) ** ((sp + 80) ↦ₘ n2) **
       ((sp + 88) ↦ₘ n3) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ (0 : Word))) := by
  delta evmMulModProductZeroPost; rfl

/-- Zero the eight-limb MULMOD product window while preserving the input stack
    cells. -/
theorem evm_mulmod_product_zero_spec_within (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 8 base (base + 32) (evm_mulmod_product_zero_code base)
      ((.x12 ↦ᵣ sp) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
       ((sp + 56) ↦ₘ b3) **
       ((sp + 64) ↦ₘ n0) ** ((sp + 72) ↦ₘ n1) ** ((sp + 80) ↦ₘ n2) **
       ((sp + 88) ↦ₘ n3) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ p0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ p1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ p2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ p7))
      (evmMulModProductZeroPost sp a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3) := by
  simp only [evmMulModProductZeroPost_unfold]
  have I0 := sd_x0_spec_gen_within .x12 sp p0 96 base
  have I1 := sd_x0_spec_gen_within .x12 sp p1 104 (base + 4)
  have I2 := sd_x0_spec_gen_within .x12 sp p2 112 (base + 8)
  have I3 := sd_x0_spec_gen_within .x12 sp p3 120 (base + 12)
  have I4 := sd_x0_spec_gen_within .x12 sp p4 128 (base + 16)
  have I5 := sd_x0_spec_gen_within .x12 sp p5 136 (base + 20)
  have I6 := sd_x0_spec_gen_within .x12 sp p6 144 (base + 24)
  have I7 := sd_x0_spec_gen_within .x12 sp p7 152 (base + 28)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7

-- ============================================================================
-- evm_mulmod_product_propagate_carry
-- ============================================================================

abbrev evm_mulmod_product_propagate_carry_code (base : Word) (offsets : List (BitVec 12)) :
    CodeReq :=
  CodeReq.ofProg base (evm_mulmod_product_propagate_carry offsets)

/-- One product-window carry propagation step: add incoming carry to a limb,
    store the updated limb, and leave the overflow carry in `x10`. -/
def mulModCarryStepValue (limb carry : Word) : Word :=
  limb + carry

/-- Carry-out from `mulModCarryStepValue`. -/
def mulModCarryStepCarry (limb carry : Word) : Word :=
  if BitVec.ult (limb + carry) carry then (1 : Word) else 0

/-- Empty carry propagation is a no-op. -/
theorem evm_mulmod_product_propagate_carry_nil_spec_within (base sp carry v9 : Word) :
    cpsTripleWithin 0 base base (evm_mulmod_product_propagate_carry_code base [])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9)) := by
  show cpsTripleWithin 0 base base CodeReq.empty
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9))
  exact cpsTripleWithin_refl (fun _ hp => hp)

/-- Single-limb carry propagation. This is the reusable step used to build the
    concrete carry-offset list specs for `evm_mulmod_product_add_partial`. -/
theorem evm_mulmod_product_propagate_carry_one_spec_within (sp base : Word)
    (off : BitVec 12) (carry limb v9 : Word) :
    cpsTripleWithin 4 base (base + 16)
      (evm_mulmod_product_propagate_carry_code base [off])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 off) ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry limb carry) **
       (.x9 ↦ᵣ mulModCarryStepValue limb carry) **
       ((sp + signExtend12 off) ↦ₘ mulModCarryStepValue limb carry)) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 limb off base (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 limb carry (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (limb + carry) carry (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (limb + carry) limb off (base + 12)
  runBlock I0 I1 I2 I3

-- ============================================================================
-- Concrete carry-propagation suffixes used by evm_mulmod_product_layout
-- ============================================================================

/-- Concrete carry propagation over product offsets 144, 152. -/
theorem evm_mulmod_product_propagate_carry_144_152_spec_within
    (sp base carry v9 p6 p7 : Word) :
    cpsTripleWithin 8 base (base + 32)
      (evm_mulmod_product_propagate_carry_code base [144, 152])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (carry))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (carry))) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 (carry)) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (carry)))) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 p6 144 (base + 0) (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p6 (carry) (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p6 + (carry)) (carry) (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (p6 + (carry)) p6 144 (base + 12)
  have I4 := ld_spec_gen_within .x9 .x12 sp (p6 + (carry)) p7 152 (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p7 (if BitVec.ult (p6 + (carry)) (carry) then 1 else 0) (base + 20) (by nofun)
  have I6 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p7 + (if BitVec.ult (p6 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p6 + (carry)) (carry) then 1 else 0) (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x9 sp (p7 + (if BitVec.ult (p6 + (carry)) (carry) then 1 else 0)) p7 152 (base + 28)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7

/-- Concrete carry propagation over product offsets 136, 144, 152. -/
theorem evm_mulmod_product_propagate_carry_136_144_152_spec_within
    (sp base carry v9 p5 p6 p7 : Word) :
    cpsTripleWithin 12 base (base + 48)
      (evm_mulmod_product_propagate_carry_code base [136, 144, 152])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (carry)))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (carry)))) **
       ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 (carry)) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 (mulModCarryStepCarry p5 (carry))) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (carry))))) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 p5 136 (base + 0) (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p5 (carry) (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p5 + (carry)) (carry) (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (p5 + (carry)) p5 136 (base + 12)
  have I4 := ld_spec_gen_within .x9 .x12 sp (p5 + (carry)) p6 144 (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p6 (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) (base + 20) (by nofun)
  have I6 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x9 sp (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) p6 144 (base + 28)
  have I8 := ld_spec_gen_within .x9 .x12 sp (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) p7 152 (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p7 (if BitVec.ult (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 36) (by nofun)
  have I10 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 40) (by nofun)
  have I11 := sd_spec_gen_within .x12 .x9 sp (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) then 1 else 0)) p7 152 (base + 44)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11

/-- Concrete carry propagation over product offsets 128, 136, 144, 152. -/
theorem evm_mulmod_product_propagate_carry_128_136_144_152_spec_within
    (sp base carry v9 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 16 base (base + 64)
      (evm_mulmod_product_propagate_carry_code base [128, 136, 144, 152])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (carry))))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (carry))))) **
       ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ mulModCarryStepValue p4 (carry)) **
       ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 (mulModCarryStepCarry p4 (carry))) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (carry)))) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (carry)))))) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 p4 128 (base + 0) (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p4 (carry) (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p4 + (carry)) (carry) (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (p4 + (carry)) p4 128 (base + 12)
  have I4 := ld_spec_gen_within .x9 .x12 sp (p4 + (carry)) p5 136 (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p5 (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) (base + 20) (by nofun)
  have I6 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x9 sp (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) p5 136 (base + 28)
  have I8 := ld_spec_gen_within .x9 .x12 sp (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) p6 144 (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p6 (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 36) (by nofun)
  have I10 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 40) (by nofun)
  have I11 := sd_spec_gen_within .x12 .x9 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) p6 144 (base + 44)
  have I12 := ld_spec_gen_within .x9 .x12 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) p7 152 (base + 48) (by nofun)
  have I13 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p7 (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 52) (by nofun)
  have I14 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 56) (by nofun)
  have I15 := sd_spec_gen_within .x12 .x9 sp (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) p7 152 (base + 60)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15

/-- Concrete carry propagation over product offsets 120, 128, 136, 144, 152. -/
theorem evm_mulmod_product_propagate_carry_120_128_136_144_152_spec_within
    (sp base carry v9 p3 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 20 base (base + 80)
      (evm_mulmod_product_propagate_carry_code base [120, 128, 136, 144, 152])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (carry)))))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (carry)))))) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ mulModCarryStepValue p3 (carry)) **
       ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ mulModCarryStepValue p4 (mulModCarryStepCarry p3 (carry))) **
       ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (carry)))) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (carry))))) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (carry))))))) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 p3 120 (base + 0) (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p3 (carry) (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p3 + (carry)) (carry) (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (p3 + (carry)) p3 120 (base + 12)
  have I4 := ld_spec_gen_within .x9 .x12 sp (p3 + (carry)) p4 128 (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p4 (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) (base + 20) (by nofun)
  have I6 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x9 sp (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) p4 128 (base + 28)
  have I8 := ld_spec_gen_within .x9 .x12 sp (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) p5 136 (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p5 (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 36) (by nofun)
  have I10 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 40) (by nofun)
  have I11 := sd_spec_gen_within .x12 .x9 sp (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) p5 136 (base + 44)
  have I12 := ld_spec_gen_within .x9 .x12 sp (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) p6 144 (base + 48) (by nofun)
  have I13 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p6 (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 52) (by nofun)
  have I14 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 56) (by nofun)
  have I15 := sd_spec_gen_within .x12 .x9 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) p6 144 (base + 60)
  have I16 := ld_spec_gen_within .x9 .x12 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) p7 152 (base + 64) (by nofun)
  have I17 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p7 (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 68) (by nofun)
  have I18 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 72) (by nofun)
  have I19 := sd_spec_gen_within .x12 .x9 sp (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) p7 152 (base + 76)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19

/-- Concrete carry propagation over product offsets 112, 120, 128, 136, 144, 152. -/
theorem evm_mulmod_product_propagate_carry_112_120_128_136_144_152_spec_within
    (sp base carry v9 p2 p3 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 24 base (base + 96)
      (evm_mulmod_product_propagate_carry_code base [112, 120, 128, 136, 144, 152])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ p2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry))))))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry))))))) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ mulModCarryStepValue p2 (carry)) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ mulModCarryStepValue p3 (mulModCarryStepCarry p2 (carry))) **
       ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ mulModCarryStepValue p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry)))) **
       ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry))))) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry)))))) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry)))))))) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 p2 112 (base + 0) (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p2 (carry) (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p2 + (carry)) (carry) (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (p2 + (carry)) p2 112 (base + 12)
  have I4 := ld_spec_gen_within .x9 .x12 sp (p2 + (carry)) p3 120 (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p3 (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) (base + 20) (by nofun)
  have I6 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x9 sp (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) p3 120 (base + 28)
  have I8 := ld_spec_gen_within .x9 .x12 sp (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) p4 128 (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p4 (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 36) (by nofun)
  have I10 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 40) (by nofun)
  have I11 := sd_spec_gen_within .x12 .x9 sp (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) p4 128 (base + 44)
  have I12 := ld_spec_gen_within .x9 .x12 sp (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) p5 136 (base + 48) (by nofun)
  have I13 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p5 (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 52) (by nofun)
  have I14 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 56) (by nofun)
  have I15 := sd_spec_gen_within .x12 .x9 sp (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) p5 136 (base + 60)
  have I16 := ld_spec_gen_within .x9 .x12 sp (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) p6 144 (base + 64) (by nofun)
  have I17 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p6 (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 68) (by nofun)
  have I18 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 72) (by nofun)
  have I19 := sd_spec_gen_within .x12 .x9 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) p6 144 (base + 76)
  have I20 := ld_spec_gen_within .x9 .x12 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) p7 152 (base + 80) (by nofun)
  have I21 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p7 (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 84) (by nofun)
  have I22 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 88) (by nofun)
  have I23 := sd_spec_gen_within .x12 .x9 sp (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) p7 152 (base + 92)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20 I21 I22 I23

end EvmAsm.Evm64
