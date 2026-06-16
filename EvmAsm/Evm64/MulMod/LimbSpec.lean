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

end EvmAsm.Evm64
