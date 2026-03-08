/-
  EvmAsm.Evm32.Not

  Full 256-bit EVM NOT spec composed from per-limb specs.
-/

import EvmAsm.Evm32.Bitwise
import EvmAsm.Rv32.Tactics.LiftSpec

namespace EvmAsm

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

-- ============================================================================
-- Full NOT spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM NOT: composes 8 per-limb NOT specs.
    24 instructions total. Unary: complements each limb in-place, sp unchanged. -/
theorem evm_not_spec (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (v7 : Word)
    (hvalid : ValidMemRange sp 8) :
    let c := signExtend12 (-1 : BitVec 12)
    let code :=
      -- Limb 0 code
      (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 8) ↦ᵢ .SW .x12 .x7 0) **
      -- Limb 1 code
      ((base + 12) ↦ᵢ .LW .x7 .x12 4) ** ((base + 16) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 20) ↦ᵢ .SW .x12 .x7 4) **
      -- Limb 2 code
      ((base + 24) ↦ᵢ .LW .x7 .x12 8) ** ((base + 28) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 32) ↦ᵢ .SW .x12 .x7 8) **
      -- Limb 3 code
      ((base + 36) ↦ᵢ .LW .x7 .x12 12) ** ((base + 40) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 44) ↦ᵢ .SW .x12 .x7 12) **
      -- Limb 4 code
      ((base + 48) ↦ᵢ .LW .x7 .x12 16) ** ((base + 52) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 56) ↦ᵢ .SW .x12 .x7 16) **
      -- Limb 5 code
      ((base + 60) ↦ᵢ .LW .x7 .x12 20) ** ((base + 64) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 68) ↦ᵢ .SW .x12 .x7 20) **
      -- Limb 6 code
      ((base + 72) ↦ᵢ .LW .x7 .x12 24) ** ((base + 76) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 80) ↦ᵢ .SW .x12 .x7 24) **
      -- Limb 7 code
      ((base + 84) ↦ᵢ .LW .x7 .x12 28) ** ((base + 88) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 92) ↦ᵢ .SW .x12 .x7 28)
    cpsTriple base (base + 96)
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
      (code **
       -- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a7 ^^^ c)) **
       (sp ↦ₘ (a0 ^^^ c)) ** ((sp + 4) ↦ₘ (a1 ^^^ c)) ** ((sp + 8) ↦ₘ (a2 ^^^ c)) ** ((sp + 12) ↦ₘ (a3 ^^^ c)) **
       ((sp + 16) ↦ₘ (a4 ^^^ c)) ** ((sp + 20) ↦ₘ (a5 ^^^ c)) ** ((sp + 24) ↦ₘ (a6 ^^^ c)) ** ((sp + 28) ↦ₘ (a7 ^^^ c))) := by
  have L0 := not_limb_spec 0 sp a0 v7 base (by validMem)
  have L1 := not_limb_spec 4 sp a1 (a0 ^^^ signExtend12 (-1 : BitVec 12)) (base + 12) (by validMem)
  have L2 := not_limb_spec 8 sp a2 (a1 ^^^ signExtend12 (-1 : BitVec 12)) (base + 24) (by validMem)
  have L3 := not_limb_spec 12 sp a3 (a2 ^^^ signExtend12 (-1 : BitVec 12)) (base + 36) (by validMem)
  have L4 := not_limb_spec 16 sp a4 (a3 ^^^ signExtend12 (-1 : BitVec 12)) (base + 48) (by validMem)
  have L5 := not_limb_spec 20 sp a5 (a4 ^^^ signExtend12 (-1 : BitVec 12)) (base + 60) (by validMem)
  have L6 := not_limb_spec 24 sp a6 (a5 ^^^ signExtend12 (-1 : BitVec 12)) (base + 72) (by validMem)
  have L7 := not_limb_spec 28 sp a7 (a6 ^^^ signExtend12 (-1 : BitVec 12)) (base + 84) (by validMem)
  runBlock L0 L1 L2 L3 L4 L5 L6 L7

-- ============================================================================
-- Stack-level NOT spec
-- ============================================================================

theorem signExtend12_neg1_eq_allOnes : signExtend12 (-1 : BitVec 12) = BitVec.allOnes 32 := by
  native_decide

set_option maxHeartbeats 6400000 in
/-- Stack-level 256-bit EVM NOT: complements an EvmWord in-place. -/
theorem evm_not_stack_spec (sp base : Addr)
    (a : EvmWord) (v7 : Word)
    (hvalid : ValidMemRange sp 8) :
    let c := signExtend12 (-1 : BitVec 12)
    let code :=
      -- Code
      (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 8) ↦ᵢ .SW .x12 .x7 0) **
      ((base + 12) ↦ᵢ .LW .x7 .x12 4) ** ((base + 16) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 20) ↦ᵢ .SW .x12 .x7 4) **
      ((base + 24) ↦ᵢ .LW .x7 .x12 8) ** ((base + 28) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 32) ↦ᵢ .SW .x12 .x7 8) **
      ((base + 36) ↦ᵢ .LW .x7 .x12 12) ** ((base + 40) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 44) ↦ᵢ .SW .x12 .x7 12) **
      ((base + 48) ↦ᵢ .LW .x7 .x12 16) ** ((base + 52) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 56) ↦ᵢ .SW .x12 .x7 16) **
      ((base + 60) ↦ᵢ .LW .x7 .x12 20) ** ((base + 64) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 68) ↦ᵢ .SW .x12 .x7 20) **
      ((base + 72) ↦ᵢ .LW .x7 .x12 24) ** ((base + 76) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 80) ↦ᵢ .SW .x12 .x7 24) **
      ((base + 84) ↦ᵢ .LW .x7 .x12 28) ** ((base + 88) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 92) ↦ᵢ .SW .x12 .x7 28)
    cpsTriple base (base + 96)
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** evmWordIs sp a)
      (code **
       -- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a.getLimb 7 ^^^ c)) ** evmWordIs sp (~~~a)) := by
  -- Helper: (~~~a).getLimb i = a.getLimb i ^^^ signExtend12 (-1)
  have not_limb_eq : ∀ i : Fin 8,
      (~~~a).getLimb i = a.getLimb i ^^^ signExtend12 (-1 : BitVec 12) := by
    intro i
    rw [EvmWord.getLimb_not, BitVec.not_def, BitVec.xor_comm, ← signExtend12_neg1_eq_allOnes]
  -- Apply evm_not_spec with individual limbs
  have h_main := evm_not_spec sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (a.getLimb 4) (a.getLimb 5) (a.getLimb 6) (a.getLimb 7)
    v7 hvalid
  liftSpec h_main post_simp [not_limb_eq]

end EvmAsm
