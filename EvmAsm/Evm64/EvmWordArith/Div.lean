/-
  EvmAsm.Evm64.EvmWordArith.Div

  EVM DIV/MOD semantics: word-level definitions and getLimb lemmas for zero case.
  Bridge lemmas connecting the RISC-V limb-level computation to EvmWord.div/mod.
-/

import EvmAsm.Evm64.EvmWordArith.Common

namespace EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- EVM DIV/MOD semantics
-- ============================================================================

/-- EVM DIV semantics: unsigned integer division, returning 0 when divisor is 0. -/
def div (a b : EvmWord) : EvmWord :=
  if b = 0 then 0 else BitVec.udiv a b

/-- EVM MOD semantics: unsigned modulus, returning 0 when divisor is 0. -/
def mod (a b : EvmWord) : EvmWord :=
  if b = 0 then 0 else BitVec.umod a b

-- ============================================================================
-- Zero divisor lemmas
-- ============================================================================

theorem div_zero_right (a : EvmWord) : div a 0 = 0 := by
  simp [div]

theorem mod_zero_right (a : EvmWord) : mod a 0 = 0 := by
  simp [mod]

private theorem getLimb_zero (i : Fin 4) : (0 : EvmWord).getLimb i = 0 := by
  simp [getLimb]

theorem div_getLimb_zero_right (a : EvmWord) (i : Fin 4) :
    (div a 0).getLimb i = 0 := by
  rw [div_zero_right]; exact getLimb_zero i

theorem mod_getLimb_zero_right (a : EvmWord) (i : Fin 4) :
    (mod a 0).getLimb i = 0 := by
  rw [mod_zero_right]; exact getLimb_zero i

-- ============================================================================
-- b = 0 ↔ all limbs OR to zero (bridge for program specs)
-- ============================================================================

/-- b0 ||| b1 ||| b2 ||| b3 = 0 implies all individual limbs are zero. -/
theorem limbs_or_eq_zero_imp (b0 b1 b2 b3 : Word) (h : b0 ||| b1 ||| b2 ||| b3 = 0) :
    b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 := by
  -- h : ((b0 ||| b1) ||| b2) ||| b3 = 0 (left-associated)
  have ⟨h012, h3⟩ := bv_or_eq_zero h
  have ⟨h01, h2⟩ := bv_or_eq_zero h012
  have ⟨h0, h1⟩ := bv_or_eq_zero h01
  exact ⟨h0, h1, h2, h3⟩

/-- A 256-bit word is zero iff the OR of all its limbs is zero. -/
theorem eq_zero_iff_limbs_or (b : EvmWord) :
    b = 0 ↔ b.getLimb 0 ||| b.getLimb 1 ||| b.getLimb 2 ||| b.getLimb 3 = 0 := by
  constructor
  · intro h; subst h
    show (0 : EvmWord).getLimb 0 ||| (0 : EvmWord).getLimb 1 |||
         (0 : EvmWord).getLimb 2 ||| (0 : EvmWord).getLimb 3 = 0
    native_decide
  · intro h
    set b0 := b.getLimb 0 with hb0_def
    set b1 := b.getLimb 1 with hb1_def
    set b2 := b.getLimb 2 with hb2_def
    set b3 := b.getLimb 3 with hb3_def
    have ⟨h0, h1, h2, h3⟩ := limbs_or_eq_zero_imp b0 b1 b2 b3 h
    exact (eq_zero_iff_limbs b).mpr ⟨hb0_def ▸ h0, hb1_def ▸ h1, hb2_def ▸ h2, hb3_def ▸ h3⟩

end EvmWord

end EvmAsm.Rv64
