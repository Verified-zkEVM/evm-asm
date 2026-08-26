/-
  EvmAsm.Evm64.DivMod.Spec.DivisorLimbCaseHelpers

  Small convenience helpers around `DivisorLimbCase` for use by the final
  top-level public DIV wrapper assembly.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.UnifiedDivisorCases

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- For a nonzero divisor, the divisor limbs satisfy exactly one of the four
    shape disjuncts (n1, n2, n3, n4). Stated as a four-way disjunction over
    the shape predicates so callers can pattern-match without going through
    the inductive `DivisorLimbCase`. -/
theorem nonzero_divisor_limb_shape (b : EvmWord) (hbnz : b ≠ 0) :
    (b.getLimbN 3 = 0 ∧ b.getLimbN 2 = 0 ∧ b.getLimbN 1 = 0 ∧ b.getLimbN 0 ≠ 0) ∨
    (b.getLimbN 3 = 0 ∧ b.getLimbN 2 = 0 ∧ b.getLimbN 1 ≠ 0) ∨
    (b.getLimbN 3 = 0 ∧ b.getLimbN 2 ≠ 0) ∨
    (b.getLimbN 3 ≠ 0) := by
  have hbnzOr : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  by_cases hb3z : b.getLimbN 3 = 0
  · by_cases hb2z : b.getLimbN 2 = 0
    · by_cases hb1z : b.getLimbN 1 = 0
      · left
        refine ⟨hb3z, hb2z, hb1z, ?_⟩
        intro hb0z
        apply hbnzOr
        simp [hb0z, hb1z, hb2z, hb3z]
      · right; left
        exact ⟨hb3z, hb2z, hb1z⟩
    · right; right; left
      exact ⟨hb3z, hb2z⟩
  · right; right; right
    exact hb3z

end EvmAsm.Evm64
