/-
  EvmAsm.Evm64.EvmWordArith.IsZero

  ISZERO correctness: OR-reduction of limbs detects zero.
-/

import EvmAsm.Evm64.EvmWordArith.Common

namespace EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- ISZERO correctness
-- ============================================================================

theorem iszero_or_reduce_correct (a : EvmWord) :
    (if BitVec.ult (a.getLimb 0 ||| a.getLimb 1 ||| a.getLimb 2 ||| a.getLimb 3) 1
     then (1 : Word) else 0) =
    (if a = 0 then (1 : Word) else 0) := by
  suffices h : BitVec.ult (a.getLimb 0 ||| a.getLimb 1 ||| a.getLimb 2 ||| a.getLimb 3) 1 ↔ a = 0 by
    by_cases ha : a = 0 <;> simp_all
  constructor
  · intro h
    have hor := ult_one_eq_zero.mp h
    have h12 := bv_or_eq_zero (show (a.getLimb 0 ||| a.getLimb 1) ||| (a.getLimb 2 ||| a.getLimb 3) = 0 by
      rw [BitVec.or_assoc] at hor; exact hor)
    exact (eq_zero_iff_limbs a).mpr
      ⟨(bv_or_eq_zero h12.1).1, (bv_or_eq_zero h12.1).2,
       (bv_or_eq_zero h12.2).1, (bv_or_eq_zero h12.2).2⟩
  · intro h; subst h; exact ult_one_eq_zero.mpr rfl

end EvmWord

end EvmAsm.Rv64
