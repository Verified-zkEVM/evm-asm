/-
  EvmAsm.Evm64.EvmWordArith.Eq

  EQ correctness: XOR-OR accumulation tests equality.
-/

import EvmAsm.Evm64.EvmWordArith.Common

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- EQ correctness
-- ============================================================================

theorem eq_xor_or_reduce_correct (a b : EvmWord) :
    let acc0 := a.getLimb 0 ^^^ b.getLimb 0
    let acc1 := acc0 ||| (a.getLimb 1 ^^^ b.getLimb 1)
    let acc2 := acc1 ||| (a.getLimb 2 ^^^ b.getLimb 2)
    let acc3 := acc2 ||| (a.getLimb 3 ^^^ b.getLimb 3)
    (if BitVec.ult acc3 1 then (1 : Word) else 0) =
    (if a = b then (1 : Word) else 0) := by
  intro acc0 acc1 acc2 acc3
  suffices h : BitVec.ult acc3 1 ↔ a = b by
    by_cases hab : a = b <;> simp_all
  constructor
  · intro h
    have hacc : acc3 = 0 := ult_one_eq_zero.mp h
    have hacc_flat : (a.getLimb 0 ^^^ b.getLimb 0) ||| (a.getLimb 1 ^^^ b.getLimb 1) |||
                     (a.getLimb 2 ^^^ b.getLimb 2) ||| (a.getLimb 3 ^^^ b.getLimb 3) = 0 := by
      show acc3 = 0; exact hacc
    have h12 := bv_or_eq_zero (show ((a.getLimb 0 ^^^ b.getLimb 0) ||| (a.getLimb 1 ^^^ b.getLimb 1)) |||
        ((a.getLimb 2 ^^^ b.getLimb 2) ||| (a.getLimb 3 ^^^ b.getLimb 3)) = 0 by
      rw [BitVec.or_assoc] at hacc_flat; exact hacc_flat)
    calc a = fromLimbs a.getLimb := (fromLimbs_getLimb a).symm
      _ = fromLimbs b.getLimb := by unfold fromLimbs; simp only [
            xor_eq_zero_imp (bv_or_eq_zero h12.1).1, xor_eq_zero_imp (bv_or_eq_zero h12.1).2,
            xor_eq_zero_imp (bv_or_eq_zero h12.2).1, xor_eq_zero_imp (bv_or_eq_zero h12.2).2]
      _ = b := fromLimbs_getLimb b
  · intro h; subst h
    show BitVec.ult ((((a.getLimb 0 ^^^ a.getLimb 0) |||
      (a.getLimb 1 ^^^ a.getLimb 1)) |||
      (a.getLimb 2 ^^^ a.getLimb 2)) |||
      (a.getLimb 3 ^^^ a.getLimb 3)) 1
    simp [BitVec.xor_self, BitVec.ult]

end EvmWord

end EvmAsm.Evm64
