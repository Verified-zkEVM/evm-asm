/-
  EvmAsm.Evm64.DivMod.Spec.N1V5Shift0LaneRest

  The remaining (digits j=2,1,0) loop conditions for the v5 n=1 **shift=0** lane,
  chaining the generic single-limb cores through `fullN1S2`/`fullN1S1`.  At shift=0
  the loop runs at `v=(b0,0,0,0)`, `u0=a3`, `u1=u2=u3=uTop=0`, `u0_orig_2=a2`,
  `u0_orig_1=a1`, `u0_orig_0=a0`.  Each digit's remainder is single-limb
  (`val256 < b0 < 2^64` ⇒ high limbs zero), so the next digit's input matches the
  core's `(v0,0,0,0)/(u0,u1,0,0,0)` shape and the cores re-apply.  Shift=0
  counterparts of `n1v5_lane_bltu_1/0_of_shape` and
  `n1v5_lane_hborrow_2/1/0_of_shape`.  Together with `N1V5Shift0LaneFirstDigit`
  this discharges all eight hypotheses of
  `divK_loop_n1_call_unified_v5_spec_within_noNop` at the shift=0 inputs.  Bead
  `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0LaneFirstDigit
import EvmAsm.Evm64.DivMod.LoopIterN1.N1V5IterChainShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64

private theorem b0_norm {b0 : Word} (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    b0.toNat ≥ 2 ^ 63 := b0_ge_pow63_of_clz_zero b0 hb0nz hclz

private theorem b0_pos {b0 : Word} (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    (0 : Word).toNat < b0.toNat := by
  have := b0_ge_pow63_of_clz_zero b0 hb0nz hclz
  have hz : (0 : Word).toNat = 0 := by decide
  omega

/-- Digit-3 (top) remainder `val256` bound for the shift=0 inputs. -/
private theorem s3_rem_lt (a3 b0 : Word) (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    EvmWord.val256
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.1
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.1
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.2.1
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.2.2.1 < b0.toNat := by
  rw [← iterN1V5_true]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call b0 a3 0 (b0_norm hb0nz hclz) (b0_pos hb0nz hclz)

/-- Digit-2 remainder `val256` bound for the shift=0 inputs (`fullN1S2`). -/
private theorem s2_rem_lt (a2 a3 b0 : Word) (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    EvmWord.val256
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.1
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.1
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.2.1
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.2.2.1 < b0.toNat := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ _
    (s3_rem_lt a3 b0 hb0nz hclz)
  unfold fullN1S2
  simp only [hz1, hz2, hz3]
  rw [← iterN1V5_true]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call b0 a2 _ (b0_norm hb0nz hclz)
    (n1v5_limb0_toNat_lt_of_val256_lt (s3_rem_lt a3 b0 hb0nz hclz))

/-- Digit-1 remainder `val256` bound for the shift=0 inputs (`fullN1S1`). -/
private theorem s1_rem_lt (a1 a2 a3 b0 : Word) (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    EvmWord.val256
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.1
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.1
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.2.1 < b0.toNat := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ _
    (s2_rem_lt a2 a3 b0 hb0nz hclz)
  unfold fullN1S1
  simp only [hz1, hz2, hz3]
  rw [← iterN1V5_true]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call b0 a1 _ (b0_norm hb0nz hclz)
    (n1v5_limb0_toNat_lt_of_val256_lt (s2_rem_lt a2 a3 b0 hb0nz hclz))

/-- n=1 shift=0 lane, `j=1` `bltu`. -/
theorem n1v5_shift0_lane_bltu_1 (a2 a3 b0 : Word) (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    BitVec.ult (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.1 b0 :=
  n1v5_bltu_limb0_of_val256_lt (s2_rem_lt a2 a3 b0 hb0nz hclz)

/-- n=1 shift=0 lane, `j=0` `bltu`. -/
theorem n1v5_shift0_lane_bltu_0 (a1 a2 a3 b0 : Word) (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    BitVec.ult (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1 b0 :=
  n1v5_bltu_limb0_of_val256_lt (s1_rem_lt a1 a2 a3 b0 hb0nz hclz)

/-- n=1 shift=0 lane, `j=2` no-borrow. -/
theorem n1v5_shift0_lane_hborrow_2 (a2 a3 b0 : Word) (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    mulsubN4NoBorrow
      (divKTrialCallV5QHat (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.1 a2 b0)
      b0 0 0 0 a2
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.1
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.1
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.2.1
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.2.2.1 := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ _
    (s3_rem_lt a3 b0 hb0nz hclz)
  rw [hz1, hz2, hz3, divKTrialCallV5QHat_eq_div128Quot_v5]
  exact mulsubN4NoBorrow_div128Quot_v5_of_norm_call b0 a2 _ 0 (b0_norm hb0nz hclz)
    (n1v5_limb0_toNat_lt_of_val256_lt (s3_rem_lt a3 b0 hb0nz hclz))

/-- n=1 shift=0 lane, `j=1` no-borrow. -/
theorem n1v5_shift0_lane_hborrow_1 (a1 a2 a3 b0 : Word) (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    mulsubN4NoBorrow
      (divKTrialCallV5QHat (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.1 a1 b0)
      b0 0 0 0 a1
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.1
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.1
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.2.1
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.2.2.1 := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ _
    (s2_rem_lt a2 a3 b0 hb0nz hclz)
  rw [hz1, hz2, hz3, divKTrialCallV5QHat_eq_div128Quot_v5]
  exact mulsubN4NoBorrow_div128Quot_v5_of_norm_call b0 a1 _ 0 (b0_norm hb0nz hclz)
    (n1v5_limb0_toNat_lt_of_val256_lt (s2_rem_lt a2 a3 b0 hb0nz hclz))

/-- n=1 shift=0 lane, `j=0` no-borrow. -/
theorem n1v5_shift0_lane_hborrow_0 (a0 a1 a2 a3 b0 : Word) (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    mulsubN4NoBorrow
      (divKTrialCallV5QHat (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1 a0 b0)
      b0 0 0 0 a0
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.1
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.1
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.2.1 := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ _
    (s1_rem_lt a1 a2 a3 b0 hb0nz hclz)
  rw [hz1, hz2, hz3, divKTrialCallV5QHat_eq_div128Quot_v5]
  exact mulsubN4NoBorrow_div128Quot_v5_of_norm_call b0 a0 _ 0 (b0_norm hb0nz hclz)
    (n1v5_limb0_toNat_lt_of_val256_lt (s1_rem_lt a1 a2 a3 b0 hb0nz hclz))

end EvmAsm.Evm64
