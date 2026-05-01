/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1RemainderV4

  v4 first-step extended-remainder bounds for the n=1 full path.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1ConservationV4

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem fullDivN1R3_v4_extended_remainder_lt
    (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hbltu_3 : isTrialN1_v4_j3 bltu_3 a3 b0) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepRemainderVal r3 + n1StepTopVal r3 * 2^256 <
      EvmWord.val256 v.1 v.2.1 v.2.2.1 0 := by
  intro v r3
  subst v
  subst r3
  have hv0_ge : ((fullDivN1NormV b0 b1 b2 b3).1).toNat ≥ 2^63 :=
    fullDivN1NormV_v0_ge_pow63_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hv1z := fullDivN1NormV_v1_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hshift_nz
  have hv2z := fullDivN1NormV_v2_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hcon := fullDivN1R3_v4_step_conservation
    bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2
  have hqeq := fullDivN1R3_v4_qout_eq_local_digit
    bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hshift_nz hbltu_3
  have h_shift_pos : 1 ≤ (fullDivN1Shift b0).toNat := by
    rcases Nat.eq_zero_or_pos (fullDivN1Shift b0).toNat with h | h
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq h
    · exact h
  have h_shift_le : (fullDivN1Shift b0).toNat ≤ 63 := by
    rw [fullDivN1Shift_unfold]
    exact clzResult_fst_toNat_le b0
  have hu4_lt_pow63 : ((fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2).toNat < 2^63 := by
    rw [fullDivN1NormU_unfold]
    simp only []
    rw [fullDivN1AntiShift_unfold]
    exact u_top_lt_pow63_of_shift_nz a3 (fullDivN1Shift b0) h_shift_pos h_shift_le
  have hu4_lt_v0 : ((fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2).toNat <
      ((fullDivN1NormV b0 b1 b2 b3).1).toNat :=
    lt_of_lt_of_le hu4_lt_pow63 hv0_ge
  have hlocal : n1LocalFloorDigit (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 =
      (((fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2).toNat * 2^64 +
        ((fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1).toNat) /
        ((fullDivN1NormV b0 b1 b2 b3).1).toNat := by
    delta n1LocalFloorDigit
    rw [show BitVec.ult (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        (fullDivN1NormV b0 b1 b2 b3).1 = true from (EvmWord.ult_iff).mpr hu4_lt_v0]
    simp only [if_true]
  have hge :
      (EvmWord.val256 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 + 0 * 2^256) /
        EvmWord.val256 (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 ≤
        (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
    rw [hqeq]
    rw [hlocal]
    unfold EvmWord.val256
    simp [hv1z, hv2z, Nat.add_comm]
  exact n1StepExtendedRemainder_lt_of_floor_le
    (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    hvnz hcon hge

end EvmAsm.Evm64
