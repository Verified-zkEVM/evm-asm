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

theorem fullDivN1R2_v4_extended_remainder_lt
    (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hbltu_3 : isTrialN1_v4_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_v4_j2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepRemainderVal r2 + n1StepTopVal r2 * 2^256 <
      EvmWord.val256 v.1 v.2.1 v.2.2.1 0 := by
  intro v r2
  subst v
  subst r2
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  have hv1z := fullDivN1NormV_v1_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hshift_nz
  have hv2z := fullDivN1NormV_v2_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hprev := fullDivN1R3_v4_extended_remainder_lt
    bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hshift_nz hcarry2 hbltu_3
  have hprev' : n1StepRemainderVal r3 + n1StepTopVal r3 * 2^256 <
      ((fullDivN1NormV b0 b1 b2 b3).1).toNat := by
    subst r3
    simpa [hv1z, hv2z, EvmWord.val256] using hprev
  have htop_lt_v0 : r3.2.1.toNat < ((fullDivN1NormV b0 b1 b2 b3).1).toNat := by
    delta n1StepRemainderVal n1StepTopVal at hprev'
    unfold EvmWord.val256 at hprev'
    omega
  have hcon := fullDivN1R2_v4_step_conservation
    bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2
  have hqeq := fullDivN1R2_v4_qout_eq_local_digit
    bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hshift_nz hbltu_2
  have hlocal : n1LocalFloorDigit (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 r3.2.1 =
      (r3.2.1.toNat * 2^64 + (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1.toNat) /
        ((fullDivN1NormV b0 b1 b2 b3).1).toNat := by
    delta n1LocalFloorDigit
    rw [show BitVec.ult r3.2.1 (fullDivN1NormV b0 b1 b2 b3).1 = true from
      (EvmWord.ult_iff).mpr htop_lt_v0]
    simp only [if_true]
  have hnum_eq :
      EvmWord.val256 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          r3.2.1 r3.2.2.1 r3.2.2.2.1 + r3.2.2.2.2.1.toNat * 2^256 =
        r3.2.1.toNat * 2^64 + (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1.toNat := by
    delta n1StepRemainderVal n1StepTopVal at hprev'
    unfold EvmWord.val256 at hprev' ⊢
    omega
  have hge :
      (EvmWord.val256 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          r3.2.1 r3.2.2.1 r3.2.2.2.1 + r3.2.2.2.2.1.toNat * 2^256) /
        EvmWord.val256 (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 ≤
        (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
    rw [hqeq]
    rw [hlocal]
    rw [hnum_eq]
    unfold EvmWord.val256
    simp [hv1z, hv2z]
  exact n1StepExtendedRemainder_lt_of_floor_le
    (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    hvnz hcon hge

theorem fullDivN1R1_v4_extended_remainder_lt
    (bltu_3 bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hbltu_3 : isTrialN1_v4_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_v4_j2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_v4_j1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepRemainderVal r1 + n1StepTopVal r1 * 2^256 <
      EvmWord.val256 v.1 v.2.1 v.2.2.1 0 := by
  intro v r1
  subst v
  subst r1
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  have hv1z := fullDivN1NormV_v1_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hshift_nz
  have hv2z := fullDivN1NormV_v2_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hprev := fullDivN1R2_v4_extended_remainder_lt
    bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hshift_nz
    hcarry2 hbltu_3 hbltu_2
  have hprev' : n1StepRemainderVal r2 + n1StepTopVal r2 * 2^256 <
      ((fullDivN1NormV b0 b1 b2 b3).1).toNat := by
    subst r2
    simpa [hv1z, hv2z, EvmWord.val256] using hprev
  have htop_lt_v0 : r2.2.1.toNat < ((fullDivN1NormV b0 b1 b2 b3).1).toNat := by
    delta n1StepRemainderVal n1StepTopVal at hprev'
    unfold EvmWord.val256 at hprev'
    omega
  have hcon := fullDivN1R1_v4_step_conservation
    bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2
  have hqeq := fullDivN1R1_v4_qout_eq_local_digit
    bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hshift_nz
    hbltu_1
  have hlocal : n1LocalFloorDigit (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1 r2.2.1 =
      (r2.2.1.toNat * 2^64 + (fullDivN1NormU a0 a1 a2 a3 b0).2.1.toNat) /
        ((fullDivN1NormV b0 b1 b2 b3).1).toNat := by
    delta n1LocalFloorDigit
    rw [show BitVec.ult r2.2.1 (fullDivN1NormV b0 b1 b2 b3).1 = true from
      (EvmWord.ult_iff).mpr htop_lt_v0]
    simp only [if_true]
  have hnum_eq :
      EvmWord.val256 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
          r2.2.1 r2.2.2.1 r2.2.2.2.1 + r2.2.2.2.2.1.toNat * 2^256 =
        r2.2.1.toNat * 2^64 + (fullDivN1NormU a0 a1 a2 a3 b0).2.1.toNat := by
    delta n1StepRemainderVal n1StepTopVal at hprev'
    unfold EvmWord.val256 at hprev' ⊢
    omega
  have hge :
      (EvmWord.val256 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
          r2.2.1 r2.2.2.1 r2.2.2.2.1 + r2.2.2.2.2.1.toNat * 2^256) /
        EvmWord.val256 (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 ≤
        (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
    rw [hqeq]
    rw [hlocal]
    rw [hnum_eq]
    unfold EvmWord.val256
    simp [hv1z, hv2z]
  exact n1StepExtendedRemainder_lt_of_floor_le
    (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    hvnz hcon hge

theorem fullDivN1R0_v4_extended_remainder_lt
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hbltu_3 : isTrialN1_v4_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_v4_j2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_v4_j1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_v4_j0 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let r0 := fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepRemainderVal r0 + n1StepTopVal r0 * 2^256 <
      EvmWord.val256 v.1 v.2.1 v.2.2.1 0 := by
  intro v r0
  subst v
  subst r0
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  have hv1z := fullDivN1NormV_v1_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hshift_nz
  have hv2z := fullDivN1NormV_v2_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hprev := fullDivN1R1_v4_extended_remainder_lt
    bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hshift_nz
    hcarry2 hbltu_3 hbltu_2 hbltu_1
  have hprev' : n1StepRemainderVal r1 + n1StepTopVal r1 * 2^256 <
      ((fullDivN1NormV b0 b1 b2 b3).1).toNat := by
    subst r1
    simpa [hv1z, hv2z, EvmWord.val256] using hprev
  have htop_lt_v0 : r1.2.1.toNat < ((fullDivN1NormV b0 b1 b2 b3).1).toNat := by
    delta n1StepRemainderVal n1StepTopVal at hprev'
    unfold EvmWord.val256 at hprev'
    omega
  have hcon := fullDivN1R0_v4_step_conservation
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz
    hcarry2
  have hqeq := fullDivN1R0_v4_qout_eq_local_digit
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz
    hshift_nz hbltu_0
  have hlocal : n1LocalFloorDigit (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormU a0 a1 a2 a3 b0).1 r1.2.1 =
      (r1.2.1.toNat * 2^64 + (fullDivN1NormU a0 a1 a2 a3 b0).1.toNat) /
        ((fullDivN1NormV b0 b1 b2 b3).1).toNat := by
    delta n1LocalFloorDigit
    rw [show BitVec.ult r1.2.1 (fullDivN1NormV b0 b1 b2 b3).1 = true from
      (EvmWord.ult_iff).mpr htop_lt_v0]
    simp only [if_true]
  have hnum_eq :
      EvmWord.val256 (fullDivN1NormU a0 a1 a2 a3 b0).1
          r1.2.1 r1.2.2.1 r1.2.2.2.1 + r1.2.2.2.2.1.toNat * 2^256 =
        r1.2.1.toNat * 2^64 + (fullDivN1NormU a0 a1 a2 a3 b0).1.toNat := by
    delta n1StepRemainderVal n1StepTopVal at hprev'
    unfold EvmWord.val256 at hprev' ⊢
    omega
  have hge :
      (EvmWord.val256 (fullDivN1NormU a0 a1 a2 a3 b0).1
          r1.2.1 r1.2.2.1 r1.2.2.2.1 + r1.2.2.2.2.1.toNat * 2^256) /
        EvmWord.val256 (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 ≤
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
    rw [hqeq]
    rw [hlocal]
    rw [hnum_eq]
    unfold EvmWord.val256
    simp [hv1z, hv2z]
  exact n1StepExtendedRemainder_lt_of_floor_le
    (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    hvnz hcon hge

theorem fullDivN1ExtendedRemainder_v4_lt_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hbltu_3 : isTrialN1_v4_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_v4_j2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_v4_j1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_v4_j0 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    n1StepRemainderVal
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) +
        n1StepsCarryVal
          (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) <
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) := by
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  have hv1z := fullDivN1NormV_v1_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hshift_nz
  have hv2z := fullDivN1NormV_v2_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hnormv := fullDivN1NormV_val256_eq_scaled b0 b1 b2 b3 hb3z hshift_nz
  have hV_eq : EvmWord.val256 (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 =
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) := by
    rw [← hnormv]
    rw [hv3z]
  have hV_lt_pow64 : EvmWord.val256 (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 < 2^64 := by
    unfold EvmWord.val256
    simp [hv1z, hv2z]
    exact (fullDivN1NormV b0 b1 b2 b3).1.isLt
  have hR3 : n1StepRemainderVal r3 + n1StepTopVal r3 * 2^256 <
      EvmWord.val256 (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    subst r3
    exact fullDivN1R3_v4_extended_remainder_lt
      bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hshift_nz hcarry2 hbltu_3
  have hR2 : n1StepRemainderVal r2 + n1StepTopVal r2 * 2^256 <
      EvmWord.val256 (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    subst r2
    exact fullDivN1R2_v4_extended_remainder_lt
      bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hshift_nz hcarry2
      hbltu_3 hbltu_2
  have hR1 : n1StepRemainderVal r1 + n1StepTopVal r1 * 2^256 <
      EvmWord.val256 (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    subst r1
    exact fullDivN1R1_v4_extended_remainder_lt
      bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hshift_nz
      hcarry2 hbltu_3 hbltu_2 hbltu_1
  have hR0 : n1StepRemainderVal r0 + n1StepTopVal r0 * 2^256 <
      EvmWord.val256 (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    subst r0
    exact fullDivN1R0_v4_extended_remainder_lt
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz
      hshift_nz hcarry2 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have ht3 : n1StepTopVal r3 = 0 := by
    delta n1StepTopVal at hR3 ⊢
    omega
  have ht2 : n1StepTopVal r2 = 0 := by
    delta n1StepTopVal at hR2 ⊢
    omega
  have ht1 : n1StepTopVal r1 = 0 := by
    delta n1StepTopVal at hR1 ⊢
    omega
  have ht0 : n1StepTopVal r0 = 0 := by
    delta n1StepTopVal at hR0 ⊢
    omega
  rw [← hV_eq]
  change n1StepRemainderVal r0 + n1StepsCarryVal r3 r2 r1 r0 <
    EvmWord.val256 (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.1 0
  delta n1StepsCarryVal
  simp [ht0, ht1, ht2, ht3] at hR0 ⊢
  exact hR0

end EvmAsm.Evm64
