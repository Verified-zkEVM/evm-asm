module

public import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridgeGetLimbStep
public import EvmAsm.Evm64.DivMod.Spec.N1CarryZeroReducers
public import EvmAsm.Evm64.DivMod.Spec.N1PathCallbacks
public import EvmAsm.Evm64.DivMod.Spec.N1TrialWitnesses

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

private theorem finalCarryZero_of_conservation_bound
    {a b q r carry : Nat}
    (hbpos : 0 < b)
    (hcons : a = q * b + r + carry * 2 ^ 256)
    (hge : a / b ≤ q)
    (hb_lt : b < 2 ^ 256) :
    carry = 0 := by
  have hcons' : a = q * b + (r + carry * 2 ^ 256) := by
    omega
  have hrem_lt : r + carry * 2 ^ 256 < b :=
    (EvmWord.remainder_lt_of_ge_floor hbpos hcons' hge).2
  by_contra hcarry_nz
  have hcarry_pos : 0 < carry := by omega
  have hrem_ge : 2 ^ 256 ≤ r + carry * 2 ^ 256 := by
    nlinarith
  omega

/-- The raw normalized n=1 conservation equation plus the legacy quotient
    overestimate forces the final overflow carry to be zero. -/
theorem fullDivN1FinalCarryZero_of_conservation_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0)
    (hcons : fullDivN1NormalizedConservation bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hpow : 0 < 2 ^ (fullDivN1Shift b0).toNat := by
    positivity
  have hbScaled_pos :
      0 < EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat := by
    have hbpos : 0 < EvmWord.val256 b0 b1 b2 b3 :=
      EvmWord.val256_pos_of_or_ne_zero hbnz
    positivity
  have hgeScaled :
      (EvmWord.val256 a0 a1 a2 a3 * 2 ^ (fullDivN1Shift b0).toNat) /
        (EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat) ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat := by
    rw [Nat.mul_div_mul_right _ _ hpow]
    exact hge
  have hs_le64 : (fullDivN1Shift b0).toNat ≤ 64 := by
    rw [fullDivN1Shift_unfold]
    have hle := clzResult_fst_toNat_le b0
    omega
  have hb3_bound :
      b3.toNat < 2 ^ (64 - (fullDivN1Shift b0).toNat) := by
    rw [hb3z]
    simp
  have hbVal_lt :
      EvmWord.val256 b0 b1 b2 b3 <
        2 ^ (256 - (fullDivN1Shift b0).toNat) :=
    EvmWord.val256_lt_of_b3_bound b0 b1 b2 b3 hs_le64 hb3_bound
  have hbScaled_lt :
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat <
        2 ^ 256 := by
    calc
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat
          < 2 ^ (256 - (fullDivN1Shift b0).toNat) *
              2 ^ (fullDivN1Shift b0).toNat :=
            (Nat.mul_lt_mul_right hpow).mpr hbVal_lt
      _ = 2 ^ 256 := by
            rw [← pow_add]
            congr 1
            omega
  have hcarry_toNat_zero :
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2).toNat = 0 := by
    unfold fullDivN1NormalizedConservation at hcons
    exact finalCarryZero_of_conservation_bound
      (hbpos := hbScaled_pos)
      (hcons := hcons)
      (hge := hgeScaled)
      (hb_lt := hbScaled_lt)
  unfold fullDivN1FinalCarryZero
  exact BitVec.eq_of_toNat_eq hcarry_toNat_zero

/-- Step-conservation wrapper for the final n=1 carry-zero fact. -/
theorem fullDivN1FinalCarryZero_of_step_conservation_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hcons :
      fullDivN1NormalizedConservation bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 :=
    fullDivN1NormalizedConservation_of_step_conservation
      bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero
  exact fullDivN1FinalCarryZero_of_conservation_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hb3z hcons hge

/-- Raw dispatcher-surface carry form of
    `fullDivN1FinalCarryZero_of_step_conservation_overestimate`. -/
theorem fullDivN1FinalCarryZero_of_raw_step_conservation_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hcarry2Norm : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2 := by
    unfold fullDivN1NormV fullDivN1Shift fullDivN1AntiShift
    rw [fullDivN1Shift_unfold]
    exact hcarry2
  exact fullDivN1FinalCarryZero_of_step_conservation_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0
    a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz hcarry2Norm
    hr3_zero hr2_zero hr1_zero hge

/-- Step-conservation bridge to the normalized n=1 Euclidean equation,
    deriving the final carry-zero witness internally from the legacy quotient
    overestimate. -/
theorem fullDivN1NormalizedMulSubEq_of_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hfinal_zero : fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
    fullDivN1FinalCarryZero_of_step_conservation_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact fullDivN1NormalizedMulSubEq_of_step_conservation
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hfinal_zero

/-- Raw dispatcher-surface carry form of
    `fullDivN1NormalizedMulSubEq_of_step_conservation_overestimate_final`. -/
theorem fullDivN1NormalizedMulSubEq_of_raw_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hfinal_zero : fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
    fullDivN1FinalCarryZero_of_raw_step_conservation_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact fullDivN1NormalizedMulSubEq_of_raw_step_conservation
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hfinal_zero

/-- Step-conservation bridge to the normalized n=1 final-remainder bound,
    deriving the final carry-zero and normalized mulsub facts internally from
    the legacy quotient overestimate. -/
theorem fullDivN1NormalizedRemainderLt_of_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
    fullDivN1NormalizedMulSubEq_of_step_conservation_overestimate_final
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact fullDivN1NormalizedRemainderLt_of_mulsub_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hge

/-- Raw dispatcher-surface carry form of
    `fullDivN1NormalizedRemainderLt_of_step_conservation_overestimate_final`. -/
theorem fullDivN1NormalizedRemainderLt_of_raw_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hcarry2Norm : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2 := by
    unfold fullDivN1NormV fullDivN1Shift fullDivN1AntiShift
    rw [fullDivN1Shift_unfold]
    exact hcarry2
  exact fullDivN1NormalizedRemainderLt_of_step_conservation_overestimate_final
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz hcarry2Norm
    hr3_zero hr2_zero hr1_zero hge

/-- n=1 quotient bridge from raw step-conservation witnesses plus the legacy
    quotient overestimate, deriving the final carry-zero and normalized
    remainder facts internally. -/
theorem fullDivN1QuotientWord_eq_div_of_raw_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  have hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
    fullDivN1NormalizedMulSubEq_of_raw_step_conservation_overestimate_final
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  have hrem_lt : fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
    fullDivN1NormalizedRemainderLt_of_raw_step_conservation_overestimate_final
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact fullDivN1QuotientWord_eq_div_of_normalized_mulsub_remainder_lt
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hrem_lt

/-- Explicit-limb n=1 quotient bridge from raw step-conservation witnesses
    plus the legacy quotient overestimate, deriving the final carry-zero and
    normalized remainder facts internally. -/
theorem fullDivN1QuotientWord_eq_div_of_limbs_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b := by
  subst a0
  subst a1
  subst a2
  subst a3
  subst b0
  subst b1
  subst b2
  subst b3
  have hraw :=
    fullDivN1QuotientWord_eq_div_of_raw_step_conservation_overestimate_final
      bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  change
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => a.getLimbN 0
            | 1 => a.getLimbN 1
            | 2 => a.getLimbN 2
            | 3 => a.getLimbN 3)
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => b.getLimbN 0
            | 1 => b.getLimbN 1
            | 2 => b.getLimbN 2
            | 3 => b.getLimbN 3) at hraw
  exact hraw.trans (by
    congr
    · exact EvmWord.fromLimbs_match_getLimbN_id a
    · exact EvmWord.fromLimbs_match_getLimbN_id b)

/-- GetLimb-level n=1 quotient bridge from raw step-conservation witnesses
    plus the legacy quotient overestimate, deriving the final carry-zero and
    normalized remainder facts internally. -/
theorem fullDivN1QuotientWord_eq_div_of_getLimbN_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hb1z : b.getLimbN 1 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb3z : b.getLimbN 3 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero bltu_3
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hge :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) /
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3) ≤
        ((fullDivN1R3 bltu_3
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  exact fullDivN1QuotientWord_eq_div_of_limbs_step_conservation_overestimate_final
    bltu_3 bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl
    hbnz hb1z hb2z hb3z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hge

/-- GetLimb-level n=1 hdiv witness from raw step conservation plus the
    legacy quotient overestimate, deriving the final carry-zero fact
    internally. -/
theorem fullDivN1_getLimbN_of_getLimbN_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hb1z : b.getLimbN 1 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb3z : b.getLimbN 3 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero bltu_3
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hge :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) /
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3) ≤
        ((fullDivN1R3 bltu_3
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  have hfinal_zero : fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1FinalCarryZero_of_raw_step_conservation_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact fullDivN1_getLimbN_of_getLimbN_step_conservation_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hb1z hb2z hb3z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hfinal_zero hge

/-- Explicit-limb n=1 hdiv witness from raw step conservation plus the
    legacy quotient overestimate, deriving the final carry-zero fact
    internally. -/
theorem fullDivN1_getLimbN_of_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  subst a0
  subst a1
  subst a2
  subst a3
  subst b0
  subst b1
  subst b2
  subst b3
  exact fullDivN1_getLimbN_of_getLimbN_step_conservation_overestimate_final
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hb1z hb2z hb3z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hge

/-- Shape-specialized n=1 full division limb theorem from raw step
    conservation plus quotient-overestimate facts. The remaining unconditional
    step is to discharge `hcarry2`, the per-step carry-zero facts, and `hge`
    from the schoolbook arithmetic. -/
theorem n1_full_div_getLimbN_of_step_conservation_overestimate
    (a b : EvmWord) (bltu_2 bltu_1 bltu_0 : Bool)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hr2_zero : fullDivN1R2CarryZero true bltu_2
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hr1_zero : fullDivN1R1CarryZero true bltu_2 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hge : fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 true bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 true bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  exact fullDivN1_getLimbN_of_getLimbN_step_conservation_overestimate_final
    true bltu_2 bltu_1 bltu_0 hbnz hb1z hb2z hb3z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hge

/-- Shape-specialized n=1 full division limb theorem from a step-conservation
    path surface. This packages the forced branch witnesses and the step
    arithmetic facts in one eliminator. -/
theorem n1_shape_full_div_getLimbN_of_step_conservation_overestimate
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1StepOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnz hb3z hb2z hb1z hshift_nz
  obtain ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact ⟨bltu_2, bltu_1, bltu_0,
    hbltu_3, hbltu_2, hbltu_1, hbltu_0,
    n1_full_div_getLimbN_of_step_conservation_overestimate
      a b bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge⟩

/-- Shape-specialized n=1 quotient-word theorem from a step-conservation
    path surface. This keeps the selected branch booleans but drops the
    mechanical branch-proof witnesses from the conclusion. -/
theorem n1_quotient_word_of_step_conservation_path
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1StepOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnz hb3z hb2z hb1z hshift_nz
  obtain ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_step_conservation_overestimate_final
      true bltu_2 bltu_1 bltu_0 hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact ⟨bltu_2, bltu_1, bltu_0, hdivWord⟩

/-- Shape-specialized n=1 quotient-word package from a step-conservation path
    surface.

    This is the callable-stack package: it keeps the selected branch booleans
    and branch proofs, carries the normalized `Carry2NzAll` fact, and returns
    the quotient-word equality consumed by callable wrappers. -/
theorem n1_quotient_word_package_of_step_conservation_path
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1StepOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 0 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 1 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 2 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))) ∧
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnz hb3z hb2z hb1z hshift_nz
  obtain ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_step_conservation_overestimate_final
      true bltu_2 bltu_1 bltu_0 hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact ⟨bltu_2, bltu_1, bltu_0,
    hbltu_3, hbltu_2, hbltu_1, hbltu_0, hcarry2, hdivWord⟩

/-- Shape-specialized n=1 normalized mulsub plus quotient-overestimate theorem
    from a step-conservation path surface.

    This is the arithmetic package consumed by stack wrappers: it keeps the
    selected branch booleans and branch proofs, derives final carry-zero
    internally, and returns the normalized Euclidean equation together with the
    quotient upper-bound surface and quotient-word equality. -/
theorem n1_normalized_mulsub_overestimate_of_step_conservation_path
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1StepOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 0 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 1 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 2 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))) ∧
      fullDivN1NormalizedMulSubEq true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnz hb3z hb2z hb1z hshift_nz
  obtain ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hfinal_zero : fullDivN1FinalCarryZero true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1FinalCarryZero_of_raw_step_conservation_overestimate
      true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  have hmulsub : fullDivN1NormalizedMulSubEq true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1NormalizedMulSubEq_of_raw_step_conservation
      true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hfinal_zero
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_step_conservation_overestimate_final
      true bltu_2 bltu_1 bltu_0 hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact ⟨bltu_2, bltu_1, bltu_0,
    hbltu_3, hbltu_2, hbltu_1, hbltu_0, hcarry2, hmulsub, hge, hdivWord⟩

/-- Acceptance-shaped n=1 full division limb theorem from the
    step-conservation path surface.

    This is the consumer-facing form of
    `n1_shape_full_div_getLimbN_of_step_conservation_overestimate`: it keeps the
    chosen branch booleans but drops the mechanical branch-proof witnesses from
    the conclusion. -/
theorem n1_full_div_getLimbN_of_step_conservation_path
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1StepOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_2, bltu_1, bltu_0,
      _hbltu_3, _hbltu_2, _hbltu_1, _hbltu_0,
      _hcarry2, _hmulsub, _hge, hdivWord⟩ :=
    n1_normalized_mulsub_overestimate_of_step_conservation_path
      a b hbnz hb3z hb2z hb1z hshift_nz hpath
  exact ⟨bltu_2, bltu_1, bltu_0,
    fullDivN1_hdivs_of_word_eq true bltu_2 bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord⟩

/-- Package all-true n=1 path evidence from the all-phases overestimate path
    surface. The path provides the selected carry facts, the first no-wrap
    invariant, and quotient overestimate; the final normalized remainder bound
    is derived internally from those step-conservation facts. -/
theorem N1AllTruePathEvidence.ofAllPhasesOverestimatePath
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr1_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hfinal_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1AllPhasesOverestimatePathCallback a b) :
    N1AllTruePathEvidence a b := by
  obtain ⟨hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_all_true_of_remainders_lt
      a b hbnz hb3z hb2z hb1z hshift_nz hr3_lt hr2_lt hr1_lt
  obtain ⟨hcarry2, hinit_inv, hr2_zero, hr1_zero, hge⟩ :=
    hpath true true true hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hr3_zero : fullDivN1R3CarryZero true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1R3CarryZero_true_of_shape_all_phases_no_wrap
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hinit_inv
  have hrem_lt : fullDivN1NormalizedRemainderLt true true true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1NormalizedRemainderLt_of_raw_step_conservation_overestimate_final
      true true true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact ⟨hcarry2, hinit_inv, hr2_inv, hr1_inv, hfinal_inv, hrem_lt⟩

/-- A conjunct-level R3 no-wrap callback implies the existing all-phases
    callback by assembling the R3 invariant from its three local conjuncts. -/
theorem N1AllPhasesConjunctOverestimatePathCallback.toAllPhasesOverestimatePathCallback
    {a b : EvmWord}
    (hpath : N1AllPhasesConjunctOverestimatePathCallback a b) :
    N1AllPhasesOverestimatePathCallback a b := by
  intro bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  obtain ⟨hcarry2, h_r3_conjuncts, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  obtain ⟨h_un21, h_phase1, h_phase2⟩ := h_r3_conjuncts
  refine ⟨hcarry2, ?hinit_inv, hr2_zero, hr1_zero, hge⟩
  exact fullDivN1R3_all_phases_no_wrap_of_conjuncts
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    h_un21 h_phase1 h_phase2

/-- Package all-true n=1 path evidence from a conjunct-level R3 no-wrap path.
    This is the same surface as `ofAllPhasesOverestimatePath`, except callers
    may provide the selected R3 all-phases invariant as its three local
    no-wrap conjuncts. -/
theorem N1AllTruePathEvidence.ofAllPhasesConjunctOverestimatePath
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr1_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hfinal_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1AllPhasesConjunctOverestimatePathCallback a b) :
    N1AllTruePathEvidence a b := by
  exact N1AllTruePathEvidence.ofAllPhasesOverestimatePath
    a b hbnz hb3z hb2z hb1z hshift_nz hr3_lt hr2_lt hr1_lt
    hr2_inv hr1_inv hfinal_inv
    (N1AllPhasesConjunctOverestimatePathCallback.toAllPhasesOverestimatePathCallback hpath)

end EvmAsm.Evm64
