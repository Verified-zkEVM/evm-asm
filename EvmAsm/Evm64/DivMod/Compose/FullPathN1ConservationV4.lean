/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1ConservationV4

  v4 trial-quotient helpers for the n=1 full path.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1Conservation
import EvmAsm.Evm64.DivMod.Spec.V4
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Saturated local quotient digit for an n=1 step.

If the high word is below the divisor top word, this is the exact 128/64
floor. Otherwise the hardware path uses the max trial digit `2^64 - 1`. -/
@[irreducible]
def n1LocalFloorDigit (v0 u0 uTop : Word) : Nat :=
  if BitVec.ult uTop v0 then
    (uTop.toNat * 2^64 + u0.toNat) / v0.toNat
  else
    2^64 - 1

/-- v4 raw trial quotient bounds the saturated local quotient digit. This is
    the per-step shape needed by N1 later digits: the call path only needs
    `uTop < v0`, and the max path is exact by construction. -/
theorem iterN1_v4_rawTrial_ge_local_digit
    (bltu : Bool) (v0 u0 uTop : Word)
    (hv0_ge : v0.toNat ≥ 2^63)
    (hbranch : bltu = BitVec.ult uTop v0) :
    let qHat : Word := if bltu then div128Quot_v4 uTop u0 v0 else signExtend12 4095
    n1LocalFloorDigit v0 u0 uTop ≤ qHat.toNat := by
  intro qHat
  subst qHat
  delta n1LocalFloorDigit
  cases hult : BitVec.ult uTop v0
  · have hbltu_false : bltu = false := by
      simpa [hult] using hbranch
    rw [hbltu_false]
    simp only [Bool.false_eq_true, if_false]
    rw [signExtend12_4095_toNat]
  · have hbltu_true : bltu = true := by
      simpa [hult] using hbranch
    rw [hbltu_true]
    simp only [if_true]
    have huTop_lt_v0 : uTop.toNat < v0.toNat := (EvmWord.ult_iff).mp hult
    exact div128Quot_v4_ge_q_true_normalized_of_lt uTop u0 v0 hv0_ge huTop_lt_v0

@[irreducible]
def iterN1Call_v4 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot_v4 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- v4 per-iteration computation for n=1. The max path is unchanged; the call
    path uses the fully corrected `div128Quot_v4`. -/
def iterN1_v4 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN1Call_v4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[simp]
theorem iterN1_v4_true {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN1_v4 true v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN1Call_v4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN1_v4]

@[simp]
theorem iterN1_v4_false {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN1_v4 false v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN1_v4]

theorem iterN1_v4_qout_ge_trial_sub_two
    (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    let qHat : Word := if bltu then div128Quot_v4 u1 u0 v0 else signExtend12 4095
    let out := iterN1_v4 bltu v0 v1 v2 v3 u0 u1 u2 u3 uTop
    qHat.toNat - 2 ≤ out.1.toNat := by
  intro qHat out
  subst qHat
  subst out
  cases bltu
  · simp only [iterN1_v4_false]
    unfold iterN1Max
    exact iterWithDoubleAddback_qout_ge_sub_two
      (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop (by
        rw [signExtend12_4095_toNat]
        norm_num)
  · simp only [ite_true, iterN1_v4_true]
    unfold iterN1Call_v4
    exact iterWithDoubleAddback_qout_ge_tsub_two
      (div128Quot_v4 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[irreducible]
def fullDivN1R3_v4 (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  iterN1_v4 bltu_3 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)

@[irreducible]
def fullDivN1R2_v4 (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1_v4 bltu_2 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.1 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1

@[irreducible]
def fullDivN1R1_v4 (bltu_3 bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1_v4 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

@[irreducible]
def fullDivN1R0_v4 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1_v4 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

def isTrialN1_v4_j3 (bltu_3 : Bool) (a3 b0 : Word) : Prop :=
  isTrialN1_j3 bltu_3 a3 b0

def isTrialN1_v4_j2 (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Prop :=
  bltu_2 = BitVec.ult
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).1

def isTrialN1_v4_j1 (bltu_3 bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_1 = BitVec.ult
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).1

def isTrialN1_v4_j0 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_0 = BitVec.ult
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).1

theorem fullDivN1R3_v4_qout_ge_trial_sub_two
    (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let qHat : Word := if bltu_3 then div128Quot_v4 u.2.2.2.2 u.2.2.2.1 v.1
      else signExtend12 4095
    qHat.toNat - 2 ≤
      (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
  intro v u qHat
  subst v
  subst u
  subst qHat
  delta fullDivN1R3_v4
  exact iterN1_v4_qout_ge_trial_sub_two bltu_3
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    0 0 0

theorem fullDivN1R2_v4_qout_ge_trial_sub_two
    (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    let qHat : Word := if bltu_2 then div128Quot_v4 r3.2.1 u.2.2.1 v.1
      else signExtend12 4095
    qHat.toNat - 2 ≤
      (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
  intro v u r3 qHat
  subst v
  subst u
  subst r3
  subst qHat
  delta fullDivN1R2_v4
  exact iterN1_v4_qout_ge_trial_sub_two bltu_2
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1

theorem fullDivN1R1_v4_qout_ge_trial_sub_two
    (bltu_3 bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    let qHat : Word := if bltu_1 then div128Quot_v4 r2.2.1 u.2.1 v.1
      else signExtend12 4095
    qHat.toNat - 2 ≤
      (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
  intro v u r2 qHat
  subst v
  subst u
  subst r2
  subst qHat
  delta fullDivN1R1_v4
  exact iterN1_v4_qout_ge_trial_sub_two bltu_1
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1

theorem fullDivN1R0_v4_qout_ge_trial_sub_two
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    let qHat : Word := if bltu_0 then div128Quot_v4 r1.2.1 u.1 v.1
      else signExtend12 4095
    qHat.toNat - 2 ≤
      (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
  intro v u r1 qHat
  subst v
  subst u
  subst r1
  subst qHat
  delta fullDivN1R0_v4
  exact iterN1_v4_qout_ge_trial_sub_two bltu_0
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1

theorem fullDivN1R3_v4_rawTrial_ge_local_digit
    (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hbltu_3 : isTrialN1_v4_j3 bltu_3 a3 b0) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let qHat : Word := if bltu_3 then div128Quot_v4 u.2.2.2.2 u.2.2.2.1 v.1
      else signExtend12 4095
    n1LocalFloorDigit v.1 u.2.2.2.1 u.2.2.2.2 ≤ qHat.toNat := by
  intro v u qHat
  subst v
  subst u
  subst qHat
  have hv0_ge : ((fullDivN1NormV b0 b1 b2 b3).1).toNat ≥ 2^63 :=
    fullDivN1NormV_v0_ge_pow63_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  exact iterN1_v4_rawTrial_ge_local_digit bltu_3
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    hv0_ge (by
      delta isTrialN1_v4_j3 isTrialN1_j3 at hbltu_3
      simpa [fullDivN1NormU, fullDivN1NormV, fullDivN1Shift, fullDivN1AntiShift]
        using hbltu_3)

theorem fullDivN1R2_v4_rawTrial_ge_local_digit
    (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hbltu_2 : isTrialN1_v4_j2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    let qHat : Word := if bltu_2 then div128Quot_v4 r3.2.1 u.2.2.1 v.1
      else signExtend12 4095
    n1LocalFloorDigit v.1 u.2.2.1 r3.2.1 ≤ qHat.toNat := by
  intro v u r3 qHat
  subst v
  subst u
  subst r3
  subst qHat
  have hv0_ge : ((fullDivN1NormV b0 b1 b2 b3).1).toNat ≥ 2^63 :=
    fullDivN1NormV_v0_ge_pow63_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  exact iterN1_v4_rawTrial_ge_local_digit bltu_2
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    hv0_ge (by
      delta isTrialN1_v4_j2 at hbltu_2
      simpa using hbltu_2)

theorem fullDivN1R1_v4_rawTrial_ge_local_digit
    (bltu_3 bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hbltu_1 : isTrialN1_v4_j1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    let qHat : Word := if bltu_1 then div128Quot_v4 r2.2.1 u.2.1 v.1
      else signExtend12 4095
    n1LocalFloorDigit v.1 u.2.1 r2.2.1 ≤ qHat.toNat := by
  intro v u r2 qHat
  subst v
  subst u
  subst r2
  subst qHat
  have hv0_ge : ((fullDivN1NormV b0 b1 b2 b3).1).toNat ≥ 2^63 :=
    fullDivN1NormV_v0_ge_pow63_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  exact iterN1_v4_rawTrial_ge_local_digit bltu_1
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    hv0_ge (by
      delta isTrialN1_v4_j1 at hbltu_1
      simpa using hbltu_1)

theorem fullDivN1R0_v4_rawTrial_ge_local_digit
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hbltu_0 : isTrialN1_v4_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    let qHat : Word := if bltu_0 then div128Quot_v4 r1.2.1 u.1 v.1
      else signExtend12 4095
    n1LocalFloorDigit v.1 u.1 r1.2.1 ≤ qHat.toNat := by
  intro v u r1 qHat
  subst v
  subst u
  subst r1
  subst qHat
  have hv0_ge : ((fullDivN1NormV b0 b1 b2 b3).1).toNat ≥ 2^63 :=
    fullDivN1NormV_v0_ge_pow63_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  exact iterN1_v4_rawTrial_ge_local_digit bltu_0
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    hv0_ge (by
      delta isTrialN1_v4_j0 at hbltu_0
      simpa using hbltu_0)

@[irreducible]
def fullDivN1QuotientVal_v4
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Nat :=
  let B := 2^64
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  r3.1.toNat * B^3 + r2.1.toNat * B^2 + r1.1.toNat * B + r0.1.toNat

theorem fullDivN1QuotientVal_v4_eq_val256
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN1QuotientVal_v4 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.val256
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  delta fullDivN1QuotientVal_v4
  unfold EvmWord.val256
  ring

@[irreducible]
def fullDivN1CorrectedTrialVal_v4
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Nat :=
  let B := 2^64
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let qHat3 : Word := if bltu_3 then div128Quot_v4 u.2.2.2.2 u.2.2.2.1 v.1
    else signExtend12 4095
  let qHat2 : Word := if bltu_2 then div128Quot_v4 r3.2.1 u.2.2.1 v.1
    else signExtend12 4095
  let qHat1 : Word := if bltu_1 then div128Quot_v4 r2.2.1 u.2.1 v.1
    else signExtend12 4095
  let qHat0 : Word := if bltu_0 then div128Quot_v4 r1.2.1 u.1 v.1
    else signExtend12 4095
  (qHat3.toNat - 2) * B^3 + (qHat2.toNat - 2) * B^2 +
    (qHat1.toNat - 2) * B + (qHat0.toNat - 2)

theorem fullDivN1CorrectedTrialVal_v4_le_quotientVal_v4
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN1CorrectedTrialVal_v4 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 ≤
      fullDivN1QuotientVal_v4 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 := by
  have h3 := fullDivN1R3_v4_qout_ge_trial_sub_two
    bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  have h2 := fullDivN1R2_v4_qout_ge_trial_sub_two
    bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  have h1 := fullDivN1R1_v4_qout_ge_trial_sub_two
    bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  have h0 := fullDivN1R0_v4_qout_ge_trial_sub_two
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  delta fullDivN1CorrectedTrialVal_v4 fullDivN1QuotientVal_v4
  simp only [] at h3 h2 h1 h0 ⊢
  nlinarith [h3, h2, h1, h0]

end EvmAsm.Evm64
