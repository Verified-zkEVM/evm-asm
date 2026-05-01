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

theorem mulsubN4_c3_eq_zero_of_qv0_le_low
    (q v0 u0 u1 u2 u3 : Word)
    (hle : q.toNat * v0.toNat ≤ u1.toNat * 2^64 + u0.toNat) :
    (mulsubN4 q v0 0 0 0 u0 u1 u2 u3).2.2.2.2 = 0 := by
  by_contra hc3_ne
  have hc3_one := mulsubN4_c3_eq_one_v3_zero q v0 0 0 u0 u1 u2 u3 hc3_ne
  have hmul := mulsubN4_val256_eq q v0 0 0 0 u0 u1 u2 u3
  let ms := mulsubN4 q v0 0 0 0 u0 u1 u2 u3
  have hbound : EvmWord.val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2^256 :=
    EvmWord.val256_bound ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
  have hlow_le : u1.toNat * 2^64 + u0.toNat ≤ EvmWord.val256 u0 u1 u2 u3 := by
    unfold EvmWord.val256
    nlinarith [u2.isLt, u3.isLt]
  have hmul' : EvmWord.val256 u0 u1 u2 u3 + 2^256 =
      EvmWord.val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 + q.toNat * v0.toNat := by
    subst ms
    simp only [] at hmul
    rw [hc3_one] at hmul
    unfold EvmWord.val256 at hmul ⊢
    norm_num at hmul ⊢
    exact hmul
  have hval_lt_qv0 : EvmWord.val256 u0 u1 u2 u3 < q.toNat * v0.toNat := by
    nlinarith [hbound, hmul']
  have : q.toNat * v0.toNat ≤ EvmWord.val256 u0 u1 u2 u3 := le_trans hle hlow_le
  omega

theorem iterWithDoubleAddback_qout_eq_q_of_qv0_le_low
    (q v0 u0 u1 u2 u3 uTop : Word)
    (hle : q.toNat * v0.toNat ≤ u1.toNat * 2^64 + u0.toNat) :
    (iterWithDoubleAddback q v0 0 0 0 u0 u1 u2 u3 uTop).1 = q := by
  have hc3 := mulsubN4_c3_eq_zero_of_qv0_le_low q v0 u0 u1 u2 u3 hle
  have hb : ¬ BitVec.ult uTop (mulsubN4 q v0 0 0 0 u0 u1 u2 u3).2.2.2.2 := by
    rw [hc3]
    exact (EvmWord.ult_iff).not.mpr (by simp)
  have hout := iterWithDoubleAddback_no_borrow (qHat := q) (v0 := v0) (v1 := 0)
      (v2 := 0) (v3 := 0) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
      (uTop := uTop) hb
  simp only [] at hout
  rw [hout]

theorem iterN1_v4_qout_eq_local_digit
    (bltu : Bool) (v0 u0 u1 u2 u3 uTop : Word)
    (hv0_ge : v0.toNat ≥ 2^63)
    (hbranch : bltu = BitVec.ult u1 v0) :
    (iterN1_v4 bltu v0 0 0 0 u0 u1 u2 u3 uTop).1.toNat =
      n1LocalFloorDigit v0 u0 u1 := by
  cases hult : BitVec.ult u1 v0
  · have hbltu_false : bltu = false := by simpa [hult] using hbranch
    rw [hbltu_false]
    simp only [iterN1_v4_false]
    unfold iterN1Max n1LocalFloorDigit
    rw [hult]
    simp only [Bool.false_eq_true, if_false]
    have hnot : ¬ BitVec.ult u1 v0 := by simp [hult]
    have hv0_le_u1 : v0.toNat ≤ u1.toNat := by
      exact le_of_not_gt (fun h => hnot ((EvmWord.ult_iff).mpr h))
    have hle : (signExtend12 (4095 : BitVec 12) : Word).toNat * v0.toNat ≤
        u1.toNat * 2^64 + u0.toNat := by
      rw [signExtend12_4095_toNat]
      have hmul := Nat.mul_le_mul_right (2^64) hv0_le_u1
      calc
        (2^64 - 1) * v0.toNat ≤ 2^64 * v0.toNat := by
          exact Nat.mul_le_mul_right v0.toNat (by norm_num)
        _ = v0.toNat * 2^64 := by rw [Nat.mul_comm]
        _ ≤ u1.toNat * 2^64 := by simpa [Nat.mul_comm] using hmul
        _ ≤ u1.toNat * 2^64 + u0.toNat := Nat.le_add_right _ _
    rw [iterWithDoubleAddback_qout_eq_q_of_qv0_le_low _ _ _ _ _ _ _ hle]
    rw [signExtend12_4095_toNat]
  · have hbltu_true : bltu = true := by simpa [hult] using hbranch
    rw [hbltu_true]
    simp only [iterN1_v4_true]
    unfold iterN1Call_v4 n1LocalFloorDigit
    rw [hult]
    simp only [if_true]
    have hq_eq := div128Quot_v4_eq_q_true_normalized_of_lt u1 u0 v0 hv0_ge
      ((EvmWord.ult_iff).mp hult)
    have hle :
        (div128Quot_v4 u1 u0 v0).toNat * v0.toNat ≤ u1.toNat * 2^64 + u0.toNat := by
      rw [hq_eq]
      exact Nat.div_mul_le_self _ _
    rw [iterWithDoubleAddback_qout_eq_q_of_qv0_le_low _ _ _ _ _ _ _ hle]
    rw [hq_eq]

theorem iterN1_v4_val256_conservation_v3_zero_of_carry2
    (bltu : Bool) (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| (0 : Word) ≠ 0)
    (hcarry2 : Carry2NzAll v0 v1 v2 0) :
    let out := iterN1_v4 bltu v0 v1 v2 0 u0 u1 u2 u3 uTop
    EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 =
      out.1.toNat * EvmWord.val256 v0 v1 v2 0 +
        EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
        out.2.2.2.2.2.toNat * 2^256 := by
  cases bltu
  · simp only [iterN1_v4_false]
    unfold iterN1Max
    exact iterWithDoubleAddback_val256_conservation_v3_zero_of_carry2
      (signExtend12 4095) v0 v1 v2 u0 u1 u2 u3 uTop hbnz
      (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop)
  · simp only [iterN1_v4_true]
    unfold iterN1Call_v4
    exact iterWithDoubleAddback_val256_conservation_v3_zero_of_carry2
      (div128Quot_v4 u1 u0 v0) v0 v1 v2 u0 u1 u2 u3 uTop hbnz
      (hcarry2 (div128Quot_v4 u1 u0 v0) u0 u1 u2 u3 uTop)

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

theorem fullDivN1R3_v4_qout_eq_local_digit
    (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hbltu_3 : isTrialN1_v4_j3 bltu_3 a3 b0) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat =
      n1LocalFloorDigit v.1 u.2.2.2.1 u.2.2.2.2 := by
  intro v u
  subst v
  subst u
  have hv0_ge : ((fullDivN1NormV b0 b1 b2 b3).1).toNat ≥ 2^63 :=
    fullDivN1NormV_v0_ge_pow63_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hv1z := fullDivN1NormV_v1_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hshift_nz
  have hv2z := fullDivN1NormV_v2_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hbranch : bltu_3 = BitVec.ult
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (fullDivN1NormV b0 b1 b2 b3).1 := by
    delta isTrialN1_v4_j3 isTrialN1_j3 at hbltu_3
    simpa [fullDivN1NormU, fullDivN1NormV, fullDivN1Shift, fullDivN1AntiShift]
      using hbltu_3
  delta fullDivN1R3_v4
  simpa [hv1z, hv2z, hv3z] using
    iterN1_v4_qout_eq_local_digit bltu_3
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      0 0 0 hv0_ge hbranch

theorem fullDivN1R2_v4_qout_eq_local_digit
    (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hbltu_2 : isTrialN1_v4_j2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat =
      n1LocalFloorDigit v.1 u.2.2.1 r3.2.1 := by
  intro v u r3
  subst v
  subst u
  subst r3
  have hv0_ge : ((fullDivN1NormV b0 b1 b2 b3).1).toNat ≥ 2^63 :=
    fullDivN1NormV_v0_ge_pow63_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hv1z := fullDivN1NormV_v1_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hshift_nz
  have hv2z := fullDivN1NormV_v2_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  delta fullDivN1R2_v4
  simpa [hv1z, hv2z, hv3z] using
    iterN1_v4_qout_eq_local_digit bltu_2
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      hv0_ge hbltu_2

theorem fullDivN1R1_v4_qout_eq_local_digit
    (bltu_3 bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hbltu_1 : isTrialN1_v4_j1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat =
      n1LocalFloorDigit v.1 u.2.1 r2.2.1 := by
  intro v u r2
  subst v
  subst u
  subst r2
  have hv0_ge : ((fullDivN1NormV b0 b1 b2 b3).1).toNat ≥ 2^63 :=
    fullDivN1NormV_v0_ge_pow63_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hv1z := fullDivN1NormV_v1_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hshift_nz
  have hv2z := fullDivN1NormV_v2_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  delta fullDivN1R1_v4
  simpa [hv1z, hv2z, hv3z] using
    iterN1_v4_qout_eq_local_digit bltu_1
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      hv0_ge hbltu_1

theorem fullDivN1R0_v4_qout_eq_local_digit
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hbltu_0 : isTrialN1_v4_j0 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat =
      n1LocalFloorDigit v.1 u.1 r1.2.1 := by
  intro v u r1
  subst v
  subst u
  subst r1
  have hv0_ge : ((fullDivN1NormV b0 b1 b2 b3).1).toNat ≥ 2^63 :=
    fullDivN1NormV_v0_ge_pow63_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hv1z := fullDivN1NormV_v1_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hshift_nz
  have hv2z := fullDivN1NormV_v2_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  delta fullDivN1R0_v4
  simpa [hv1z, hv2z, hv3z] using
    iterN1_v4_qout_eq_local_digit bltu_0
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      hv0_ge hbltu_0

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

@[irreducible]
def fullDivN1LocalFloorVal_v4
    (bltu_3 bltu_2 bltu_1 _bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Nat :=
  let B := 2^64
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let local3 := n1LocalFloorDigit v.1 u.2.2.2.1 u.2.2.2.2
  let local2 := n1LocalFloorDigit v.1 u.2.2.1 r3.2.1
  let local1 := n1LocalFloorDigit v.1 u.2.1 r2.2.1
  let local0 := n1LocalFloorDigit v.1 u.1 r1.2.1
  (local3 - 2) * B^3 + (local2 - 2) * B^2 + (local1 - 2) * B + (local0 - 2)

theorem fullDivN1LocalFloorVal_v4_le_correctedTrialVal_v4
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hbltu_3 : isTrialN1_v4_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_v4_j2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_v4_j1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_v4_j0 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1LocalFloorVal_v4 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 ≤
      fullDivN1CorrectedTrialVal_v4 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 := by
  have h3 := fullDivN1R3_v4_rawTrial_ge_local_digit
    bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hbltu_3
  have h2 := fullDivN1R2_v4_rawTrial_ge_local_digit
    bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hbltu_2
  have h1 := fullDivN1R1_v4_rawTrial_ge_local_digit
    bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hbltu_1
  have h0 := fullDivN1R0_v4_rawTrial_ge_local_digit
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb1z hb2z hb3z hbnz hbltu_0
  have h3' := Nat.sub_le_sub_right h3 2
  have h2' := Nat.sub_le_sub_right h2 2
  have h1' := Nat.sub_le_sub_right h1 2
  have h0' := Nat.sub_le_sub_right h0 2
  delta fullDivN1LocalFloorVal_v4 fullDivN1CorrectedTrialVal_v4
  simp only [] at h3' h2' h1' h0' ⊢
  nlinarith [h3', h2', h1', h0']

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

theorem fullDivN1R3_v4_step_conservation
    (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    n1StepConservation v.1 v.2.1 v.2.2.1 u.2.2.2.1 u.2.2.2.2 0 0 0
      (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u
  subst v
  subst u
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_v4_val256_conservation_v3_zero_of_carry2 bltu_3
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    0 0 0 hvnz hc
  delta n1StepConservation
  delta fullDivN1R3_v4
  simpa [hv3z] using h

theorem fullDivN1R2_v4_step_conservation
    (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepConservation v.1 v.2.1 v.2.2.1 u.2.2.1
      r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
      (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u r3
  subst v
  subst u
  subst r3
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_v4_val256_conservation_v3_zero_of_carry2 bltu_2
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hvnz hc
  delta n1StepConservation
  delta fullDivN1R2_v4
  simpa [hv3z] using h

theorem fullDivN1R1_v4_step_conservation
    (bltu_3 bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepConservation v.1 v.2.1 v.2.2.1 u.2.1
      r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
      (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u r2
  subst v
  subst u
  subst r2
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_v4_val256_conservation_v3_zero_of_carry2 bltu_1
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hvnz hc
  delta n1StepConservation
  delta fullDivN1R1_v4
  simpa [hv3z] using h

theorem fullDivN1R0_v4_step_conservation
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepConservation v.1 v.2.1 v.2.2.1 u.1
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u r1
  subst v
  subst u
  subst r1
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_v4_val256_conservation_v3_zero_of_carry2 bltu_0
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hvnz hc
  delta n1StepConservation
  delta fullDivN1R0_v4
  simpa [hv3z] using h

@[irreducible]
def fullDivN1StepsConservation_v4
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  n1StepsConservation v u r3 r2 r1 r0

theorem fullDivN1StepsConservation_v4_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1StepsConservation_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  delta fullDivN1StepsConservation_v4
  delta n1StepsConservation
  constructor
  · exact fullDivN1R3_v4_step_conservation
      bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2
  constructor
  · exact fullDivN1R2_v4_step_conservation
      bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2
  constructor
  · exact fullDivN1R1_v4_step_conservation
      bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz
      hcarry2
  · exact fullDivN1R0_v4_step_conservation
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z
      hbnz hcarry2

@[irreducible]
def fullDivN1StepsTelescoped_v4
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  n1StepsTelescoped v u r3 r2 r1 r0

theorem fullDivN1StepsTelescoped_v4_of_conservation
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hsteps : fullDivN1StepsConservation_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1StepsTelescoped_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  delta fullDivN1StepsConservation_v4 at hsteps
  delta fullDivN1StepsTelescoped_v4
  exact n1StepsTelescoped_of_conservation
    (fullDivN1NormV b0 b1 b2 b3)
    (fullDivN1NormU a0 a1 a2 a3 b0)
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    hsteps

theorem fullDivN1StepsTelescoped_v4_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1StepsTelescoped_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
  fullDivN1StepsTelescoped_v4_of_conservation
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    (fullDivN1StepsConservation_v4_of_runtime
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hb1z hb2z hb3z hbnz hcarry2)

theorem fullDivN1QuotientVal_v4_le_div_of_telescoped
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (htel : fullDivN1StepsTelescoped_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1QuotientVal_v4 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 ≤
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 := by
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let qVal := r3.1.toNat * (2^64)^3 + r2.1.toNat * (2^64)^2 +
    r1.1.toNat * (2^64) + r0.1.toNat
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hnormu := fullDivN1NormU_val256_eq_scaled_with_overflow
    a0 a1 a2 a3 b0 hshift_nz
  have hnormv := fullDivN1NormV_val256_eq_scaled b0 b1 b2 b3 hb3z hshift_nz
  have heq : EvmWord.val256 a0 a1 a2 a3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) =
      qVal * (EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) +
        (n1StepRemainderVal r0 + n1StepsCarryVal r3 r2 r1 r0) := by
    delta fullDivN1StepsTelescoped_v4 n1StepsTelescoped at htel
    dsimp only at htel
    rw [← hnormu]
    rw [← hnormv]
    rw [hv3z]
    simp only [qVal, r0, r1, r2, r3]
    norm_num at htel ⊢
    omega
  have hb_pos : 0 < EvmWord.val256 b0 b1 b2 b3 *
      2 ^ ((fullDivN1Shift b0).toNat % 64) := by
    have hb : 0 < EvmWord.val256 b0 b1 b2 b3 := EvmWord.val256_pos_of_or_ne_zero hbnz
    positivity
  have hq_le := EvmWord.quotient_le_of_euclidean hb_pos heq
  rw [div_mul_pow_mul_pow_eq_div] at hq_le
  delta fullDivN1QuotientVal_v4
  simp only [qVal, r0, r1, r2, r3] at hq_le ⊢
  exact hq_le

theorem fullDivN1QuotientVal_v4_le_div_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1QuotientVal_v4 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 ≤
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 := by
  exact fullDivN1QuotientVal_v4_le_div_of_telescoped
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb2z hb3z hbnz hshift_nz
    (fullDivN1StepsTelescoped_v4_of_runtime
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hb1z hb2z hb3z hbnz hcarry2)

theorem fullDivN1ExtendedRemainder_v4_lt_of_runtime_quotientVal_le
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
    (hge : EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
      fullDivN1QuotientVal_v4 bltu_3 bltu_2 bltu_1 bltu_0
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
  let qVal := r3.1.toNat * (2^64)^3 + r2.1.toNat * (2^64)^2 +
    r1.1.toNat * (2^64) + r0.1.toNat
  have htel : n1StepsTelescoped
      (fullDivN1NormV b0 b1 b2 b3)
      (fullDivN1NormU a0 a1 a2 a3 b0)
      (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) := by
    exact n1StepsTelescoped_of_conservation
      (fullDivN1NormV b0 b1 b2 b3)
      (fullDivN1NormU a0 a1 a2 a3 b0)
      (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
      (by
        delta n1StepsConservation
        exact ⟨
          fullDivN1R3_v4_step_conservation
            bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2,
          fullDivN1R2_v4_step_conservation
            bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2,
          fullDivN1R1_v4_step_conservation
            bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz
            hcarry2,
          fullDivN1R0_v4_step_conservation
            bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z
            hbnz hcarry2⟩)
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hnormu := fullDivN1NormU_val256_eq_scaled_with_overflow
    a0 a1 a2 a3 b0 hshift_nz
  have hnormv := fullDivN1NormV_val256_eq_scaled b0 b1 b2 b3 hb3z hshift_nz
  have heq : EvmWord.val256 a0 a1 a2 a3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) =
      qVal * (EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) +
        (n1StepRemainderVal r0 + n1StepsCarryVal r3 r2 r1 r0) := by
    delta n1StepsTelescoped at htel
    dsimp only at htel
    rw [← hnormu]
    rw [← hnormv]
    rw [hv3z]
    simp only [qVal, r0, r1, r2, r3]
    norm_num at htel ⊢
    omega
  have hb_pos : 0 < EvmWord.val256 b0 b1 b2 b3 *
      2 ^ ((fullDivN1Shift b0).toNat % 64) := by
    have hb : 0 < EvmWord.val256 b0 b1 b2 b3 := EvmWord.val256_pos_of_or_ne_zero hbnz
    positivity
  have hge' : EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤ qVal := by
    delta fullDivN1QuotientVal_v4 at hge
    simpa [qVal, r0, r1, r2, r3] using hge
  have hge_scaled :
      (EvmWord.val256 a0 a1 a2 a3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) /
        (EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) ≤
      qVal := by
    rw [div_mul_pow_mul_pow_eq_div]
    exact hge'
  have ⟨_, hr_lt⟩ := EvmWord.remainder_lt_of_ge_floor hb_pos heq hge_scaled
  simpa [r0, r1, r2, r3] using hr_lt

theorem fullDivN1ExtendedRemainder_v4_lt_of_runtime_correctedTrial_le
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
    (hge : EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
      fullDivN1CorrectedTrialVal_v4 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3) :
    n1StepRemainderVal
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) +
        n1StepsCarryVal
          (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) <
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) := by
  have hcorr := fullDivN1CorrectedTrialVal_v4_le_quotientVal_v4
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  exact fullDivN1ExtendedRemainder_v4_lt_of_runtime_quotientVal_le
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb1z hb2z hb3z hbnz hshift_nz hcarry2 (Nat.le_trans hge hcorr)

theorem fullDivN1ExtendedRemainder_v4_lt_of_runtime_localFloor_le
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
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge : EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
      fullDivN1LocalFloorVal_v4 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3) :
    n1StepRemainderVal
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) +
        n1StepsCarryVal
          (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) <
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) := by
  have hlocal := fullDivN1LocalFloorVal_v4_le_correctedTrialVal_v4
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb1z hb2z hb3z hbnz hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact fullDivN1ExtendedRemainder_v4_lt_of_runtime_correctedTrial_le
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb1z hb2z hb3z hbnz hshift_nz hcarry2 (Nat.le_trans hge hlocal)

end EvmAsm.Evm64
