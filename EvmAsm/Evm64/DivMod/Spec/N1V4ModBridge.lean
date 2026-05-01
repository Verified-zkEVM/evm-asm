/-
  EvmAsm.Evm64.DivMod.Spec.N1V4ModBridge

  v4 n=1 MOD denormalization bridges.
-/

import EvmAsm.Evm64.DivMod.Spec.Dispatcher
import EvmAsm.Evm64.DivMod.Compose.FullPathN1RemainderV4

namespace EvmAsm.Evm64

open EvmAsm.Rv64

@[irreducible]
def fullModN1RemainderWord_v4 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 =>
        (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
    | 1 =>
        (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
    | 2 =>
        (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
    | 3 =>
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)))

theorem fullModN1_hmods_v4_of_word_eq
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hmod : fullModN1RemainderWord_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64)) := by
  constructor
  · rw [← hmod]
    delta fullModN1RemainderWord_v4
    exact EvmWord.getLimbN_fromLimbs_0
  constructor
  · rw [← hmod]
    delta fullModN1RemainderWord_v4
    exact EvmWord.getLimbN_fromLimbs_1
  constructor
  · rw [← hmod]
    delta fullModN1RemainderWord_v4
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hmod]
    delta fullModN1RemainderWord_v4
    exact EvmWord.getLimbN_fromLimbs_3

theorem fullModN1RemainderWord_v4_eq_mod_of_toNat_eq
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hmod_toNat :
      (fullModN1RemainderWord_v4 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.mod a b).toNat) :
    fullModN1RemainderWord_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b :=
  BitVec.eq_of_toNat_eq hmod_toNat

theorem fullModN1RemainderWord_v4_toNat
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullModN1RemainderWord_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat =
    EvmWord.val256
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64)) := by
  delta fullModN1RemainderWord_v4
  rw [EvmWord.fromLimbs_toNat]
  rfl

theorem fullModN1_hmods_v4_of_normalized_val256_eq
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (h_val_eq :
      EvmWord.val256
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 =
      EvmWord.val256 a0 a1 a2 a3 % EvmWord.val256 b0 b1 b2 b3 *
        2 ^ ((fullDivN1Shift b0).toNat % 64)) :
    (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0 := by
    rw [hb0, hb1, hb2, hb3]
    exact hbnz
  have hs0 : 0 < (fullDivN1Shift b0).toNat % 64 := by
    rw [fullDivN1Shift_toNat_mod_eq]
    exact fullDivN1Shift_toNat_pos_of_ne_zero hshift_nz
  have hs : (fullDivN1Shift b0).toNat % 64 < 64 :=
    Nat.mod_lt _ (by decide)
  have h_val_eq' : EvmWord.val256
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 =
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((fullDivN1Shift b0).toNat % 64) := by
    rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]
    exact h_val_eq
  have hmods :=
    denorm_4limb_eq_mod_of_val256_eq_amod_pow_s_of_or_ne_zero hs0 hs hbnz' h_val_eq'
  have hanti_mod :
      (signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64 =
        64 - (fullDivN1Shift b0).toNat % 64 := by
    rw [fullDivN1AntiShift_toNat_mod_eq hshift_nz,
      fullDivN1Shift_toNat_mod_eq b0]
  rw [hanti_mod]
  exact hmods

theorem fullModN1_hmods_v4_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
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
    (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64)) := by
  have h_val_eq := fullDivN1RemainderVal_v4_eq_mod_mul_pow_of_runtime
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb1z hb2z hb3z hbnz hshift_nz hcarry2 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact fullModN1_hmods_v4_of_normalized_val256_eq
    bltu_3 bltu_2 bltu_1 bltu_0 a b a0 a1 a2 a3 b0 b1 b2 b3
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hshift_nz
    (by
      unfold n1StepRemainderVal at h_val_eq
      exact h_val_eq)

theorem fullModN1RemainderWord_v4_eq_mod_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
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
    fullModN1RemainderWord_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b := by
  have hmods := fullModN1_hmods_v4_of_runtime
    bltu_3 bltu_2 bltu_1 bltu_0 a b a0 a1 a2 a3 b0 b1 b2 b3
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hb1z hb2z hb3z hbnz hshift_nz hcarry2
    hbltu_3 hbltu_2 hbltu_1 hbltu_0
  apply fullModN1RemainderWord_v4_eq_mod_of_toNat_eq
  rw [fullModN1RemainderWord_v4_toNat]
  rw [← hmods.1, ← hmods.2.1, ← hmods.2.2.1, ← hmods.2.2.2]
  simp only [← EvmWord.getLimb_as_getLimbN_0,
    ← EvmWord.getLimb_as_getLimbN_1,
    ← EvmWord.getLimb_as_getLimbN_2,
    ← EvmWord.getLimb_as_getLimbN_3]
  exact EvmWord.val256_eq_toNat (EvmWord.mod a b)

theorem fullModN1RemainderWord_v4_toNat_eq_mod_toNat_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
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
    (fullModN1RemainderWord_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.mod a b).toNat := by
  rw [fullModN1RemainderWord_v4_eq_mod_of_runtime
    bltu_3 bltu_2 bltu_1 bltu_0 a b a0 a1 a2 a3 b0 b1 b2 b3
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hb1z hb2z hb3z hbnz hshift_nz hcarry2
    hbltu_3 hbltu_2 hbltu_1 hbltu_0]

theorem fullModN1_denorm_v4_val256_eq_mod_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
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
    EvmWord.val256
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      (((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      ((fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64)) =
    EvmWord.val256 a0 a1 a2 a3 % EvmWord.val256 b0 b1 b2 b3 := by
  rw [← fullModN1RemainderWord_v4_toNat]
  rw [fullModN1RemainderWord_v4_toNat_eq_mod_toNat_of_runtime
    bltu_3 bltu_2 bltu_1 bltu_0 a b a0 a1 a2 a3 b0 b1 b2 b3
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hb1z hb2z hb3z hbnz hshift_nz hcarry2
    hbltu_3 hbltu_2 hbltu_1 hbltu_0]
  have ha_val : EvmWord.val256 a0 a1 a2 a3 = a.toNat := by
    rw [← ha0, ← ha1, ← ha2, ← ha3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : EvmWord.val256 b0 b1 b2 b3 = b.toNat := by
    rw [← hb0, ← hb1, ← hb2, ← hb3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  have hb_pos : 0 < b.toNat := by
    rw [← hb_val]
    exact EvmWord.val256_pos_of_or_ne_zero hbnz
  have hb_ne : b ≠ 0 := by
    intro hb_zero
    have hb_toNat_zero : b.toNat = 0 := by simp [hb_zero]
    omega
  have hmod_toNat : (EvmWord.mod a b).toNat = a.toNat % b.toNat := by
    unfold EvmWord.mod
    rw [if_neg hb_ne]
    exact BitVec.toNat_umod
  rw [hmod_toNat, ← ha_val, ← hb_val]

end EvmAsm.Evm64
