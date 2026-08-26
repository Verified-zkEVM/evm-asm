/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackV5

  V5 mirror of the n=4 call+addback-BEQ dispatcher predicate family.

  These are the V5 analogs of the predicates in
  `EvmAsm.Evm64.DivMod.Spec.CallAddback`: identical in structure, but
  referencing the repaired trial quotient `div128Quot_v5` (and the V5 trial
  call quotient `divKTrialCallV5QHat`) instead of the buggy `div128Quot_v4`.

  All version-agnostic helpers (shift/antishift, the B'/U normalized limbs,
  `n4CallAddbackBeqQTrue`, `mulsubN4`, `addbackN4_carry`, `iterWithDoubleAddback`,
  `val256`) are REUSED from `CallAddback` / the loop-def modules and are NOT
  redefined here.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallAddback
public import EvmAsm.Evm64.DivMod.LoopBody.TrialCallV5

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- V5 call+addback BEQ trial quotient
-- ============================================================================

/-- Trial quotient used by the n=4 v5 call+addback-BEQ semantic marker. -/
def n4CallAddbackBeqQHatV5 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  div128Quot_v5 u4 u3 b3'

theorem n4CallAddbackBeqQHatV5_unfold {a b : EvmWord} :
    n4CallAddbackBeqQHatV5 a b =
      (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
       let antiShift :=
         (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
       let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
       let u4 := (a.getLimbN 3) >>> antiShift
       let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
       div128Quot_v5 u4 u3 b3') :=
  rfl

theorem n4CallAddbackBeqQHatV5_eq_normalized {a b : EvmWord} :
    n4CallAddbackBeqQHatV5 a b =
      div128Quot_v5
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b) :=
  rfl

theorem n4CallAddbackBeqQHatV5_eq_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqQHatV5 a b =
      div128Quot_v5
        ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
        (((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)))
        (((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))) := by
  rw [n4CallAddbackBeqQHatV5_eq_normalized]
  rw [n4CallAddbackBeqU4_eq_direct hshift_nz]
  rw [n4CallAddbackBeqU3_eq_direct hshift_nz]
  rw [n4CallAddbackBeqB3Prime_eq_direct hshift_nz]

-- ============================================================================
-- V5 first addback carry
-- ============================================================================

/-- First addback carry used by the n=4 v5 call+addback-BEQ semantic marker. -/
def n4CallAddbackBeqCarryV5 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let qHat := n4CallAddbackBeqQHatV5 a b
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'

theorem n4CallAddbackBeqCarryV5_unfold {a b : EvmWord} :
    n4CallAddbackBeqCarryV5 a b =
      (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
       let antiShift :=
         (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
       let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
       let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
       let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
       let b0' := (b.getLimbN 0) <<< shift
       let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
       let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
       let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
       let u0 := (a.getLimbN 0) <<< shift
       let qHat := n4CallAddbackBeqQHatV5 a b
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3') :=
  rfl

theorem n4CallAddbackBeqCarryV5_eq_normalized {a b : EvmWord} :
    n4CallAddbackBeqCarryV5 a b =
      (let qHat := n4CallAddbackBeqQHatV5 a b
       let ms := mulsubN4 qHat
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b)
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b)
       addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b)) :=
  rfl

theorem n4CallAddbackBeqCarryV5_eq_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqCarryV5 a b =
      (let b3' :=
        ((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b2' :=
        ((b.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b1' :=
        ((b.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b0' := (b.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let u3 :=
        ((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u2 :=
        ((a.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u1 :=
        ((a.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u0 := (a.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let qHat :=
        div128Quot_v5
          ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
          u3
          b3'
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3') := by
  rw [n4CallAddbackBeqCarryV5_eq_normalized]
  rw [n4CallAddbackBeqQHatV5_eq_direct hshift_nz]
  rw [n4CallAddbackBeqB0Prime_eq_direct hshift_nz]
  rw [n4CallAddbackBeqB1Prime_eq_direct hshift_nz]
  rw [n4CallAddbackBeqB2Prime_eq_direct hshift_nz]
  rw [n4CallAddbackBeqB3Prime_eq_direct hshift_nz]
  rw [n4CallAddbackBeqU0_eq_direct hshift_nz]
  rw [n4CallAddbackBeqU1_eq_direct hshift_nz]
  rw [n4CallAddbackBeqU2_eq_direct hshift_nz]
  rw [n4CallAddbackBeqU3_eq_direct hshift_nz]

-- ============================================================================
-- V5 corrected quotient
-- ============================================================================

/-- Corrected quotient produced by the n=4 v5 call+addback-BEQ semantic marker. -/
def n4CallAddbackBeqQOutV5 (a b : EvmWord) : Word :=
  let qHat := n4CallAddbackBeqQHatV5 a b
  let carry := n4CallAddbackBeqCarryV5 a b
  if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
  else qHat + signExtend12 4095

theorem n4CallAddbackBeqQOutV5_unfold {a b : EvmWord} :
    n4CallAddbackBeqQOutV5 a b =
      (let qHat := n4CallAddbackBeqQHatV5 a b
       let carry := n4CallAddbackBeqCarryV5 a b
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095) :=
  rfl

theorem n4CallAddbackBeqQOutV5_raw_unfold {a b : EvmWord} :
    n4CallAddbackBeqQOutV5 a b =
      (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
       let antiShift :=
         (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
       let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
       let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
       let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
       let b0' := (b.getLimbN 0) <<< shift
       let u4 := (a.getLimbN 3) >>> antiShift
       let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
       let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
       let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
       let u0 := (a.getLimbN 0) <<< shift
       let qHat := div128Quot_v5 u4 u3 b3'
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095) :=
  rfl

theorem n4CallAddbackBeqQOutV5_eq_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqQOutV5 a b =
      (let b3' :=
        ((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b2' :=
        ((b.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b1' :=
        ((b.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b0' := (b.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let u3 :=
        ((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u2 :=
        ((a.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u1 :=
        ((a.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u0 := (a.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let qHat :=
        div128Quot_v5
          ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
          u3
          b3'
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095) := by
  rw [n4CallAddbackBeqQOutV5_unfold]
  rw [n4CallAddbackBeqQHatV5_eq_direct hshift_nz]
  rw [n4CallAddbackBeqCarryV5_eq_direct hshift_nz]

/-- On the addback branch, the loop iterator's quotient output agrees with the
    v5 call+addback-BEQ marker quotient. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_qOutV5_of_borrow {a b : EvmWord}
    (h_borrow :
      BitVec.ult (n4CallAddbackBeqU4 a b)
        (mulsubN4
          (n4CallAddbackBeqQHatV5 a b)
          (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b)
          (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b)).2.2.2.2) :
    (iterWithDoubleAddback
      (n4CallAddbackBeqQHatV5 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b)).1 =
      n4CallAddbackBeqQOutV5 a b := by
  have h_iter := iterWithDoubleAddback_borrow h_borrow
  have h_fst := congrArg Prod.fst h_iter
  have h_carry_eq := n4CallAddbackBeqCarryV5_eq_normalized (a := a) (b := b)
  by_cases h_carry : n4CallAddbackBeqCarryV5 a b = 0
  · rw [← h_carry_eq] at h_fst
    rw [if_pos h_carry] at h_fst
    rw [n4CallAddbackBeqQOutV5_unfold, h_carry]
    exact h_fst
  · have h_carry_norm : ¬
        (let qHat := n4CallAddbackBeqQHatV5 a b
         let ms := mulsubN4 qHat
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
         addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)) = 0 := by
      intro h_norm
      exact h_carry (h_carry_eq.trans h_norm)
    rw [if_neg h_carry_norm] at h_fst
    rw [n4CallAddbackBeqQOutV5_unfold, if_neg h_carry]
    exact h_fst

/-- The zero-carry call+addback-BEQ case decrements the trial quotient twice. -/
theorem n4CallAddbackBeqQOutV5_of_carry_eq_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b = 0) :
    n4CallAddbackBeqQOutV5 a b =
      n4CallAddbackBeqQHatV5 a b + signExtend12 4095 + signExtend12 4095 := by
  simp [n4CallAddbackBeqQOutV5, h_carry]

/-- The nonzero-carry call+addback-BEQ case decrements the trial quotient once. -/
theorem n4CallAddbackBeqQOutV5_of_carry_ne_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b ≠ 0) :
    n4CallAddbackBeqQOutV5 a b =
      n4CallAddbackBeqQHatV5 a b + signExtend12 4095 := by
  rw [n4CallAddbackBeqQOutV5]
  rw [if_neg h_carry]

/-- `toNat` form of the zero-carry double-decrement qOut case. -/
theorem n4CallAddbackBeqQOutV5_toNat_of_carry_eq_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b = 0) :
    (n4CallAddbackBeqQOutV5 a b).toNat =
      (n4CallAddbackBeqQHatV5 a b + signExtend12 4095 + signExtend12 4095).toNat := by
  rw [n4CallAddbackBeqQOutV5_of_carry_eq_zero h_carry]

/-- `toNat` form of the nonzero-carry single-decrement qOut case. -/
theorem n4CallAddbackBeqQOutV5_toNat_of_carry_ne_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b ≠ 0) :
    (n4CallAddbackBeqQOutV5 a b).toNat =
      (n4CallAddbackBeqQHatV5 a b + signExtend12 4095).toNat := by
  rw [n4CallAddbackBeqQOutV5_of_carry_ne_zero h_carry]

-- ============================================================================
-- V5 carry-selected qHat equality vs. qTrue
-- ============================================================================

/-- Carry-selected qHat equality targeted by the v5 n=4 call+addback-BEQ marker. -/
def n4CallAddbackBeqQHatBranchEqQTrueV5 (a b : EvmWord) : Prop :=
  if n4CallAddbackBeqCarryV5 a b = 0 then
    (n4CallAddbackBeqQHatV5 a b + signExtend12 4095 + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b
  else
    (n4CallAddbackBeqQHatV5 a b + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b

theorem n4CallAddbackBeqQHatBranchEqQTrueV5_unfold {a b : EvmWord} :
    n4CallAddbackBeqQHatBranchEqQTrueV5 a b =
      if n4CallAddbackBeqCarryV5 a b = 0 then
        (n4CallAddbackBeqQHatV5 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV5 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b :=
  rfl

theorem n4CallAddbackBeqQHatBranchEqQTrueV5_carry_eq_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b = 0) :
    n4CallAddbackBeqQHatBranchEqQTrueV5 a b ↔
      (n4CallAddbackBeqQHatV5 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQHatBranchEqQTrueV5, if_pos h_carry]

theorem n4CallAddbackBeqQHatBranchEqQTrueV5_carry_ne_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b ≠ 0) :
    n4CallAddbackBeqQHatBranchEqQTrueV5 a b ↔
      (n4CallAddbackBeqQHatV5 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQHatBranchEqQTrueV5, if_neg h_carry]

theorem n4CallAddbackBeqQHatBranchEqQTrueV5_of_carry_eq_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b = 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV5 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqQHatBranchEqQTrueV5 a b :=
  (n4CallAddbackBeqQHatBranchEqQTrueV5_carry_eq_zero_iff h_carry).2 h_qHat

theorem n4CallAddbackBeqQHatBranchEqQTrueV5_carry_eq_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b = 0)
    (h_qHat : n4CallAddbackBeqQHatBranchEqQTrueV5 a b) :
    (n4CallAddbackBeqQHatV5 a b + signExtend12 4095 + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQHatBranchEqQTrueV5_carry_eq_zero_iff h_carry).1 h_qHat

theorem n4CallAddbackBeqQHatBranchEqQTrueV5_of_carry_ne_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b ≠ 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV5 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqQHatBranchEqQTrueV5 a b :=
  (n4CallAddbackBeqQHatBranchEqQTrueV5_carry_ne_zero_iff h_carry).2 h_qHat

theorem n4CallAddbackBeqQHatBranchEqQTrueV5_carry_ne_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b ≠ 0)
    (h_qHat : n4CallAddbackBeqQHatBranchEqQTrueV5 a b) :
    (n4CallAddbackBeqQHatV5 a b + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQHatBranchEqQTrueV5_carry_ne_zero_iff h_carry).1 h_qHat

theorem n4CallAddbackBeqQOutV5_toNat_eq_qTrue_carry_eq_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b = 0) :
    (n4CallAddbackBeqQOutV5 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      (n4CallAddbackBeqQHatV5 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQOutV5_toNat_of_carry_eq_zero h_carry]

theorem n4CallAddbackBeqQOutV5_toNat_eq_qTrue_carry_ne_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV5 a b ≠ 0) :
    (n4CallAddbackBeqQOutV5 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      (n4CallAddbackBeqQHatV5 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQOutV5_toNat_of_carry_ne_zero h_carry]

theorem n4CallAddbackBeqQOutV5_toNat_eq_qTrue_qHat_branch_iff {a b : EvmWord} :
    (n4CallAddbackBeqQOutV5 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      if n4CallAddbackBeqCarryV5 a b = 0 then
        (n4CallAddbackBeqQHatV5 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV5 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b := by
  by_cases h_carry : n4CallAddbackBeqCarryV5 a b = 0
  · rw [if_pos h_carry]
    exact n4CallAddbackBeqQOutV5_toNat_eq_qTrue_carry_eq_zero_iff h_carry
  · rw [if_neg h_carry]
    exact n4CallAddbackBeqQOutV5_toNat_eq_qTrue_carry_ne_zero_iff h_carry

/-- Introduce `qOut = qTrue` from the carry-selected qHat equality. -/
theorem n4CallAddbackBeqQOutV5_toNat_eq_qTrue_of_qHat_branch {a b : EvmWord}
    (h_qHat :
      if n4CallAddbackBeqCarryV5 a b = 0 then
        (n4CallAddbackBeqQHatV5 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV5 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b) :
    (n4CallAddbackBeqQOutV5 a b).toNat = n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQOutV5_toNat_eq_qTrue_qHat_branch_iff).2 h_qHat

/-- Eliminate `qOut = qTrue` to the carry-selected qHat equality. -/
theorem n4CallAddbackBeqQOutV5_toNat_eq_qTrue_qHat_branch {a b : EvmWord}
    (h_qOut : (n4CallAddbackBeqQOutV5 a b).toNat = n4CallAddbackBeqQTrue a b) :
    if n4CallAddbackBeqCarryV5 a b = 0 then
      (n4CallAddbackBeqQHatV5 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b
    else
      (n4CallAddbackBeqQHatV5 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQOutV5_toNat_eq_qTrue_qHat_branch_iff).1 h_qOut

theorem n4CallAddbackBeqQOutV5_toNat_eq_qTrue_qHatBranchEqQTrue_iff {a b : EvmWord} :
    (n4CallAddbackBeqQOutV5 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      n4CallAddbackBeqQHatBranchEqQTrueV5 a b := by
  exact n4CallAddbackBeqQOutV5_toNat_eq_qTrue_qHat_branch_iff

/-- Introduce `qOut = qTrue` from the named carry-selected qHat predicate. -/
theorem n4CallAddbackBeqQOutV5_toNat_eq_qTrue_of_qHatBranchEqQTrue {a b : EvmWord}
    (h_qHat : n4CallAddbackBeqQHatBranchEqQTrueV5 a b) :
    (n4CallAddbackBeqQOutV5 a b).toNat = n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQOutV5_toNat_eq_qTrue_qHatBranchEqQTrue_iff).2 h_qHat

/-- Eliminate `qOut = qTrue` to the named carry-selected qHat predicate. -/
theorem n4CallAddbackBeqQOutV5_toNat_eq_qTrue_qHatBranchEqQTrue {a b : EvmWord}
    (h_qOut : (n4CallAddbackBeqQOutV5 a b).toNat = n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqQHatBranchEqQTrueV5 a b :=
  (n4CallAddbackBeqQOutV5_toNat_eq_qTrue_qHatBranchEqQTrue_iff).1 h_qOut

-- ============================================================================
-- V5 semantic-correctness predicate
-- ============================================================================

/-- V5 semantic-correctness precondition for the n=4 call+addback-BEQ sub-path:
    the final corrected quotient `q_out` (under the repaired `div128Quot_v5`
    trial quotient) equals `⌊val256(a)/val256(b)⌋`. -/
def n4CallAddbackBeqSemanticHoldsV5 (a b : EvmWord) : Prop :=
  (n4CallAddbackBeqQOutV5 a b).toNat = n4CallAddbackBeqQTrue a b

theorem n4CallAddbackBeqSemanticV5_unfold {a b : EvmWord} :
    n4CallAddbackBeqSemanticHoldsV5 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let qHat := div128Quot_v5 u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     let q_out : Word :=
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095
     q_out.toNat =
         val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
           val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl

-- ============================================================================
-- V5 raw-limb / EvmWord runtime-condition predicates
-- ============================================================================

/-- v5 call-addback borrow condition after n=4 pre-loop normalization. -/
@[irreducible]
def loopBodyN4CallAddbackBorrowV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := divKTrialCallV5QHat uTop u3 v3
  let c3 := mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3
  (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word)

/-- v5 call-addback carry2 condition after n=4 pre-loop normalization. -/
@[irreducible]
def loopBodyN4CallAddbackCarry2NzV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := divKTrialCallV5QHat uTop u3 v3
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
  carry = 0 →
    addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0

/-- v5 call-addback borrow condition over raw limbs (after CLZ normalization). -/
@[irreducible]
def isAddbackBorrowN4CallV5Ab (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  loopBodyN4CallAddbackBorrowV5 b0' b1' b2' b3' u0 u1 u2 u3 u4

/-- v5 call-addback carry2 condition over raw limbs (after CLZ normalization). -/
@[irreducible]
def isAddbackCarry2NzN4CallV5Ab (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  loopBodyN4CallAddbackCarry2NzV5 b0' b1' b2' b3' u0 u1 u2 u3 u4

/-- Call trial condition at n=4 v5 call path in EvmWord form (version-agnostic
    `isCallTrialN4` wrapper; mirrors `isCallTrialN4Evm`). -/
def isCallTrialN4V5Evm (a b : EvmWord) : Prop :=
  isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)

theorem isCallTrialN4V5Evm_def {a b : EvmWord} :
    isCallTrialN4V5Evm a b =
    isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- Addback-needed condition at n=4 v5 call path in EvmWord form. -/
def isAddbackBorrowN4CallV5Evm (a b : EvmWord) : Prop :=
  isAddbackBorrowN4CallV5Ab (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- Carry-2-non-zero condition at n=4 v5 call path in EvmWord form. -/
def isAddbackCarry2NzN4CallV5Evm (a b : EvmWord) : Prop :=
  isAddbackCarry2NzN4CallV5Ab (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                              (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackBorrowN4CallV5Evm_def {a b : EvmWord} :
    isAddbackBorrowN4CallV5Evm a b =
    isAddbackBorrowN4CallV5Ab (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                              (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

theorem isAddbackCarry2NzN4CallV5Evm_def {a b : EvmWord} :
    isAddbackCarry2NzN4CallV5Evm a b =
    isAddbackCarry2NzN4CallV5Ab (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                                (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

end EvmAsm.Evm64
