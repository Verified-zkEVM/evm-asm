/-
  Shared declaration home for the n=1 v5 quotient/no-borrow facts.
-/

import EvmAsm.Evm64.DivMod.Spec.N1CarryZeroReducers
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Defs
import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5DigitBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

open EvmAsm.Rv64

/-- **Abstract v5 single-limb carry-zero.** For a normalized one-limb divisor
    (`v0 ≥ 2^63`) in the call regime (`u1 < v0`), the v5 call-path iteration has
    zero carry. Mirrors `iterN1_true_carry_zero_of_v0_all_phases_no_wrap` but
    with NO `Div128AllPhasesNoWrapInv` — the v5 floor bound is unconditional. -/
theorem iterN1V5_true_carry_zero_of_v0_norm_call
    (v0 u0 u1 : Word)
    (hv0_norm : v0.toNat ≥ 2^63)
    (hcall : u1.toNat < v0.toNat) :
    (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).2.2.2.2.2 = 0 := by
  apply iterN1V5_true_carry_zero_of_mulsub_c3_zero
  · apply c3_un_zero_of_qHat_mul_le
    have hq_le := div128Quot_v5_le_q_true u1 u0 v0 hv0_norm hcall
    have h_product : (div128Quot_v5 u1 u0 v0).toNat * v0.toNat ≤
        u1.toNat * 2^64 + u0.toNat :=
      le_trans (Nat.mul_le_mul_right v0.toNat hq_le) (Nat.div_mul_le_self _ _)
    simp [EvmWord.val256]
    omega
  · rfl

/-- **Abstract v5 single-limb remainder bound.** For a normalized one-limb
    divisor (`v0 ≥ 2^63`) in the call regime (`u1 < v0`), the v5 iteration's
    remainder is `< v0`: the v5 trial is the exact floor, so the no-borrow
    mulsub leaves `remainder = (u1·2^64 + u0) mod v0 < v0`. The per-step
    invariant that propagates the call regime to the next n=1 digit, with NO
    `Div128AllPhasesNoWrapInv`. -/
theorem iterN1V5_true_remainder_lt_of_v0_norm_call
    (v0 u0 u1 : Word)
    (hv0_norm : v0.toNat ≥ 2^63)
    (hcall : u1.toNat < v0.toNat) :
    EvmWord.val256
      (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).2.1
      (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).2.2.1
      (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).2.2.2.1
      (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).2.2.2.2.1 < v0.toNat := by
  have hv0_pos : 0 < v0.toNat := by omega
  have hq_eq := div128Quot_v5_eq_q_true u1 u0 v0 hv0_norm hcall
  have hc3 : (mulsubN4 (div128Quot_v5 u1 u0 v0) v0 0 0 0 u0 u1 0 0).2.2.2.2 = 0 := by
    apply c3_un_zero_of_qHat_mul_le
    have h_prod : (div128Quot_v5 u1 u0 v0).toNat * v0.toNat ≤ u1.toNat * 2^64 + u0.toNat :=
      le_trans (Nat.mul_le_mul_right v0.toNat
        (div128Quot_v5_le_q_true u1 u0 v0 hv0_norm hcall)) (Nat.div_mul_le_self _ _)
    simp [EvmWord.val256]
    omega
  rw [iterN1V5_true]
  unfold iterN1Call_v5
  rw [iterWithDoubleAddback_no_borrow (by rw [hc3]; simp [BitVec.ult])]
  dsimp only
  have hval := mulsubN4_val256_eq (div128Quot_v5 u1 u0 v0) v0 0 0 0 u0 u1 0 0
  simp only [hc3] at hval
  rw [hq_eq] at hval
  simp [EvmWord.val256] at hval ⊢
  -- `simp` evaluated `2^64` to its literal; state the Euclidean facts in the
  -- same literal form so omega sees one `floor * v0` atom.
  have hdm := Nat.div_add_mod' (u1.toNat * 18446744073709551616 + u0.toNat) v0.toNat
  have hlt := Nat.mod_lt (u1.toNat * 18446744073709551616 + u0.toNat) hv0_pos
  omega

/-- **Abstract v5 single-limb quotient extraction.** For a normalized one-limb
    divisor (`v0 ≥ 2^63`) in the call regime (`u1 < v0`), the v5 iteration's
    stored quotient digit is exactly the capped 128/64 trial `div128Quot_v5 u1 u0
    v0`: the no-borrow mulsub (same `c3 = 0` as the remainder bound) keeps the
    trial uncorrected, so the iteration's `.1` is the trial itself. With NO
    `Div128AllPhasesNoWrapInv`. -/
theorem iterN1V5_true_quot_eq_div128_of_v0_norm_call
    (v0 u0 u1 : Word)
    (hv0_norm : v0.toNat ≥ 2^63)
    (hcall : u1.toNat < v0.toNat) :
    (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).1 = div128Quot_v5 u1 u0 v0 := by
  have hc3 : (mulsubN4 (div128Quot_v5 u1 u0 v0) v0 0 0 0 u0 u1 0 0).2.2.2.2 = 0 := by
    apply c3_un_zero_of_qHat_mul_le
    have h_prod : (div128Quot_v5 u1 u0 v0).toNat * v0.toNat ≤ u1.toNat * 2^64 + u0.toNat :=
      le_trans (Nat.mul_le_mul_right v0.toNat
        (div128Quot_v5_le_q_true u1 u0 v0 hv0_norm hcall)) (Nat.div_mul_le_self _ _)
    simp [EvmWord.val256]
    omega
  rw [iterN1V5_true]
  unfold iterN1Call_v5
  rw [iterWithDoubleAddback_no_borrow (by rw [hc3]; simp [BitVec.ult])]

/-- **Abstract v5 single-limb remainder extraction.** Companion of
    `iterN1V5_true_quot_eq_div128_of_v0_norm_call`: under the normalized call
    regime, the iteration's stored remainder limb is `u0 - q·v0` in closed form
    (the single-limb no-borrow mulsub low limb, `un0 = u0 - q·v0`). This matches
    the v6 body's `v6chainR = uLo -₆₄ q·d`. -/
theorem iterN1V5_true_rem_eq_of_v0_norm_call
    (v0 u0 u1 : Word)
    (hv0_norm : v0.toNat ≥ 2^63)
    (hcall : u1.toNat < v0.toNat) :
    (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).2.1 = u0 - div128Quot_v5 u1 u0 v0 * v0 := by
  have hc3 : (mulsubN4 (div128Quot_v5 u1 u0 v0) v0 0 0 0 u0 u1 0 0).2.2.2.2 = 0 := by
    apply c3_un_zero_of_qHat_mul_le
    have h_prod : (div128Quot_v5 u1 u0 v0).toNat * v0.toNat ≤ u1.toNat * 2^64 + u0.toNat :=
      le_trans (Nat.mul_le_mul_right v0.toNat
        (div128Quot_v5_le_q_true u1 u0 v0 hv0_norm hcall)) (Nat.div_mul_le_self _ _)
    simp [EvmWord.val256]
    omega
  rw [iterN1V5_true]
  unfold iterN1Call_v5
  rw [iterWithDoubleAddback_no_borrow (by rw [hc3]; simp [BitVec.ult])]
  show (mulsubN4 (div128Quot_v5 u1 u0 v0) v0 0 0 0 u0 u1 0 0).1 = _
  unfold mulsubN4
  simp only [AddrNorm.se12_0]
  bv_omega

/-- **v5 n=1 first-digit carry-zero, from shape (no `Carry2NzAll`).** -/
theorem fullDivN1R3V5_carry_zero_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2 = 0 := by
  unfold fullDivN1R3V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  exact iterN1V5_true_carry_zero_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

/-- **v5 n=1 first-digit remainder bound, from shape.** `val256` of the
    `fullDivN1R3V5` remainder is `< normV.1` — the per-step invariant that feeds
    the call regime of the R2 digit. From shape (no `Carry2NzAll`). -/
theorem fullDivN1R3V5_remainder_lt_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.val256
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
  unfold fullDivN1R3V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

/-- **v5 n=1 first-digit quotient, from shape.** The `fullDivN1R3V5` stored
    quotient digit equals the capped 128/64 trial `div128Quot_v5` of the
    normalized top window — the digit the v6 body computes (as
    `div128V5CodeQuot`).  From shape (no `Carry2NzAll`). -/
theorem fullDivN1R3V5_quot_eq_div128_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 =
      div128Quot_v5 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
                    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
                    (fullDivN1NormV b0 b1 b2 b3).1 := by
  unfold fullDivN1R3V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  exact iterN1V5_true_quot_eq_div128_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

/-- **v5 n=1 first-digit remainder, from shape.** The `fullDivN1R3V5` stored
    remainder limb equals `uLo - q₃·v0'` in closed form — the form the v6 body
    threads as the next digit's high word (`v6chainR3`).  From shape. -/
theorem fullDivN1R3V5_rem_eq_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1 =
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 -
        div128Quot_v5 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
                      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
                      (fullDivN1NormV b0 b1 b2 b3).1 *
          (fullDivN1NormV b0 b1 b2 b3).1 := by
  unfold fullDivN1R3V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  exact iterN1V5_true_rem_eq_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

open EvmAsm.Rv64

/-- **v5 single-limb no-borrow, from shape.** For a normalized one-limb divisor
    (`v0 ≥ 2^63`) in the call regime (`u1 < v0`), the v5 trial's single-limb
    mulsub leaves no top borrow, for any top accumulator `uTop`.  No
    `Carry2NzAll` / reachability — the exact floor bound forces `c3 = 0`. -/
theorem mulsubN4NoBorrow_div128Quot_v5_of_norm_call
    (v0 u0 u1 uTop : Word)
    (hv0_norm : v0.toNat ≥ 2 ^ 63)
    (hcall : u1.toNat < v0.toNat) :
    mulsubN4NoBorrow (div128Quot_v5 u1 u0 v0) v0 0 0 0 u0 u1 0 0 uTop := by
  have hc3 : (mulsubN4 (div128Quot_v5 u1 u0 v0) v0 0 0 0 u0 u1 0 0).2.2.2.2 = 0 := by
    apply c3_un_zero_of_qHat_mul_le
    have hq_le := div128Quot_v5_le_q_true u1 u0 v0 hv0_norm hcall
    have h_product : (div128Quot_v5 u1 u0 v0).toNat * v0.toNat ≤
        u1.toNat * 2 ^ 64 + u0.toNat :=
      le_trans (Nat.mul_le_mul_right v0.toNat hq_le) (Nat.div_mul_le_self _ _)
    simp [EvmWord.val256]
    omega
  unfold mulsubN4NoBorrow
  rw [hc3]
  simp [BitVec.ult]

open EvmAsm.Rv64

/-- The div128 code quotient equals the trial def `divKTrialCallV5QHat`
    (transitively, via the model `div128Quot_v5`). -/
theorem div128V5CodeQuot_eq_divKTrialCallV5QHat (uHi uLo vTop : Word) :
    div128V5CodeQuot uHi uLo vTop = divKTrialCallV5QHat uHi uLo vTop :=
  (div128V5CodeQuot_eq_div128Quot_v5 uHi uLo vTop).trans
    (divKTrialCallV5QHat_eq_div128Quot_v5 uHi uLo vTop).symm

/-- **No-borrow for the div128 code quotient, from shape.**  For a normalized
    one-limb divisor (`v0 ≥ 2^63`) in the call regime (`u1 < v0`), the code's
    single-limb mulsub with the code trial `div128V5CodeQuot u1 u0 v0` leaves no
    top borrow — the `hborrow` hypothesis the v5 n=1 loop-body skip consumes. -/
theorem mulsubN4NoBorrow_div128V5CodeQuot_of_norm_call
    (v0 u0 u1 uTop : Word)
    (hv0_norm : v0.toNat ≥ 2 ^ 63)
    (hcall : u1.toNat < v0.toNat) :
    mulsubN4NoBorrow (div128V5CodeQuot u1 u0 v0) v0 0 0 0 u0 u1 0 0 uTop := by
  rw [div128V5CodeQuot_eq_div128Quot_v5]
  exact mulsubN4NoBorrow_div128Quot_v5_of_norm_call v0 u0 u1 uTop hv0_norm hcall

end EvmAsm.Evm64
