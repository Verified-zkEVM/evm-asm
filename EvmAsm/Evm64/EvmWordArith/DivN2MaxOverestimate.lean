/-
  EvmAsm.Evm64.EvmWordArith.DivN2MaxOverestimate

  Max-path local quotient overestimate bound for the n=2 outer-loop iteration.

  In Knuth's Algorithm D, when the divisor has exactly two (pre-normalisation)
  significant limbs (b3 = 0, b2 = 0, b1 ≠ 0) and the leading-zero shift is
  applied so the normalised v has v1 ≥ 2^63 (top bit set), the high limbs
  of the normalised v are zero: v2 = 0, v3 = 0.

  At the j=2 outer-loop iteration the dividend window is
  (u0, u1, u2, 0, uTop=0) and the MAX trial qHat = 2^64 - 1 is taken when the
  carry-in u2 is at least v1.  This file proves that the true local quotient
  is then within 2 of qHat — exactly the `+2` slack the generic double-addback
  progress bridge `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero`
  needs.

  The arithmetic core is `max_trial_local_overestimate_n2_of_not_ult`; the
  application to `isAddbackCarry2NzN2Max` is the N1-style `_of_not_ult_…`
  bridge below.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Core Nat-level inequality: `(B - 3) * (V0 + V1 * B) ≤ U0 + U1 * B + U2 * (B * B)`
    when `V0 < B`, `2 * 2^63 = B`, `2^63 ≤ V1`, and `V1 ≤ U2`. -/
private theorem core_overestimate_step
    (B V0 V1 U0 U1 U2 : Nat)
    (hBhalf : 2^63 + 2^63 = B)
    (hV0_lt : V0 < B)
    (hV1_msb : 2^63 ≤ V1)
    (hle : V1 ≤ U2) :
    (B - 3) * (V0 + V1 * B) ≤ U0 + U1 * B + U2 * (B * B) := by
  -- 2^63 ≤ V1 ⟹ B ≤ 2 * V1, so B*B ≤ 2*V1*B.
  have hB_le : B ≤ 2 * V1 := by
    have h := Nat.mul_le_mul_left 2 hV1_msb
    have : (2:Nat) * 2^63 = 2^63 + 2^63 := by ring
    omega
  have hB_ge3 : 3 ≤ B := by
    have h63ge : 3 ≤ 2^63 := by
      have h : (2:Nat)^63 ≥ 8 := by
        calc (2:Nat)^63 = 2^60 * 2^3 := by ring
          _ ≥ 1 * 2^3 := by
            have : (1:Nat) ≤ 2^60 := Nat.one_le_pow _ _ (by norm_num)
            exact Nat.mul_le_mul_right _ this
          _ = 8 := by norm_num
      omega
    omega
  -- Step 1: U2 ≥ V1 ⟹ V1 * (B*B) ≤ U.
  have hu_ge : V1 * (B * B) ≤ U0 + U1 * B + U2 * (B * B) := by
    have hmul : V1 * (B * B) ≤ U2 * (B * B) := Nat.mul_le_mul_right _ hle
    have hU0_nn : 0 ≤ U0 := Nat.zero_le _
    have hU1B_nn : 0 ≤ U1 * B := Nat.zero_le _
    linarith
  -- Step 2: (B - 3) * V0 ≤ B * B.
  have hbound_v0 : (B - 3) * V0 ≤ B * B := by
    have h1 : (B - 3) * V0 ≤ B * V0 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have h2 : B * V0 ≤ B * B := Nat.mul_le_mul_left _ (le_of_lt hV0_lt)
    linarith
  -- Step 3: 3 * V1 ≥ 2^63 + B (since V1 ≥ 2^63 and 2 * 2^63 = B).
  have h3V1_ge : 3 * V1 ≥ 2^63 + B := by
    have : 3 * 2^63 ≤ 3 * V1 := Nat.mul_le_mul_left 3 hV1_msb
    have h3_split : 3 * (2:Nat)^63 = 2^63 + (2^63 + 2^63) := by ring
    omega
  -- Step 4: 3 * V1 * B ≥ (2^63 + B) * B = 2^63 * B + B*B ≥ B * B.
  have h3V1B_ge : 3 * V1 * B ≥ B * B := by
    have h1 : (2^63 + B) * B ≤ 3 * V1 * B := Nat.mul_le_mul_right _ h3V1_ge
    have h2 : (2^63 + B) * B = 2^63 * B + B * B := by ring
    have h3 : 0 ≤ 2^63 * B := Nat.zero_le _
    linarith
  -- Step 5: Combine. (B - 3) * V0 + (B - 3) * V1 * B = (B - 3) * (V0 + V1 * B).
  have hexpand : (B - 3) * (V0 + V1 * B) =
      (B - 3) * V0 + (B - 3) * V1 * B := by ring
  -- And (B - 3) * V1 * B + 3 * V1 * B = V1 * (B * B).
  have hsplit : (B - 3) * V1 * B + 3 * V1 * B = V1 * (B * B) := by
    have h_add : (B - 3) + 3 = B := by omega
    have hexpand_lhs :
        ((B - 3) + 3) * V1 * B = (B - 3) * V1 * B + 3 * V1 * B := by ring
    have hexpand_rhs : B * V1 * B = V1 * (B * B) := by ring
    have hsubst : ((B - 3) + 3) * V1 * B = B * V1 * B := by rw [h_add]
    linarith
  -- Now: (B - 3) * V0 ≤ B * B ≤ 3 * V1 * B, so
  --   (B - 3) * (V0 + V1 * B) = (B - 3) * V0 + (B - 3) * V1 * B
  --                           ≤ 3 * V1 * B + (B - 3) * V1 * B
  --                           = V1 * (B * B)
  --                           ≤ U.
  have hkey : (B - 3) * V0 ≤ 3 * V1 * B := by linarith
  linarith

/-- General N2 max-path local quotient bound (allowing nonzero `u3`).  If the
    divisor's high two limbs are zero, the second limb `v1` is normalised (top
    bit set), and the carry-in `u2` is at least `v1`, then `2^64 - 1` is within
    the local quotient plus the double-addback slack of `+2`. -/
theorem max_trial_local_overestimate_n2_of_not_ult_general
    (v0 v1 u0 u1 u2 u3 : Word)
    (hv1_msb : 2^63 ≤ v1.toNat)
    (hbltu : ¬ BitVec.ult u2 v1) :
    (signExtend12 (4095 : BitVec 12) : Word).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 0 0 + 2 := by
  rw [signExtend12_4095_toNat]
  rw [EvmWord.val256_zero_upper_2]
  unfold EvmWord.val256
  -- Powers of two; folded back through `hB_eq`.
  have hB_eq : (2:Nat)^128 = 2^64 * 2^64 := by ring
  have hBhalf : (2:Nat)^63 + 2^63 = 2^64 := by ring
  have hV1_pos : 0 < v1.toNat := by
    have : (0:Nat) < 2^63 := by positivity
    omega
  have hB_pos : (0:Nat) < 2^64 := by positivity
  have hV0_lt : v0.toNat < 2^64 := v0.isLt
  have hle : v1.toNat ≤ u2.toNat := by
    rw [BitVec.ult_eq_decide] at hbltu
    simp at hbltu
    omega
  have hv_pos : 0 < v0.toNat + v1.toNat * 2^64 := by
    have : 0 < v1.toNat * 2^64 := Nat.mul_pos hV1_pos hB_pos
    omega
  -- Goal after val256 unfolds (LHS sum):
  --   u0 + u1*2^64 + u2*2^128 + u3*2^192.
  -- Step: u/v ≥ (u0+u1*2^64+u2*2^128)/v, and the latter is ≥ 2^64 - 3.
  -- So it suffices to bound the smaller sum.
  set U_lo : Nat := u0.toNat + u1.toNat * 2^64 + u2.toNat * 2^128 with hU_lo
  set U_full : Nat := U_lo + u3.toNat * 2^192 with hU_full
  set V : Nat := v0.toNat + v1.toNat * 2^64 with hV
  have hU_le : U_lo ≤ U_full := by
    show U_lo ≤ U_lo + u3.toNat * 2^192
    have : 0 ≤ u3.toNat * 2^192 := Nat.zero_le _
    linarith
  -- u/v monotone: U_lo/V ≤ U_full/V.
  have hdiv_mono : U_lo / V ≤ U_full / V := Nat.div_le_div_right hU_le
  -- Reduce to (2^64 - 3) * V ≤ U_lo via core_overestimate_step.
  suffices h : (2^64 - 3 : Nat) ≤ U_lo / V by
    have hB_ge3 : (3:Nat) ≤ 2^64 := by norm_num
    show 2^64 - 1 ≤ U_full / V + 2
    omega
  rw [Nat.le_div_iff_mul_le hv_pos]
  show (2^64 - 3 : Nat) * V ≤ U_lo
  show (2^64 - 3 : Nat) * (v0.toNat + v1.toNat * 2^64) ≤
       u0.toNat + u1.toNat * 2^64 + u2.toNat * 2^128
  rw [hB_eq]
  exact core_overestimate_step (2^64) v0.toNat v1.toNat u0.toNat u1.toNat u2.toNat
    hBhalf hV0_lt hv1_msb hle

/-- N2 max-path local quotient bound (j=2 specialisation with `u3 = 0`).

    Concrete math: with `v = v0 + v1·2^64` and `u = u0 + u1·2^64 + u2·2^128`,
    we show `u / v + 2 ≥ 2^64 − 1` whenever `v1 ≥ 2^63` and `u2 ≥ v1`.  The
    bound is tight at `v0 = 2^64 − 1`, `v1 = 2^63`, `u0 = u1 = 0`, `u2 = v1`,
    where `u / v = 2^64 − 2`. -/
theorem max_trial_local_overestimate_n2_of_not_ult
    (v0 v1 u0 u1 u2 : Word)
    (hv1_msb : 2^63 ≤ v1.toNat)
    (hbltu : ¬ BitVec.ult u2 v1) :
    (signExtend12 (4095 : BitVec 12) : Word).toNat ≤
      val256 u0 u1 u2 0 / val256 v0 v1 0 0 + 2 :=
  max_trial_local_overestimate_n2_of_not_ult_general v0 v1 u0 u1 u2 0 hv1_msb hbltu

/-- N2 max-path specialization of the generic double-addback progress bridge.
    With a 2-limb divisor (`v2 = v3 = 0`), `v1` normalised, and the selected
    max-branch condition `¬ BitVec.ult u2 v1`, the remaining local obligation
    is exactly the reachable fact that a zero first-addback carry forces the
    mulsub carry `c3` to be one. -/
theorem isAddbackCarry2NzN2Max_of_not_ult_c3_one_of_carry_zero
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hv1_msb : 2^63 ≤ v1.toNat)
    (hv2z : v2 = 0)
    (hv3z : v3 = 0)
    (hc3_one_of_carry_zero :
      addbackN4_carry
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 = 0 →
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1)
    (hbltu : ¬ BitVec.ult u2 v1) :
    isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold isAddbackCarry2NzN2Max
  apply isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero
  · -- v0 ||| v1 ||| v2 ||| v3 ≠ 0 from v1 ≥ 2^63.
    intro h
    subst v2; subst v3
    have h1 : v0 ||| v1 ||| (0 : Word) = 0 := (BitVec.or_eq_zero_iff.mp h).1
    have h2 : v0 ||| v1 = 0 := (BitVec.or_eq_zero_iff.mp h1).1
    have hv1 : v1 = 0 := (BitVec.or_eq_zero_iff.mp h2).2
    have hv1_zero : v1.toNat = 0 := by rw [hv1]; decide
    have hpos : (0:Nat) < 2^63 := by positivity
    omega
  · subst v2; subst v3
    exact max_trial_local_overestimate_n2_of_not_ult_general v0 v1 u0 u1 u2 u3
      hv1_msb hbltu
  · exact hc3_one_of_carry_zero

end EvmAsm.Evm64
