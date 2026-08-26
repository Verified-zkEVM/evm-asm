/-
  EvmAsm.Evm64.EvmWordArith.DivN3MaxOverestimate

  Max-path local quotient overestimate bound for the n=3 outer-loop iteration.

  In Knuth's Algorithm D, when the divisor has exactly three (pre-normalisation)
  significant limbs (b3 = 0, b2 ≠ 0) and the leading-zero shift is applied so
  the normalised v has v2 ≥ 2^63 (top bit set) and v3 = 0, the MAX trial
  qHat = 2^64 - 1 is taken when the carry-in u3 is at least v2.

  This file provides the val256-level overestimate bound and the application
  bridge to `isAddbackCarry2NzN3Max`, mirroring `DivN2MaxOverestimate`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Core Nat-level inequality for the N3 max-path overestimate:
    `(B - 3) * (V0 + V1*B + V2*B²) ≤ U0 + U1*B + U2*B² + U3*B³`
    when `V0, V1 < B`, `2 * 2^63 = B`, `2^63 ≤ V2`, and `V2 ≤ U3`. -/
private theorem core_overestimate_step_n3
    (B V0 V1 V2 U0 U1 U2 U3 : Nat)
    (hBhalf : 2^63 + 2^63 = B)
    (hV0_lt : V0 < B)
    (hV1_lt : V1 < B)
    (hV2_msb : 2^63 ≤ V2)
    (hle : V2 ≤ U3) :
    (B - 3) * (V0 + V1 * B + V2 * (B * B)) ≤
      U0 + U1 * B + U2 * (B * B) + U3 * (B * B * B) := by
  have hB_ge3 : 3 ≤ B := by
    have h63ge : 3 ≤ (2:Nat)^63 := by
      have h : (2:Nat)^63 ≥ 8 := by
        calc (2:Nat)^63 = 2^60 * 2^3 := by ring
          _ ≥ 1 * 2^3 := by
            have : (1:Nat) ≤ 2^60 := Nat.one_le_pow _ _ (by norm_num)
            exact Nat.mul_le_mul_right _ this
          _ = 8 := by norm_num
      omega
    omega
  -- Step A: V2 * B³ ≤ U.
  have hu_ge : V2 * (B * B * B) ≤
      U0 + U1 * B + U2 * (B * B) + U3 * (B * B * B) := by
    have hmul : V2 * (B * B * B) ≤ U3 * (B * B * B) :=
      Nat.mul_le_mul_right _ hle
    have hU0_nn : 0 ≤ U0 := Nat.zero_le _
    have hU1B_nn : 0 ≤ U1 * B := Nat.zero_le _
    have hU2B2_nn : 0 ≤ U2 * (B * B) := Nat.zero_le _
    linarith
  -- Step B: (B - 3) * V0 ≤ B * B, (B - 3) * V1 * B ≤ B * B * B
  -- Together: (B-3) * V0 + (B-3) * V1 * B ≤ B * B + B³.
  -- We don't need that exact form; just bound (B-3)*(V0 + V1*B) ≤ 2*B³.
  have hbound_low : (B - 3) * (V0 + V1 * B) ≤ B * B + B * B * B := by
    have h0 : (B - 3) * V0 ≤ B * B := by
      have h1 : (B - 3) * V0 ≤ B * V0 :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have h2 : B * V0 ≤ B * B := Nat.mul_le_mul_left _ (le_of_lt hV0_lt)
      linarith
    have h1' : (B - 3) * V1 ≤ B * B := by
      have h1 : (B - 3) * V1 ≤ B * V1 :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have h2 : B * V1 ≤ B * B := Nat.mul_le_mul_left _ (le_of_lt hV1_lt)
      linarith
    have h_expand : (B - 3) * (V0 + V1 * B) = (B - 3) * V0 + (B - 3) * V1 * B := by
      ring
    -- (B - 3) * V1 * B ≤ B * B * B (since (B-3)*V1 ≤ B*B)
    have h_mul_B : (B - 3) * V1 * B ≤ B * B * B := by
      have h1 : (B - 3) * V1 * B = ((B - 3) * V1) * B := by ring
      have h2 : ((B - 3) * V1) * B ≤ (B * B) * B := Nat.mul_le_mul_right _ h1'
      linarith
    linarith
  -- Step C: 3 * V2 * B² ≥ B * B + B³  (the slack to close the gap).
  -- Reason: V2 ≥ 2^63 = B/2, so 3 * V2 ≥ 2^63 + B (from 3 = 1 + 2).
  -- Then 3 * V2 * B² ≥ (2^63 + B) * B² = 2^63 * B² + B³ ≥ B² + B³ (loose).
  have h3V2_ge : 3 * V2 ≥ 2^63 + B := by
    have : 3 * 2^63 ≤ 3 * V2 := Nat.mul_le_mul_left 3 hV2_msb
    have h3_split : 3 * (2:Nat)^63 = 2^63 + (2^63 + 2^63) := by ring
    omega
  have h3V2B2_ge : 3 * V2 * (B * B) ≥ B * B + B * B * B := by
    have h1 : (2^63 + B) * (B * B) ≤ 3 * V2 * (B * B) :=
      Nat.mul_le_mul_right _ h3V2_ge
    have h2 : (2^63 + B) * (B * B) = 2^63 * (B * B) + B * (B * B) := by ring
    -- 2^63 * (B * B) ≥ B * B  iff  2^63 ≥ 1.
    have h63ge1 : 1 ≤ (2:Nat)^63 := Nat.one_le_pow _ _ (by norm_num)
    have h_pow_ge : B * B ≤ 2^63 * (B * B) := by
      have h : 1 * (B * B) ≤ 2^63 * (B * B) :=
        Nat.mul_le_mul_right _ h63ge1
      linarith
    have h_eq : B * (B * B) = B * B * B := by ring
    linarith
  -- Step D: Combine. (B-3) * (V0 + V1*B + V2*B²)
  -- = (B-3)*(V0 + V1*B) + (B-3) * V2 * B²
  -- (B-3) * V2 * B² + 3 * V2 * B² = B * V2 * B² = V2 * B³
  have hsplit : (B - 3) * V2 * (B * B) + 3 * V2 * (B * B) =
      V2 * (B * B * B) := by
    have h_add : (B - 3) + 3 = B := by omega
    have h_lhs : ((B - 3) + 3) * V2 * (B * B) =
        (B - 3) * V2 * (B * B) + 3 * V2 * (B * B) := by ring
    have h_rhs : B * V2 * (B * B) = V2 * (B * B * B) := by ring
    have h_sub : ((B - 3) + 3) * V2 * (B * B) = B * V2 * (B * B) := by rw [h_add]
    linarith
  have hexp : (B - 3) * (V0 + V1 * B + V2 * (B * B)) =
      (B - 3) * (V0 + V1 * B) + (B - 3) * V2 * (B * B) := by ring
  -- Final chain:
  --   LHS = (B-3) * (V0 + V1*B) + (B-3) * V2 * B²
  --       ≤ (B*B + B*B*B) + (B-3) * V2 * B²                    [hbound_low]
  --       ≤ 3 * V2 * B² + (B-3) * V2 * B²                       [h3V2B2_ge]
  --       = V2 * B³                                             [hsplit]
  --       ≤ U                                                   [hu_ge]
  linarith

/-- N3 max-path local quotient bound.  If the divisor's top limb is zero, the
    third limb `v2` is normalised (top bit set), and the carry-in `u3` is at
    least `v2`, then `2^64 - 1` is within the local quotient plus the
    double-addback slack of `+2`. -/
theorem max_trial_local_overestimate_n3_of_not_ult
    (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2_msb : 2^63 ≤ v2.toNat)
    (hbltu : ¬ BitVec.ult u3 v2) :
    (signExtend12 (4095 : BitVec 12) : Word).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 0 + 2 := by
  rw [signExtend12_4095_toNat]
  unfold EvmWord.val256
  -- Powers of two; folded back through `hB_eq`.
  have hB_eq128 : (2:Nat)^128 = 2^64 * 2^64 := by ring
  have hB_eq192 : (2:Nat)^192 = 2^64 * 2^64 * 2^64 := by ring
  have hBhalf : (2:Nat)^63 + 2^63 = 2^64 := by ring
  have hV2_pos : 0 < v2.toNat := by
    have : (0:Nat) < 2^63 := by positivity
    omega
  have hB_pos : (0:Nat) < 2^64 := by positivity
  have hV0_lt : v0.toNat < 2^64 := v0.isLt
  have hV1_lt : v1.toNat < 2^64 := v1.isLt
  have hle : v2.toNat ≤ u3.toNat := by
    rw [BitVec.ult_eq_decide] at hbltu
    simp at hbltu
    omega
  have hv_pos : 0 < v0.toNat + v1.toNat * 2^64 + v2.toNat * 2^128 + 0 * 2^192 := by
    have h2 : 0 < v2.toNat * 2^128 := by
      have : (0:Nat) < 2^128 := by positivity
      exact Nat.mul_pos hV2_pos this
    omega
  -- After unfold, divisor side has `0 * 2^192`. Drop it.
  show (2:Nat)^64 - 1 ≤
       (u0.toNat + u1.toNat * 2^64 + u2.toNat * 2^128 + u3.toNat * 2^192) /
       (v0.toNat + v1.toNat * 2^64 + v2.toNat * 2^128 + (0:Word).toNat * 2^192) + 2
  have hzero : ((0 : Word).toNat * 2^192 : Nat) = 0 := by decide
  rw [hzero]
  -- Reduce goal: 2^64-1 ≤ u/(v0+v1*B+v2*B²) + 2, i.e., 2^64-3 ≤ u/v.
  suffices h : (2^64 - 3 : Nat) ≤
      (u0.toNat + u1.toNat * 2^64 + u2.toNat * 2^128 + u3.toNat * 2^192) /
      (v0.toNat + v1.toNat * 2^64 + v2.toNat * 2^128 + 0) by
    have hB_ge3 : (3:Nat) ≤ 2^64 := by norm_num
    omega
  have hv_pos' : 0 < v0.toNat + v1.toNat * 2^64 + v2.toNat * 2^128 + 0 := by
    omega
  rw [Nat.le_div_iff_mul_le hv_pos']
  rw [hB_eq128, hB_eq192]
  show (2^64 - 3 : Nat) * (v0.toNat + v1.toNat * 2^64 +
        v2.toNat * (2^64 * 2^64) + 0) ≤
       u0.toNat + u1.toNat * 2^64 + u2.toNat * (2^64 * 2^64) +
        u3.toNat * (2^64 * 2^64 * 2^64)
  have h_drop_zero :
      (2^64 - 3 : Nat) * (v0.toNat + v1.toNat * 2^64 +
        v2.toNat * (2^64 * 2^64) + 0) =
      (2^64 - 3) * (v0.toNat + v1.toNat * 2^64 + v2.toNat * (2^64 * 2^64)) := by
    ring
  rw [h_drop_zero]
  exact core_overestimate_step_n3 (2^64) v0.toNat v1.toNat v2.toNat
    u0.toNat u1.toNat u2.toNat u3.toNat
    hBhalf hV0_lt hV1_lt hv2_msb hle

/-- N3 max-path specialization of the generic double-addback progress bridge.
    With a 3-limb divisor (`v3 = 0`), `v2` normalised (top bit set), and the
    selected max-branch condition `¬ BitVec.ult u3 v2`, the remaining local
    obligation is exactly the reachable fact that a zero first-addback carry
    forces the mulsub carry `c3` to be one. -/
theorem isAddbackCarry2NzN3Max_of_not_ult_c3_one_of_carry_zero
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hv2_msb : 2^63 ≤ v2.toNat)
    (hv3z : v3 = 0)
    (hc3_one_of_carry_zero :
      addbackN4_carry
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 = 0 →
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1)
    (hbltu : ¬ BitVec.ult u3 v2) :
    isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold isAddbackCarry2NzN3Max
  apply isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero
  · -- v0 ||| v1 ||| v2 ||| v3 ≠ 0 from v2 ≥ 2^63.
    intro h
    subst v3
    have h1 : v0 ||| v1 ||| v2 = 0 := (BitVec.or_eq_zero_iff.mp h).1
    have hv2 : v2 = 0 := (BitVec.or_eq_zero_iff.mp h1).2
    have hv2_zero : v2.toNat = 0 := by rw [hv2]; decide
    have hpos : (0:Nat) < 2^63 := by positivity
    omega
  · subst v3
    exact max_trial_local_overestimate_n3_of_not_ult v0 v1 v2 u0 u1 u2 u3
      hv2_msb hbltu
  · exact hc3_one_of_carry_zero

end EvmAsm.Evm64
