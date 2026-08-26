/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.NoWrapChainDHiPow32

  Wider-premise no-wrap chain on the V4 Knuth-A `+1` upper-bound path.

  Composes PR #7059's `divKTrialCallV4Q1dd_eq_q_true_1_of_uHi_lt_dHi_pow32`
  and PR #7060's wider Q0dd UB / +1-floor-bound to land:

    * `divKTrialCallV4Un21_eq_r1_of_no_wrap_of_uHi_lt_dHi_pow32` — derives
      `un21 = r1` from the Phase-1b no-wrap inequality, under the wider
      `uHi < dHi * 2^32` premise (in place of `uHi < 2^63`).

    * `div128Quot_v4_le_q_true_plus_one_of_no_wrap_of_uHi_lt_dHi_pow32` —
      end-to-end `+1` floor bound on `div128Quot_v4` given the no-wrap
      inequality plus a wider `un21 < dHi*2^32` (i.e., the Q0dd narrow
      case), under wider `uHi < dHi * 2^32`.

    * `div128Quot_v4_le_q_true_plus_one_of_rhatdd_hi_zero_of_uHi_lt_dHi_pow32`
      — final convenience wrapper deriving no-wrap from
      `rhatdd >> 32 = 0`.

  This widens the upper-bound chain to cover the regime `uHi ∈
  [2^63, dHi*2^32)`, which the existing `*_of_uHi_lt_pow63` wrappers
  in `UpperBound.lean` and `ExactQuotient.lean` exclude.
-/

module

public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Q0ddUBDHiPow32

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Wider-premise `un21 = r1` discharge from Phase-1b no-wrap.  Identical to
    `divKTrialCallV4Un21_eq_r1_of_no_wrap` except the only use of
    `Q1dd = q_true_1` is via PR #7059's wider `_of_uHi_lt_dHi_pow32`
    variant. -/
theorem divKTrialCallV4Un21_eq_r1_of_no_wrap_of_uHi_lt_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 : uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32)
    (h_no_wrap :
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat ≤
        ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
          (divKTrialCallV4Un1 uLo).toNat) :
    (divKTrialCallV4Un21 uHi uLo vTop).toNat =
      (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) % vTop.toNat := by
  let q := divKTrialCallV4Q1dd uHi uLo vTop
  let rhat := divKTrialCallV4Rhatdd uHi uLo vTop
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let un21 := divKTrialCallV4Un21 uHi uLo vTop
  let n := uHi.toNat * 2^32 + un1.toNat
  have hvTop_pos : 0 < vTop.toNat := by omega
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    unfold dHi dLo divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_post : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    simpa [q, rhat, dHi] using divKTrialCallV4Q1dd_rhatdd_post uHi uLo vTop hvTop_ge
  have h_q_eq : q.toNat = n / vTop.toNat := by
    simpa [q, n, un1] using
      divKTrialCallV4Q1dd_eq_q_true_1_of_uHi_lt_dHi_pow32
        uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_dHi_pow32
  have h_add := divKTrialCallV4Un21_additive_identity_of_no_wrap
    uHi uLo vTop hvTop_ge huHi_lt_vTop h_no_wrap
  have h_n_eq :
      n = q.toNat * vTop.toNat + un21.toNat + (rhat.toNat / 2^32) * 2^64 := by
    have h_qv :
        q.toNat * vTop.toNat =
          q.toNat * dHi.toNat * 2^32 + q.toNat * dLo.toNat := by
      rw [h_vTop_decomp]
      ring
    have h_n :
        n = (q.toNat * dHi.toNat + rhat.toNat) * 2^32 + un1.toNat := by
      unfold n
      rw [h_post]
    change un21.toNat + (rhat.toNat / 2^32) * 2^64 + q.toNat * dLo.toNat =
      rhat.toNat * 2^32 + un1.toNat at h_add
    rw [h_n, h_qv]
    nlinarith [h_add]
  have h_rem_eq : n - q.toNat * vTop.toNat = un21.toNat + (rhat.toNat / 2^32) * 2^64 := by
    omega
  have h_rem_lt : n - q.toNat * vTop.toNat < vTop.toNat := by
    rw [h_q_eq]
    have h_mul_comm : n / vTop.toNat * vTop.toNat =
        vTop.toNat * (n / vTop.toNat) := by ring
    rw [h_mul_comm]
    have h_div_mod : vTop.toNat * (n / vTop.toNat) + n % vTop.toNat = n :=
      Nat.div_add_mod n vTop.toNat
    have h_mod_lt : n % vTop.toNat < vTop.toNat := Nat.mod_lt n hvTop_pos
    omega
  have h_carry_zero : (rhat.toNat / 2^32) * 2^64 = 0 := by
    have hvTop_le : vTop.toNat ≤ 2^64 := Nat.le_of_lt vTop.isLt
    by_contra h_ne
    have h_pos : 0 < (rhat.toNat / 2^32) * 2^64 := Nat.pos_of_ne_zero h_ne
    have h_big : 2^64 ≤ (rhat.toNat / 2^32) * 2^64 := by
      have h_factor_pos : rhat.toNat / 2^32 ≠ 0 := by
        intro h_zero
        rw [h_zero] at h_pos
        simp at h_pos
      have h_factor : 1 ≤ rhat.toNat / 2^32 :=
        Nat.succ_le_of_lt (Nat.pos_of_ne_zero h_factor_pos)
      calc
        2^64 = 1 * 2^64 := by ring
        _ ≤ (rhat.toNat / 2^32) * 2^64 :=
          Nat.mul_le_mul_right (2^64) h_factor
    omega
  have h_un21_rem : un21.toNat = n - q.toNat * vTop.toNat := by
    rw [h_rem_eq, h_carry_zero]
    omega
  have h_mod : n % vTop.toNat = n - q.toNat * vTop.toNat := by
    rw [h_q_eq]
    have h_div_mod : n / vTop.toNat * vTop.toNat + n % vTop.toNat = n := by
      have h := Nat.div_add_mod n vTop.toNat
      simpa [Nat.mul_comm] using h
    omega
  rw [h_mod]
  exact h_un21_rem

/-- Wider-premise end-to-end `+1` floor bound from Phase-1 no-wrap.

    Composes `divKTrialCallV4Un21_eq_r1_of_no_wrap_of_uHi_lt_dHi_pow32` and
    `div128Quot_v4_le_q_true_plus_one_of_un21_eq_r1_of_un21_lt_dHi_pow32`
    (PR #7060) — `un21 < dHi*2^32` is kept explicit since `un21 = r1 <
    vTop` does not directly give `un21 < dHi*2^32`. -/
theorem div128Quot_v4_le_q_true_plus_one_of_no_wrap_of_uHi_lt_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 : uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32)
    (hUn21_lt_dHi_pow32 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32)
    (h_no_wrap :
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat ≤
        ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
          (divKTrialCallV4Un1 uLo).toNat) :
    (div128Quot_v4 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 := by
  have hUn21_lt_vTop : (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat :=
    divKTrialCallV4Un21_lt_vTop_of_uHi_lt_dHi_pow32
      uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_dHi_pow32
  have hUn21_eq_r1 :=
    divKTrialCallV4Un21_eq_r1_of_no_wrap_of_uHi_lt_dHi_pow32
      uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_dHi_pow32 h_no_wrap
  exact div128Quot_v4_le_q_true_plus_one_of_un21_eq_r1_of_un21_lt_dHi_pow32
    uHi uLo vTop hvTop_ge huHi_lt_vTop
    hUn21_lt_dHi_pow32 hUn21_lt_vTop hUn21_eq_r1

/-- Wider-premise `+1` floor bound in the final Phase-1b high-half-zero
    branch.  When `rhatdd >> 32 = 0`, the Phase-1b dLo bound gives no-wrap
    automatically, so this only needs the wider `uHi < dHi*2^32` and the
    `un21 < dHi*2^32` Q0dd-narrow premise. -/
theorem div128Quot_v4_le_q_true_plus_one_of_rhatdd_hi_zero_of_uHi_lt_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 : uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32)
    (hUn21_lt_dHi_pow32 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word)) :
    (div128Quot_v4 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 := by
  have h_no_wrap :=
    divKTrialCallV4Un21_low_no_wrap_of_rhatdd_hi_zero
      uHi uLo vTop hvTop_ge huHi_lt_vTop h_rhat_hi_zero
  exact div128Quot_v4_le_q_true_plus_one_of_no_wrap_of_uHi_lt_dHi_pow32
    uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_dHi_pow32
    hUn21_lt_dHi_pow32 h_no_wrap

end EvmAsm.Evm64
