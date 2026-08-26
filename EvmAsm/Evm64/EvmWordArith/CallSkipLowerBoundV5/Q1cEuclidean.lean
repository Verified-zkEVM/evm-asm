/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cEuclidean

  The Euclidean identity at the Phase-1a-corrected level for V5:
  `Q1c * dHi + Rhatc = uHi`. Holds for both branches by construction:
  - No-fire (hi1 = 0): Q1c = q1 (DIVU result), Rhatc = uHi - q1*dHi.
    Identity = `q1 * dHi + (uHi - q1*dHi)` = uHi mod 2^64; no-wrap from
    `q1 = uHi / dHi ≤ uHi / dHi ≤ uHi` (so q1*dHi ≤ uHi).
  - Fire (hi1 ≠ 0): Q1c = `0xFFFFFFFF` (cap), Rhatc = uHi - Q1c*dHi.
    Identity = `Q1c*dHi + (uHi - Q1c*dHi)` = uHi mod 2^64; no-wrap from
    Q1c < 2^32 and dHi < 2^32, so Q1c*dHi < 2^64. Then need `Q1c*dHi ≤
    uHi.toNat` for Nat-level subtraction — this comes from the post-DIVU
    fact that `q1 * dHi ≤ uHi` and `Q1c ≤ q1` when hi1 ≠ 0 (Q1c is the
    cap and q1 is at least 2^32 since hi1 ≠ 0, so q1 ≥ 2^32 > Q1c = 2^32-1).

  Wait — actually when hi1 ≠ 0, q1 ≥ 2^32 (since hi1 = q1>>32 ≠ 0). And
  Q1c = 2^32 - 1, so Q1c ≤ q1 - 1 < q1. So Q1c * dHi ≤ (q1 - 1) * dHi ≤
  q1 * dHi - dHi ≤ uHi - dHi ≤ uHi (since dHi ≥ 2^31).

  Bead `evm-asm-wbc4i.4.6.6` (V5.4.0.7). Prerequisite for V5.4.1.
-/

module

public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1d

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Phase-1a Euclidean identity at the V5 cap level.

    For both the no-fire (hi1 = 0) and fire (hi1 ≠ 0) branches, the
    identity `Q1c * dHi + Rhatc = uHi` holds at the Nat level under the
    standard `vTop ≥ 2^63` normalization. -/
theorem algorithmQ1cV5_rhatc_post
    (uHi vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    (algorithmQ1cV5 uHi vTop).toNat * (divKTrialCallV5DHi vTop).toNat +
      (algorithmRhatcV5 uHi vTop).toNat = uHi.toNat := by
  rw [algorithmQ1cV5_unfold, algorithmRhatcV5_unfold]
  dsimp only
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set q1 : Word := rv64_divu uHi dHi with hq1
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    rw [hdHi]; unfold divKTrialCallV5DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have h_dHi_lt : dHi.toNat < 2^32 := by
    rw [hdHi]; exact divKTrialCallV5DHi_lt_pow32 vTop
  have h_dHi_pos : dHi.toNat > 0 := by omega
  have h_dHi_ne : dHi ≠ 0 := by
    intro h
    have : dHi.toNat = 0 := by rw [h]; rfl
    omega
  -- q1 = uHi / dHi (since dHi ≠ 0)
  have h_q1_eq : q1.toNat = uHi.toNat / dHi.toNat := by
    rw [hq1]; unfold rv64_divu
    have : ¬ (dHi == 0#64) := by simpa using h_dHi_ne
    rw [if_neg this, BitVec.toNat_udiv]
  have h_q1_dHi_le_uHi : q1.toNat * dHi.toNat ≤ uHi.toNat := by
    rw [h_q1_eq]; exact Nat.div_mul_le_self _ _
  have h_q1_dHi_no_wrap : (q1 * dHi).toNat = q1.toNat * dHi.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    have : q1.toNat * dHi.toNat ≤ uHi.toNat := h_q1_dHi_le_uHi
    have : uHi.toNat < 2^64 := uHi.isLt
    omega
  have h_rhat_no_wrap : (uHi - q1 * dHi).toNat = uHi.toNat - (q1 * dHi).toNat := by
    rw [BitVec.toNat_sub]
    rw [h_q1_dHi_no_wrap]
    have h_le : q1.toNat * dHi.toNat ≤ uHi.toNat := h_q1_dHi_le_uHi
    have hlt : uHi.toNat < 2^64 := uHi.isLt
    omega
  -- Now case-split on hi1 = q1 >> 32.
  by_cases h_hi1 : q1 >>> (32 : BitVec 6).toNat = (0 : Word)
  · -- No-fire branch: Q1c = q1, Rhatc = uHi - q1*dHi.
    rw [if_pos h_hi1, if_pos h_hi1]
    rw [h_rhat_no_wrap, h_q1_dHi_no_wrap]
    omega
  · -- Fire branch: Q1c = q1cCap = 2^32-1, Rhatc = uHi - q1cCap*dHi.
    rw [if_neg h_hi1, if_neg h_hi1]
    set q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat with hcap
    have h_cap_nat : q1cCap.toNat = 2^32 - 1 := by rw [hcap]; decide
    have h_cap_lt : q1cCap.toNat < 2^32 := by omega
    -- hi1 ≠ 0 ⇒ q1 ≥ 2^32
    have h_hi1_nat : (q1 >>> (32 : BitVec 6).toNat).toNat ≠ 0 := by
      intro h
      apply h_hi1
      apply BitVec.eq_of_toNat_eq
      rw [h]; rfl
    have h_q1_hi_pos : (q1 >>> (32 : BitVec 6).toNat).toNat ≥ 1 := by
      omega
    have h_q1_ge : q1.toNat ≥ 2^32 := by
      have h_shift : (q1 >>> (32 : BitVec 6).toNat).toNat = q1.toNat / 2^32 := by
        rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      rw [h_shift] at h_q1_hi_pos
      have : q1.toNat / 2^32 ≥ 1 := h_q1_hi_pos
      omega
    -- q1cCap * dHi < q1 * dHi ≤ uHi (since q1cCap < q1)
    have h_cap_lt_q1 : q1cCap.toNat < q1.toNat := by omega
    have h_cap_dHi_no_wrap : (q1cCap * dHi).toNat = q1cCap.toNat * dHi.toNat := by
      rw [BitVec.toNat_mul]
      apply Nat.mod_eq_of_lt
      have : q1cCap.toNat * dHi.toNat < 2^32 * 2^32 := Nat.mul_lt_mul'' h_cap_lt h_dHi_lt
      calc q1cCap.toNat * dHi.toNat < 2^32 * 2^32 := this
        _ = 2^64 := by norm_num
    have h_cap_dHi_le_uHi : q1cCap.toNat * dHi.toNat ≤ uHi.toNat := by
      have step1 : q1cCap.toNat * dHi.toNat ≤ q1.toNat * dHi.toNat :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt h_cap_lt_q1)
      exact le_trans step1 h_q1_dHi_le_uHi
    have h_rhatc_no_wrap : (uHi - q1cCap * dHi).toNat = uHi.toNat - (q1cCap * dHi).toNat := by
      rw [BitVec.toNat_sub, h_cap_dHi_no_wrap]
      have hlt : uHi.toNat < 2^64 := uHi.isLt
      omega
    rw [h_rhatc_no_wrap, h_cap_dHi_no_wrap]
    omega

/-- Phase-2a Euclidean identity at the V5 cap level. Analog of
    `algorithmQ1cV5_rhatc_post` with `un21` in place of `uHi`.
    Holds for both branches by the same case-analysis pattern. -/
theorem algorithmQ0cV5_rhat2c_post
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    (algorithmQ0cV5 uHi uLo vTop).toNat * (divKTrialCallV5DHi vTop).toNat +
      (algorithmRhat2cV5 uHi uLo vTop).toNat =
      (divKTrialCallV5Un21 uHi uLo vTop).toNat := by
  rw [algorithmQ0cV5_unfold, algorithmRhat2cV5_unfold]
  dsimp only
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set un21 := divKTrialCallV5Un21 uHi uLo vTop with hun21
  set q0 : Word := rv64_divu un21 dHi with hq0
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    rw [hdHi]; unfold divKTrialCallV5DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have h_dHi_lt : dHi.toNat < 2^32 := by
    rw [hdHi]; exact divKTrialCallV5DHi_lt_pow32 vTop
  have h_dHi_ne : dHi ≠ 0 := by
    intro h
    have : dHi.toNat = 0 := by rw [h]; rfl
    omega
  have h_q0_eq : q0.toNat = un21.toNat / dHi.toNat := by
    rw [hq0]; unfold rv64_divu
    have : ¬ (dHi == 0#64) := by simpa using h_dHi_ne
    rw [if_neg this, BitVec.toNat_udiv]
  have h_q0_dHi_le_un21 : q0.toNat * dHi.toNat ≤ un21.toNat := by
    rw [h_q0_eq]; exact Nat.div_mul_le_self _ _
  have h_q0_dHi_no_wrap : (q0 * dHi).toNat = q0.toNat * dHi.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    have : un21.toNat < 2^64 := un21.isLt
    omega
  have h_rhat2_no_wrap : (un21 - q0 * dHi).toNat = un21.toNat - (q0 * dHi).toNat := by
    rw [BitVec.toNat_sub, h_q0_dHi_no_wrap]
    have hlt : un21.toNat < 2^64 := un21.isLt
    omega
  by_cases h_hi2 : q0 >>> (32 : BitVec 6).toNat = (0 : Word)
  · rw [if_pos h_hi2, if_pos h_hi2]
    rw [h_rhat2_no_wrap, h_q0_dHi_no_wrap]
    omega
  · rw [if_neg h_hi2, if_neg h_hi2]
    set q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat with hcap
    have h_cap_nat : q0cCap.toNat = 2^32 - 1 := by rw [hcap]; decide
    have h_cap_lt : q0cCap.toNat < 2^32 := by omega
    have h_hi2_nat : (q0 >>> (32 : BitVec 6).toNat).toNat ≠ 0 := by
      intro h
      apply h_hi2
      apply BitVec.eq_of_toNat_eq
      rw [h]; rfl
    have h_q0_hi_pos : (q0 >>> (32 : BitVec 6).toNat).toNat ≥ 1 := by omega
    have h_q0_ge : q0.toNat ≥ 2^32 := by
      have h_shift : (q0 >>> (32 : BitVec 6).toNat).toNat = q0.toNat / 2^32 := by
        rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      rw [h_shift] at h_q0_hi_pos
      omega
    have h_cap_lt_q0 : q0cCap.toNat < q0.toNat := by omega
    have h_cap_dHi_no_wrap : (q0cCap * dHi).toNat = q0cCap.toNat * dHi.toNat := by
      rw [BitVec.toNat_mul]
      apply Nat.mod_eq_of_lt
      have : q0cCap.toNat * dHi.toNat < 2^32 * 2^32 := Nat.mul_lt_mul'' h_cap_lt h_dHi_lt
      calc q0cCap.toNat * dHi.toNat < 2^32 * 2^32 := this
        _ = 2^64 := by norm_num
    have h_cap_dHi_le_un21 : q0cCap.toNat * dHi.toNat ≤ un21.toNat := by
      have step1 : q0cCap.toNat * dHi.toNat ≤ q0.toNat * dHi.toNat :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt h_cap_lt_q0)
      exact le_trans step1 h_q0_dHi_le_un21
    have h_rhat2c_no_wrap : (un21 - q0cCap * dHi).toNat = un21.toNat - (q0cCap * dHi).toNat := by
      rw [BitVec.toNat_sub, h_cap_dHi_no_wrap]
      have hlt : un21.toNat < 2^64 := un21.isLt
      omega
    rw [h_rhat2c_no_wrap, h_cap_dHi_no_wrap]
    omega

end EvmAsm.Evm64
