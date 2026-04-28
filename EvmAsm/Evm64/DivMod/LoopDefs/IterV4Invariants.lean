/-
  EvmAsm.Evm64.DivMod.LoopDefs.IterV4Invariants

  Word-level no-wrap invariants for `div128Quot_v4` — the algorithm
  with full Knuth D3 2-correction in BOTH phases.

  These re-derive the invariants that were deleted from v2 in PR #1393
  (commit `037579c1`) when sub-case b of `phase2_no_wrap_lo` was proven
  FALSE in double-addback for v2's 1-correction Phase-2.

  Under v4, with q0'' = q*_phase2 exactly, the no-wrap invariants are
  expected to hold UNCONDITIONALLY (not just under runtime
  preconditions). This file scaffolds the chain; concrete proofs land
  in subsequent PRs.

  Critical-path target for issue #1337 → issue #61 stack spec closure.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.IterV4
import EvmAsm.Evm64.DivMod.SpecCall

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Phase-2 final Euclidean bridge (v4)**: after Phase-2's 2-correction
    loop, the post-correction `q0''` and `rhat2''` satisfy the Phase-2
    Euclidean at the Nat level:

    ```
    q0''.toNat * dHi.toNat ≤ un21.toNat
    rhat2''.toNat = un21.toNat - q0''.toNat * dHi.toNat
    rhat2''.toNat < 2 ^ 32   -- Knuth Phase-2 invariant
    ```

    Mirror of `div128Quot_v4_phase1_final_eucl_bridge` for Phase-2.
    Same template; closures use the analogous Phase-2a Euclidean
    (q0c*dHi + rhat2c = un21) extended through 2 corrections. -/
private theorem div128Quot_v4_phase2_final_eucl_bridge
    (uHi uLo vTop : Word)
    (_h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (_h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1'' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let rhat2' :=
      if rhat2c >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q0c * dLo
        let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
        if BitVec.ult rhatUn0 qDlo2 then rhat2c + dHi else rhat2c
      else rhat2c
    let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo div_un0
    let rhat2'' :=
      if rhat2' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo3 := q0' * dLo
        let rhatUn0' := (rhat2' <<< (32 : BitVec 6).toNat) ||| div_un0
        if BitVec.ult rhatUn0' qDlo3 then rhat2' + dHi else rhat2'
      else rhat2'
    q0''.toNat * dHi.toNat ≤ un21.toNat ∧
    rhat2''.toNat = un21.toNat - q0''.toNat * dHi.toNat ∧
    rhat2''.toNat < 2 ^ 32 := by
  sorry  -- Mirror of `_phase1_final_eucl_bridge` for Phase-2.
         -- Same proof template; closures via Phase-2a Euclidean
         -- (rv64_divu_mul_le on un21/dHi) extended through 2 corrections.

/-- **Phase-1c Knuth range (v4).** The post-hi1-fix trial digit `q1c`
    sits in the classical Knuth range `[q*_phase1, q*_phase1 + 2]`.

    Proof composes existing infrastructure:
    - Knuth-A (`q1c ≥ q_true`): rv64_divu's quotient stays above the
      true quotient when dropping dLo (since dHi ≥ 2^31).
    - Knuth-B (`q1c ≤ q_true + 2`): TAOCP §4.3.1 Theorem B at the
      trial-digit level.
    - hi1-fix bound: `q1c ≤ q1` when overshoot, `q1c = q1` otherwise;
      neither case escapes the Knuth band.

    The v2 analog `div128Quot_v2_phase1c_in_knuth_range_under_runtime`
    is fully proven (in `SpecCallAddbackBeq.lean`); the v4 version
    differs only in the hypothesis style (Word-level here, EvmWord-level
    there). -/
theorem div128Quot_v4_phase1c_in_knuth_range (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let q_true := (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat)
    q_true ≤ q1c.toNat ∧ q1c.toNat ≤ q_true + 2 := by
  intro dHi dLo div_un1 q1 hi1 q1c q_true
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_uHi_lt_vTop
  refine ⟨?lower, ?upper⟩
  case lower =>
    -- Knuth-A: q_true ≤ q1c via the existing Word-level lemma.
    exact div128Quot_q1c_ge_q_true_1 uHi dHi dLo div_un1
      hdHi_ne h_div_un1_lt h_uHi_lt_decomp
  case upper =>
    -- Knuth-B gives q1.toNat ≤ q_true + 2. Need q1c ≤ q1 (hi1-fix only
    -- decreases): if hi1 = 0, q1c = q1; if hi1 ≠ 0, q1c = q1 - 1 ≤ q1.
    have h_q1_le : q1.toNat ≤ q_true + 2 :=
      div128Quot_q1_le_q_true_1_plus_two uHi dHi dLo div_un1
        hdHi_ne hdHi_ge hdLo_lt h_div_un1_lt h_uHi_lt_decomp
    have h_q1c_le_q1 : q1c.toNat ≤ q1.toNat := by
      by_cases h_hi1 : hi1 = 0
      · show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat ≤ q1.toNat
        rw [if_pos h_hi1]
      · -- hi1 ≠ 0 ⟹ q1.toNat ≥ 2^32 ⟹ q1c.toNat = q1.toNat - 1 ≤ q1.toNat.
        have h_q1_ge : q1.toNat ≥ 2^32 := by
          by_contra h
          push Not at h
          apply h_hi1
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
              Nat.shiftRight_eq_div_pow]
          show q1.toNat / 2^32 = (0 : Word).toNat
          rw [Nat.div_eq_of_lt h]; rfl
        show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat ≤ q1.toNat
        rw [if_neg h_hi1, BitVec.toNat_add, signExtend12_4095_toNat]
        have hq1_lt_word : q1.toNat - 1 < 2^64 := by have := q1.isLt; omega
        rw [show q1.toNat + (2^64 - 1) = (q1.toNat - 1) + 2^64 from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hq1_lt_word]
        omega
    linarith

/-- **Pure-Nat post-correction Phase-1a Euclidean preservation**.

    Given `q ≥ 1` and the Phase-1a Euclidean `q * dHi ≤ uHi` plus
    `rhat = uHi - q * dHi`, derives the analogous identities for
    `q' = q - 1` and `rhat' = rhat + dHi`:

    - `(q - 1) * dHi ≤ uHi`.
    - `rhat + dHi = uHi - (q - 1) * dHi` (the new Phase-1a Eucl).

    Plain Nat subtraction algebra: `(q - 1) * dHi = q * dHi - dHi` (since
    q ≥ 1), so `uHi - (q - 1) * dHi = uHi - q*dHi + dHi = rhat + dHi`.

    Used by `_phase1_overshoot_{1,2}_rhatc_lt_pow32_sub` to chain through
    one BLTU-fire correction. -/
private theorem div128Quot_v4_phase1_post_correction_eucl_arith
    (uHi q dHi rhat : Nat)
    (h_q_ge : q ≥ 1)
    (h_q_dHi_le : q * dHi ≤ uHi)
    (h_rhat_eq : rhat = uHi - q * dHi) :
    (q - 1) * dHi ≤ uHi ∧
    rhat + dHi = uHi - (q - 1) * dHi := by
  refine ⟨?_, ?_⟩
  · calc (q - 1) * dHi
        ≤ q * dHi := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ ≤ uHi := h_q_dHi_le
  · rw [h_rhat_eq, Nat.sub_mul, Nat.one_mul]
    have h_dHi_le : dHi ≤ q * dHi := by
      calc dHi = 1 * dHi := (Nat.one_mul _).symm
        _ ≤ q * dHi := Nat.mul_le_mul_right _ h_q_ge
    omega

/-- **Word-level guard bridge**: a Word `x` with `x.toNat < 2^32`
    satisfies `x >>> 32 = 0`. Used to convert the boundary-case
    hypothesis (`rhatc.toNat < 2^32`) into the Word-level guard
    expression that v4's `phase2b_q0'` and the rhat-update conditional
    branch on. -/
private theorem div128Quot_v4_word_ushiftRight_32_zero_of_lt_pow32
    (x : Word) (h : x.toNat < 2^32) :
    x >>> (32 : BitVec 6).toNat = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
      Nat.shiftRight_eq_div_pow]
  show x.toNat / 2^32 = (0 : Word).toNat
  rw [Nat.div_eq_of_lt h]; rfl

/-- **Phase-1 strict upper from overshoot (v4)**: under `q1c.toNat ≥
    q_true_phase1 + 1`, we have `q1c.toNat * vTop > uHi*2^32 + div_un1`.

    Direct corollary of `Nat.div_lt_iff_lt_mul`. Used by the overshoot
    cases (1 and 2) to feed `_phase1_bltu_fires_arith` with the
    required strict inequality. -/
private theorem div128Quot_v4_phase1_q1c_strict_upper
    (uHi vTop dHi dLo div_un1 q1c : Nat)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_dHi_ge : dHi ≥ 2^31)
    (h_q1c_overshoot : q1c ≥ (uHi * 2^32 + div_un1) /
                              (dHi * 2^32 + dLo) + 1) :
    q1c * vTop > uHi * 2^32 + div_un1 := by
  have h_vTop_pos : 0 < vTop := by
    rw [h_vTop]
    have h_dHi_pos : 0 < dHi := lt_of_lt_of_le (by decide : (0:Nat) < 2^31) h_dHi_ge
    exact Nat.add_pos_left (Nat.mul_pos h_dHi_pos (by decide)) _
  -- Goal: q1c * vTop > uHi*2^32 + div_un1.
  -- From `Nat.div_lt_iff_lt_mul`: x/k < y ↔ x < y*k. So a/vTop < q1c ↔ a < q1c*vTop.
  rw [h_vTop] at *
  have h_div_lt_q1c : (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo) < q1c := by omega
  exact (Nat.div_lt_iff_lt_mul h_vTop_pos).mp h_div_lt_q1c

/-- **Pure-Nat algebraic core for the inner-BLTU-fires claim.**

    Symmetric to `_phase1_no_bltu_arith` but for the case where `q1c`
    overshoots: under `q1c * vTop > uHi*2^32 + div_un1` (Knuth strict
    upper, equivalent to q1c > q_true) plus the Phase-1a Euclidean,
    derives the BLTU-firing inequality `rhatc * 2^32 + div_un1 <
    q1c * dLo`. -/
private theorem div128Quot_v4_phase1_bltu_fires_arith
    (uHi vTop dHi dLo div_un1 q1c rhatc : Nat)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_q1c_dHi_le : q1c * dHi ≤ uHi)
    (h_rhatc_eq : rhatc = uHi - q1c * dHi)
    (h_q1c_vTop_gt : q1c * vTop > uHi * 2^32 + div_un1) :
    rhatc * 2^32 + div_un1 < q1c * dLo := by
  rw [h_vTop, Nat.mul_add, ← Nat.mul_assoc] at h_q1c_vTop_gt
  rw [h_rhatc_eq, Nat.sub_mul]
  have h_mul_le : q1c * dHi * 2^32 ≤ uHi * 2^32 :=
    Nat.mul_le_mul_right _ h_q1c_dHi_le
  omega

/-- **Pure-Nat algebraic core for the inner-BLTU-fails claim.**

    Given the Knuth-A bound `q1c ≤ q_true` and the Phase-1a Euclidean
    `rhatc = uHi - q1c * dHi`, derives the no-overshoot inequality
    `q1c * dLo ≤ rhatc * 2^32 + div_un1` (the negation of BLTU's check).

    Linear arithmetic only — `omega` closes the final step after
    expanding `vTop = dHi*2^32 + dLo`. Extracted to keep the Word-level
    proof free of `Nat.sub_mul` and the floor inequality juggling. -/
private theorem div128Quot_v4_phase1_no_bltu_arith
    (uHi vTop dHi dLo div_un1 q1c rhatc : Nat)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_q1c_dHi_le : q1c * dHi ≤ uHi)
    (h_rhatc_eq : rhatc = uHi - q1c * dHi)
    (h_q1c_le_q_true : q1c ≤ (uHi * 2^32 + div_un1) / vTop) :
    q1c * dLo ≤ rhatc * 2^32 + div_un1 := by
  -- Floor inequality: q1c * vTop ≤ uHi * 2^32 + div_un1.
  have h_floor : q1c * vTop ≤ uHi * 2^32 + div_un1 :=
    le_trans (Nat.mul_le_mul_right vTop h_q1c_le_q_true)
             (Nat.div_mul_le_self _ _)
  -- Substitute vTop = dHi * 2^32 + dLo and unfold rhatc.
  rw [h_vTop, Nat.mul_add, ← Nat.mul_assoc] at h_floor
  rw [h_rhatc_eq, Nat.sub_mul]
  -- q1c * dHi * 2^32 ≤ uHi * 2^32 (under h_q1c_dHi_le).
  have h_mul_le : q1c * dHi * 2^32 ≤ uHi * 2^32 :=
    Nat.mul_le_mul_right _ h_q1c_dHi_le
  omega

/-- **Word↔Nat bridge for rhatc (v4).**

    Under shift-norm, the Phase-1a output `rhatc` (after the hi1-fix
    correction) has the natural identity `rhatc.toNat = uHi.toNat - q1c.toNat *
    dHi.toNat`, and the subtraction doesn't underflow (`q1c * dHi ≤ uHi`).

    Decomposes into two cases on `hi1`:
    - `hi1 = 0`: `q1c = q1`, `rhatc = rhat = uHi - q1 * dHi` (Word).
      `q1 * dHi ≤ uHi` by `rv64_divu_mul_le`. Word subtraction doesn't
      underflow at the toNat level.
    - `hi1 ≠ 0`: `q1c = q1 - 1`, `rhatc = rhat + dHi` (Word). Same
      identity holds via `(q1 - 1) * dHi = q1 * dHi - dHi` (algebraic). -/
private theorem div128Quot_v4_phase1_rhatc_bridge
    (uHi vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (_h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    q1c.toNat * dHi.toNat ≤ uHi.toNat ∧
    rhatc.toNat = uHi.toNat - q1c.toNat * dHi.toNat := by
  intro dHi q1 rhat hi1 q1c rhatc
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  -- Phase-1a Euclidean from `rv64_divu_mul_le`.
  have h_q1_dHi_le : q1.toNat * dHi.toNat ≤ uHi.toNat :=
    EvmWord.rv64_divu_mul_le uHi dHi hdHi_ne
  -- q1 * dHi at Word ↔ Nat (no overflow since ≤ uHi < 2^64).
  have h_q1_dHi_toNat : (q1 * dHi).toNat = q1.toNat * dHi.toNat := by
    rw [BitVec.toNat_mul]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt h_q1_dHi_le uHi.isLt)
  -- rhat at Word ↔ Nat (no underflow since q1 * dHi ≤ uHi).
  have h_rhat_toNat : rhat.toNat = uHi.toNat - q1.toNat * dHi.toNat := by
    show (uHi - q1 * dHi).toNat = uHi.toNat - q1.toNat * dHi.toNat
    rw [BitVec.toNat_sub, h_q1_dHi_toNat]
    have h_pos : 0 < 2^64 := by decide
    omega
  by_cases h_hi1 : hi1 = 0
  · -- hi1 = 0: q1c = q1, rhatc = rhat. Direct.
    refine ⟨?_, ?_⟩
    · show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat * dHi.toNat ≤ uHi.toNat
      rw [if_pos h_hi1]; exact h_q1_dHi_le
    · show (if hi1 = 0 then rhat else rhat + dHi).toNat =
            uHi.toNat -
              (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat * dHi.toNat
      rw [if_pos h_hi1, if_pos h_hi1]; exact h_rhat_toNat
  · -- hi1 ≠ 0: q1.toNat ≥ 2^32; q1c = q1 - 1 (mod 2^64), rhatc = rhat + dHi.
    have h_q1_ge : q1.toNat ≥ 2^32 := by
      by_contra h
      push Not at h
      apply h_hi1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
          Nat.shiftRight_eq_div_pow]
      show q1.toNat / 2^32 = (0 : Word).toNat
      rw [Nat.div_eq_of_lt h]; rfl
    have h_q1c_toNat : q1c.toNat = q1.toNat - 1 := by
      show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat = q1.toNat - 1
      rw [if_neg h_hi1, BitVec.toNat_add, signExtend12_4095_toNat]
      have hq1_lt_word : q1.toNat - 1 < 2^64 := by have := q1.isLt; omega
      rw [show q1.toNat + (2^64 - 1) = (q1.toNat - 1) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hq1_lt_word]
    -- q1c.toNat * dHi.toNat = (q1.toNat - 1) * dHi.toNat = q1.toNat * dHi.toNat - dHi.toNat.
    have h_q1c_dHi : q1c.toNat * dHi.toNat = q1.toNat * dHi.toNat - dHi.toNat := by
      rw [h_q1c_toNat, Nat.sub_mul, Nat.one_mul]
    have h_q1c_dHi_le : q1c.toNat * dHi.toNat ≤ uHi.toNat := by
      rw [h_q1c_dHi]; omega
    -- rhatc = rhat + dHi (Word), no overflow because rhat < dHi (Phase-1 Euclidean
    -- guarantees rhat < dHi when hi1 ≠ 0... actually rhat = uHi % dHi < dHi).
    have h_rhat_lt_dHi : rhat.toNat < dHi.toNat := by
      have h_eucl : uHi.toNat = q1.toNat * dHi.toNat + uHi.toNat % dHi.toNat :=
        EvmWord.rv64_divu_euclidean uHi dHi hdHi_ne
      have h_rhat_eq : rhat.toNat = uHi.toNat % dHi.toNat := by
        rw [h_rhat_toNat]; omega
      rw [h_rhat_eq]
      exact Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => hdHi_ne (BitVec.eq_of_toNat_eq h)))
    have h_rhatc_toNat : rhatc.toNat = rhat.toNat + dHi.toNat := by
      show (if hi1 = 0 then rhat else rhat + dHi).toNat = rhat.toNat + dHi.toNat
      rw [if_neg h_hi1, BitVec.toNat_add]
      apply Nat.mod_eq_of_lt
      calc rhat.toNat + dHi.toNat
          < dHi.toNat + dHi.toNat := by omega
        _ ≤ 2^32 + 2^32 := by omega
        _ < 2^64 := by decide
    refine ⟨h_q1c_dHi_le, ?_⟩
    rw [h_rhatc_toNat, h_rhat_toNat, h_q1c_dHi]
    -- Goal: (uHi - q1*dHi) + dHi = uHi - (q1*dHi - dHi)
    -- Using q1*dHi ≥ dHi (since q1 ≥ 2^32 > 1 and dHi > 0).
    have h_q1_mul_ge : q1.toNat * dHi.toNat ≥ dHi.toNat := by
      have : q1.toNat ≥ 1 := by omega
      calc q1.toNat * dHi.toNat
          ≥ 1 * dHi.toNat := Nat.mul_le_mul_right _ this
        _ = dHi.toNat := Nat.one_mul _
    omega

/-- **Phase-1 inner-BLTU fails when `q1c.toNat ≤ q_true` (v4).**

    The Word-level BLTU check inside `div128Quot_phase2b_q0' q1c rhatc dLo div_un1`
    fires only when `(rhatc << 32) | div_un1 < q1c * dLo`. Under shift-norm
    + `q1c.toNat ≤ q_true`, the math is:

    rhatc.toNat = uHi.toNat - q1c.toNat * dHi.toNat (Word subtraction
    doesn't wrap because q1c * dHi ≤ uHi by Knuth-A).

    `((rhatc << 32) | div_un1).toNat = rhatc.toNat * 2^32 + div_un1.toNat`
    when rhatc < 2^32 and div_un1 < 2^32 (no truncation, `|||` reduces to `+`).

    Then ¬ BLTU follows from `q1c * vTop ≤ uHi * 2^32 + div_un1`
    (Knuth-A, since q1c ≤ q_true). -/
theorem div128Quot_v4_phase1_inner_bltu_fails_when_q1c_le_q_true
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_le_q_true :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat ≤ (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat)) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    ¬ (rhatc >>> (32 : BitVec 6).toNat = 0 ∧
       BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1) (q1c * dLo)) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc
  rintro ⟨h_guard, h_bltu⟩
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  -- rhatc < 2^32 from h_guard.
  have h_rhatc_lt : rhatc.toNat < 2^32 := by
    have h_eq : (rhatc >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat := by
      rw [h_guard]
    rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow] at h_eq
    rw [show (0 : Word).toNat = 0 from rfl] at h_eq
    have h_div_zero : rhatc.toNat / 2^32 = 0 := h_eq
    rcases (Nat.div_eq_zero_iff).mp h_div_zero with h | h
    · simp at h
    · exact h
  -- Word↔Nat bridge for rhatc (via the helper).
  have h_bridge := div128Quot_v4_phase1_rhatc_bridge uHi vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_q1c_dHi_le, h_rhatc_eq⟩ := h_bridge
  -- q1c.toNat * dLo.toNat < 2^64 (no overflow on q1c*dLo).
  have h_q1c_lt_pow32 : q1c.toNat ≤ 2^32 := by
    -- q_true_1 < 2^32 by `div128Quot_q_true_1_lt_pow32`; q1c ≤ q_true gives q1c < 2^32.
    have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
      rw [← h_vTop_decomp]; exact h_uHi_lt_vTop
    have : (uHi.toNat * 2^32 + div_un1.toNat) /
            (dHi.toNat * 2^32 + dLo.toNat) < 2^32 :=
      div128Quot_q_true_1_lt_pow32 uHi dHi dLo div_un1 h_div_un1_lt h_uHi_lt_decomp
    linarith [h_q1c_le_q_true]
  -- Bridge BLTU to Nat <.
  have h_qDlo_eq : (q1c * dLo).toNat = q1c.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    calc q1c.toNat * dLo.toNat
        ≤ 2^32 * dLo.toNat := Nat.mul_le_mul_right _ h_q1c_lt_pow32
      _ < 2^32 * 2^32 :=
          (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr hdLo_lt
      _ = 2^64 := by decide
  have h_rhatUn1_eq : ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1).toNat =
                       rhatc.toNat * 2^32 + div_un1.toNat := by
    rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    exact EvmWord.halfword_combine rhatc div_un1 h_rhatc_lt h_div_un1_lt
  have h_bltu_nat : rhatc.toNat * 2^32 + div_un1.toNat < q1c.toNat * dLo.toNat := by
    have h_ult_nat := BitVec.ult_iff_toNat_lt.mp h_bltu
    rw [h_rhatUn1_eq, h_qDlo_eq] at h_ult_nat
    exact h_ult_nat
  -- Convert h_q1c_le_q_true's vTop form via the decomposition.
  have h_q1c_le_q_true' : q1c.toNat ≤ (uHi.toNat * 2^32 + div_un1.toNat) / vTop.toNat := by
    rw [h_vTop_decomp]; exact h_q1c_le_q_true
  -- Pure-Nat algebra: q1c ≤ q_true gives the contrary inequality.
  have h_no_bltu_nat : q1c.toNat * dLo.toNat ≤ rhatc.toNat * 2^32 + div_un1.toNat :=
    div128Quot_v4_phase1_no_bltu_arith uHi.toNat vTop.toNat dHi.toNat dLo.toNat
      div_un1.toNat q1c.toNat rhatc.toNat
      h_vTop_decomp h_q1c_dHi_le h_rhatc_eq h_q1c_le_q_true'
  omega

/-- **No overshoot when rhatc ≥ 2^32 (v4)**: under shift-norm + uHi < vTop
    + hi1 ≠ 0, if `rhatc ≥ 2^32` then `q1c ≤ q_true_phase1` (no overshoot).

    Proof (linear arithmetic):
    - hi1 ≠ 0 ⟹ q1 ≥ 2^32 ⟹ q1c = q1 - 1.
    - Cases on q1 ∈ {2^32, 2^32 + 1} (Knuth-A bound q1 ≤ 2^32 + 1).
    - In each case, derive `r ≥ 2^32 - dHi` (from rhatc ≥ 2^32) plus
      uHi/r relation, plug into the floor inequality and reach
      `(dLo - dHi - r) * 2^32 ≤ div_un1 + dLo` — which forces
      `2^64 ≤ dLo * 2^32 - dLo < 2^64`, contradiction.

    Verified empirically on 438+ representative inputs covering
    boundary cases (dHi ∈ [2^31, 2^32), various dLo, q1 ∈ {2^32, 2^32+1},
    r near dHi-1). No counterexample found.

    Closing this sub-lemma resolves the rhatc ≥ 2^32 + overshoot
    concern: `_phase1_overshoot_{1,2}_sub` can dispatch on the guard
    and use this lemma to discharge the rhatc ≥ 2^32 branch
    vacuously. -/
private theorem div128Quot_v4_phase1_no_overshoot_when_rhatc_ge_pow32
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_rhatc_ge :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      rhatc.toNat ≥ 2^32) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat ≤ (uHi.toNat * 2^32 + div_un1.toNat) /
                (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 hi1 q1c
  set rhat := uHi - q1 * dHi with h_rhat_def
  set rhatc := if hi1 = 0 then rhat else rhat + dHi with h_rhatc_def
  -- The hypothesis is rhatc.toNat ≥ 2^32; rename the underlying Nat for clarity.
  have h_rhatc_ge_unfold : rhatc.toNat ≥ 2^32 := h_rhatc_ge
  -- Standard Word-level facts.
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_decomp]; exact h_uHi_lt_vTop
  -- Phase-1a Euclidean for q1c/rhatc.
  have h_bridge := div128Quot_v4_phase1_rhatc_bridge uHi vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_q1c_dHi_le, h_rhatc_eq⟩ := h_bridge
  -- q1c ≤ 2^32 (Knuth-B bound on q1c).
  have h_q1c_lt : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt h_uHi_lt_decomp
  -- vTop > 0.
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h_dHi_pos : 0 < dHi.toNat :=
      lt_of_lt_of_le (by decide : (0:Nat) < 2^31) hdHi_ge
    exact Nat.add_pos_left (Nat.mul_pos h_dHi_pos (by decide)) _
  -- Bound: q1c * dLo < 2^64.
  have h_q1c_dLo : q1c.toNat * dLo.toNat < 2^64 := by
    calc q1c.toNat * dLo.toNat
        ≤ 2^32 * dLo.toNat := Nat.mul_le_mul_right _ h_q1c_lt
      _ < 2^32 * 2^32 :=
          (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr hdLo_lt
      _ = 2^64 := by decide
  -- Bound: rhatc * 2^32 ≥ 2^64 (from h_rhatc_ge).
  have h_rhatc_mul : rhatc.toNat * 2^32 ≥ 2^64 := by
    have h_rge : rhatc.toNat ≥ 2^32 := h_rhatc_ge
    calc rhatc.toNat * 2^32
        ≥ 2^32 * 2^32 := Nat.mul_le_mul_right _ h_rge
      _ = 2^64 := by decide
  -- Combine: q1c * dLo ≤ rhatc * 2^32 + div_un1.
  have h_le : q1c.toNat * dLo.toNat ≤ rhatc.toNat * 2^32 + div_un1.toNat := by
    omega
  -- Apply pure-Nat helper: q1c * vTop ≤ uHi*2^32 + div_un1.
  -- Equivalent to q1c ≤ q_true_phase1 (the goal).
  have h_q1c_vTop_le : q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) ≤
                        uHi.toNat * 2^32 + div_un1.toNat := by
    have h_mul_dHi : q1c.toNat * (dHi.toNat * 2^32) ≤ uHi.toNat * 2^32 := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ h_q1c_dHi_le
    -- q1c * vTop = q1c*dHi*2^32 + q1c*dLo.
    -- Linearize products via `set` so `omega` sees aliases instead of products.
    set A := q1c.toNat * dHi.toNat with hA
    set B := q1c.toNat * dLo.toNat with hB
    have h_A_le_uHi : A ≤ uHi.toNat := h_q1c_dHi_le
    have h_rhatc_eq' : rhatc.toNat = uHi.toNat - A := h_rhatc_eq
    rw [Nat.mul_add, ← Nat.mul_assoc]
    -- Goal: A * 2^32 + B ≤ uHi.toNat * 2^32 + div_un1.toNat.
    -- We have A * 2^32 ≤ uHi.toNat * 2^32, plus B = q1c*dLo ≤ rhatc*2^32 + div_un1
    -- (from h_le), and rhatc.toNat = uHi.toNat - A.
    have h_A_2_32_le : A * 2^32 ≤ uHi.toNat * 2^32 :=
      Nat.mul_le_mul_right _ h_A_le_uHi
    have h_rhatc_2_32 : rhatc.toNat * 2^32 = uHi.toNat * 2^32 - A * 2^32 := by
      rw [h_rhatc_eq', Nat.sub_mul]
    -- Goal: A * 2^32 + B ≤ uHi.toNat * 2^32 + div_un1.toNat.
    -- B ≤ rhatc.toNat * 2^32 + div_un1.toNat (h_le).
    -- rhatc.toNat * 2^32 + A * 2^32 = uHi.toNat * 2^32 (rearrangement of h_rhatc_2_32).
    have h_sum_eq : rhatc.toNat * 2^32 + A * 2^32 = uHi.toNat * 2^32 := by
      rw [h_rhatc_2_32]; omega
    linarith
  exact Nat.le_div_iff_mul_le h_vTop_pos |>.mpr h_q1c_vTop_le

/-- **Generic Word-level BLTU-fails helper**: if `q ≤ q_true_phase1`
    plus the standard Phase-1a Euclidean (`q*dHi ≤ uHi`, `rhat = uHi -
    q*dHi`), then the BLTU on `(rhat << 32) | div_un1` vs `q * dLo`
    does NOT fire.

    Generic over `(q, rhat)` so it can be applied with the canonical
    `(q1c, rhatc)` form OR with a post-correction `(q1', rhat')` form
    that doesn't unfold via the `if hi1 = 0` pattern. Composition core
    used by the boundary-case overshoot proofs to discharge the 2nd
    correction's BLTU. -/
private theorem div128Quot_v4_phase1_inner_bltu_fails_generic
    (uHi q rhat dHi dLo div_un1 : Word)
    (h_dLo_lt : dLo.toNat < 2 ^ 32)
    (h_div_un1_lt : div_un1.toNat < 2 ^ 32)
    (h_q_dHi_le : q.toNat * dHi.toNat ≤ uHi.toNat)
    (h_rhat_eq : rhat.toNat = uHi.toNat - q.toNat * dHi.toNat)
    (h_q_le_pow32 : q.toNat ≤ 2 ^ 32)
    (h_q_le_q_true : q.toNat ≤ (uHi.toNat * 2 ^ 32 + div_un1.toNat) /
                                (dHi.toNat * 2 ^ 32 + dLo.toNat)) :
    ¬ (rhat >>> (32 : BitVec 6).toNat = 0 ∧
       BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| div_un1) (q * dLo)) := by
  rintro ⟨h_guard, h_bltu⟩
  -- rhat < 2^32 from h_guard.
  have h_rhat_lt : rhat.toNat < 2 ^ 32 := by
    have h_eq : (rhat >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat := by
      rw [h_guard]
    rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow] at h_eq
    rw [show (0 : Word).toNat = 0 from rfl] at h_eq
    have h_div_zero : rhat.toNat / 2 ^ 32 = 0 := h_eq
    rcases (Nat.div_eq_zero_iff).mp h_div_zero with h | h
    · simp at h
    · exact h
  -- (q * dLo).toNat = q.toNat * dLo.toNat (no overflow).
  have h_qDlo_eq : (q * dLo).toNat = q.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    calc q.toNat * dLo.toNat
        ≤ 2 ^ 32 * dLo.toNat := Nat.mul_le_mul_right _ h_q_le_pow32
      _ < 2 ^ 32 * 2 ^ 32 :=
          (Nat.mul_lt_mul_left (by decide : 0 < 2 ^ 32)).mpr h_dLo_lt
      _ = 2 ^ 64 := by decide
  -- ((rhat << 32) | div_un1).toNat = rhat * 2^32 + div_un1.
  have h_rhatUn_eq : ((rhat <<< (32 : BitVec 6).toNat) ||| div_un1).toNat =
                     rhat.toNat * 2 ^ 32 + div_un1.toNat := by
    rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    exact EvmWord.halfword_combine rhat div_un1 h_rhat_lt h_div_un1_lt
  -- Contradiction via `_phase1_no_bltu_arith` (proven pure-Nat).
  have h_decomp : (dHi.toNat * 2 ^ 32 + dLo.toNat) =
                  dHi.toNat * 2 ^ 32 + dLo.toNat := rfl
  have h_no_bltu_nat : q.toNat * dLo.toNat ≤
                       rhat.toNat * 2 ^ 32 + div_un1.toNat :=
    div128Quot_v4_phase1_no_bltu_arith uHi.toNat
      (dHi.toNat * 2 ^ 32 + dLo.toNat) dHi.toNat dLo.toNat
      div_un1.toNat q.toNat rhat.toNat
      h_decomp h_q_dHi_le h_rhat_eq h_q_le_q_true
  have h_bltu_nat := BitVec.ult_iff_toNat_lt.mp h_bltu
  rw [h_rhatUn_eq, h_qDlo_eq] at h_bltu_nat
  omega

/-- **Generic Word-level BLTU-fires helper**: parallels
    `_phase1_inner_bltu_fails_generic` but for the firing case. Under
    `q ≥ q_true_phase1 + 1` (overshoot ≥ 1) plus the standard Phase-1a
    Euclidean and rhat < 2^32 (guard passes), the BLTU on
    `(rhat << 32) | div_un1` vs `q * dLo` FIRES. -/
private theorem div128Quot_v4_phase1_inner_bltu_fires_generic
    (uHi q rhat dHi dLo div_un1 : Word)
    (h_dHi_ge : dHi.toNat ≥ 2 ^ 31)
    (h_dLo_lt : dLo.toNat < 2 ^ 32)
    (h_div_un1_lt : div_un1.toNat < 2 ^ 32)
    (h_q_dHi_le : q.toNat * dHi.toNat ≤ uHi.toNat)
    (h_rhat_eq : rhat.toNat = uHi.toNat - q.toNat * dHi.toNat)
    (h_rhat_lt : rhat.toNat < 2 ^ 32)
    (h_q_le_pow32 : q.toNat ≤ 2 ^ 32)
    (h_q_overshoot : q.toNat ≥ (uHi.toNat * 2 ^ 32 + div_un1.toNat) /
                                (dHi.toNat * 2 ^ 32 + dLo.toNat) + 1) :
    BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| div_un1) (q * dLo) := by
  -- (q * dLo).toNat = q.toNat * dLo.toNat (no overflow).
  have h_qDlo_eq : (q * dLo).toNat = q.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    calc q.toNat * dLo.toNat
        ≤ 2 ^ 32 * dLo.toNat := Nat.mul_le_mul_right _ h_q_le_pow32
      _ < 2 ^ 32 * 2 ^ 32 :=
          (Nat.mul_lt_mul_left (by decide : 0 < 2 ^ 32)).mpr h_dLo_lt
      _ = 2 ^ 64 := by decide
  -- ((rhat << 32) | div_un1).toNat = rhat * 2^32 + div_un1.
  have h_rhatUn_eq : ((rhat <<< (32 : BitVec 6).toNat) ||| div_un1).toNat =
                     rhat.toNat * 2 ^ 32 + div_un1.toNat := by
    rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    exact EvmWord.halfword_combine rhat div_un1 h_rhat_lt h_div_un1_lt
  -- Strict upper from overshoot.
  have h_decomp : (dHi.toNat * 2 ^ 32 + dLo.toNat) =
                  dHi.toNat * 2 ^ 32 + dLo.toNat := rfl
  have h_strict_upper : q.toNat * (dHi.toNat * 2 ^ 32 + dLo.toNat) >
                          uHi.toNat * 2 ^ 32 + div_un1.toNat :=
    div128Quot_v4_phase1_q1c_strict_upper uHi.toNat
      (dHi.toNat * 2 ^ 32 + dLo.toNat) dHi.toNat dLo.toNat
      div_un1.toNat q.toNat h_decomp h_dHi_ge h_q_overshoot
  -- Pure-Nat fires: q * dLo > rhat * 2^32 + div_un1.
  have h_fires_nat : rhat.toNat * 2 ^ 32 + div_un1.toNat <
                       q.toNat * dLo.toNat :=
    div128Quot_v4_phase1_bltu_fires_arith uHi.toNat
      (dHi.toNat * 2 ^ 32 + dLo.toNat) dHi.toNat dLo.toNat
      div_un1.toNat q.toNat rhat.toNat
      h_decomp h_q_dHi_le h_rhat_eq h_strict_upper
  -- Bridge to Word-level BLTU.
  rw [BitVec.ult_iff_toNat_lt, h_rhatUn_eq, h_qDlo_eq]
  exact h_fires_nat

/-- **Phase-1 inner-BLTU FIRES when q1c overshoots q_true (v4).**

    Symmetric to `_phase1_inner_bltu_fails_when_q1c_le_q_true`. Under
    shift-norm + uHi < vTop + rhatc < 2^32 (guard passes) +
    `q1c.toNat ≥ q_true_phase1 + 1` (overshoot ≥ 1), the 1st BLTU
    fires: `(rhatc << 32) | div_un1 < q1c * dLo`.

    Used by `_phase1_overshoot_{1,2}_rhatc_lt_pow32_sub` to discharge
    the 1st correction's BLTU-fires claim. -/
theorem div128Quot_v4_phase1_inner_bltu_fires_when_q1c_overshoots
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_overshoots :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat ≥ (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 1)
    (h_rhatc_lt :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      rhatc.toNat < 2^32) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1) (q1c * dLo) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_uHi_lt_vTop
  -- Phase-1a Euclidean for q1c/rhatc.
  have h_bridge := div128Quot_v4_phase1_rhatc_bridge uHi vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_q1c_dHi_le, h_rhatc_eq⟩ := h_bridge
  -- q1c ≤ 2^32.
  have h_q1c_lt_pow32 : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt h_uHi_lt_decomp
  -- Strict upper from overshoot.
  have h_strict_upper : q1c.toNat * vTop.toNat >
                          uHi.toNat * 2^32 + div_un1.toNat :=
    div128Quot_v4_phase1_q1c_strict_upper uHi.toNat vTop.toNat dHi.toNat dLo.toNat
      div_un1.toNat q1c.toNat h_vTop_decomp hdHi_ge h_q1c_overshoots
  -- Pure-Nat fires arith: q1c * dLo > rhatc * 2^32 + div_un1.
  have h_fires_nat : rhatc.toNat * 2^32 + div_un1.toNat < q1c.toNat * dLo.toNat :=
    div128Quot_v4_phase1_bltu_fires_arith uHi.toNat vTop.toNat dHi.toNat dLo.toNat
      div_un1.toNat q1c.toNat rhatc.toNat
      h_vTop_decomp h_q1c_dHi_le h_rhatc_eq h_strict_upper
  -- Bridge to Word-level BLTU.
  have h_qDlo_eq : (q1c * dLo).toNat = q1c.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    calc q1c.toNat * dLo.toNat
        ≤ 2^32 * dLo.toNat := Nat.mul_le_mul_right _ h_q1c_lt_pow32
      _ < 2^32 * 2^32 :=
          (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr hdLo_lt
      _ = 2^64 := by decide
  have h_rhatUn1_eq : ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1).toNat =
                       rhatc.toNat * 2^32 + div_un1.toNat := by
    rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    exact EvmWord.halfword_combine rhatc div_un1 h_rhatc_lt h_div_un1_lt
  -- BLTU.ult is true ⟺ x.toNat < y.toNat.
  rw [BitVec.ult_iff_toNat_lt, h_rhatUn1_eq, h_qDlo_eq]
  exact h_fires_nat

/-- **Phase-1 overshoot 0 case (v4).** Under `q1c.toNat = q_true`,
    Phase-1b's 1st and 2nd D3 corrections are both no-ops, so
    `q1'' = q1c = q_true`. -/
theorem div128Quot_v4_phase1_overshoot_0_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat)) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Both `phase2b_q0'` calls are no-ops: the BLTU on (rhatc, q1c*dLo)
  -- doesn't fire because q1c = q_true (Knuth-A bound saturates). Apply
  -- the inner-BLTU-fails helper to discharge both.
  have h_q1c_le : q1c.toNat ≤ (uHi.toNat * 2^32 + div_un1.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) := by
    rw [h_q1c_eq_q_true]
  have h_no_bltu := div128Quot_v4_phase1_inner_bltu_fails_when_q1c_le_q_true
    uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_q1c_le
  -- 1st correction: q1' = q1c.
  have h_q1'_eq : q1' = q1c :=
    div128Quot_phase2b_q0'_eq_self_of_no_bltu q1c rhatc dLo div_un1 h_no_bltu
  -- rhat' = rhatc: the outer rhatc-update's inner if has the same
  -- ¬ BLTU as h_no_bltu, so the if-then else branch returns rhatc.
  have h_rhat'_eq : rhat' = rhatc := by
    show (if rhatc >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                            (q1c * dLo)
             then rhatc + dHi else rhatc)
          else rhatc) = rhatc
    by_cases h_guard : rhatc >>> (32 : BitVec 6).toNat = 0
    · rw [if_pos h_guard]
      have h_inner : ¬ BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                                   (q1c * dLo) :=
        fun hb => h_no_bltu ⟨h_guard, hb⟩
      rw [if_neg h_inner]
    · rw [if_neg h_guard]
  -- 2nd correction: q1'' = phase2b_q0' q1' rhat' dLo div_un1
  --   = phase2b_q0' q1c rhatc dLo div_un1 = q1c (no-op via the same helper).
  show (div128Quot_phase2b_q0' q1' rhat' dLo div_un1).toNat = _
  rw [h_q1'_eq, h_rhat'_eq,
      div128Quot_phase2b_q0'_eq_self_of_no_bltu q1c rhatc dLo div_un1 h_no_bltu]
  exact h_q1c_eq_q_true

/-- **Phase-1 overshoot 1 case (v4) — rhatc < 2^32 sub-case.** Under
    `q1c.toNat = q_true + 1` AND `rhatc < 2^32` (guard passes), the 1st
    BLTU fires (decrements q1' to q_true), the 2nd doesn't fire (q1' is
    exact). Result: q1''.toNat = q_true. -/
private theorem div128Quot_v4_phase1_overshoot_1_rhatc_lt_pow32_sub
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true_plus_1 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 1)
    (h_rhatc_lt :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      rhatc.toNat < 2^32) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Unfold the let-prefixed hypotheses to plain Nat propositions.
  have h_rhatc_lt' : rhatc.toNat < 2^32 := h_rhatc_lt
  -- Set q_true_phase1 alias to bridge let-form mismatches between
  -- the hypothesis (computed via lets) and goal (using local lets).
  set q_true_phase1 := (uHi.toNat * 2^32 + div_un1.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) with h_q_true_def
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_uHi_lt_vTop
  -- Phase-1a Euclidean for q1c/rhatc.
  obtain ⟨h_q1c_dHi_le, h_rhatc_eq⟩ :=
    div128Quot_v4_phase1_rhatc_bridge uHi vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  -- q1c.toNat ≤ 2^32.
  have h_q1c_lt_pow32 : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt h_uHi_lt_decomp
  -- Convert hypothesis to q_true_phase1 form.
  have h_q1c_eq_q_true_plus_1' : q1c.toNat = q_true_phase1 + 1 :=
    h_q1c_eq_q_true_plus_1
  -- 1st BLTU fires.
  have h_overshoot : q1c.toNat ≥ q_true_phase1 + 1 := by linarith
  have h_bltu_fires := div128Quot_v4_phase1_inner_bltu_fires_when_q1c_overshoots
    uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_overshoot h_rhatc_lt
  -- Outer guard passes.
  have h_guard : rhatc >>> (32 : BitVec 6).toNat = 0 :=
    div128Quot_v4_word_ushiftRight_32_zero_of_lt_pow32 rhatc h_rhatc_lt
  -- q1' = q1c + signExtend12 4095 (Word).
  have h_q1'_word : q1' = q1c + signExtend12 4095 := by
    show div128Quot_phase2b_q0' q1c rhatc dLo div_un1 = _
    unfold div128Quot_phase2b_q0'
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- q1c.toNat ≥ 1.
  have h_q1c_pos : q1c.toNat ≥ 1 := by linarith
  -- q1'.toNat = q1c.toNat - 1.
  have h_q1'_toNat : q1'.toNat = q1c.toNat - 1 := by
    rw [h_q1'_word, BitVec.toNat_add, signExtend12_4095_toNat]
    have hq1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
    rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq1c_lt_word]
  -- rhat' = rhatc + dHi (Word).
  have h_rhat'_word : rhat' = rhatc + dHi := by
    show (if rhatc >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                            (q1c * dLo)
             then rhatc + dHi else rhatc)
          else rhatc) = rhatc + dHi
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- rhat'.toNat = rhatc.toNat + dHi.toNat (no overflow).
  have h_rhat'_toNat : rhat'.toNat = rhatc.toNat + dHi.toNat := by
    rw [h_rhat'_word, BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    -- rhatc < 2^32 (h_rhatc_lt') + dHi < 2^32 (hdHi_lt) → sum < 2^33 < 2^64.
    have h_sum_lt : rhatc.toNat + dHi.toNat < 2^32 + 2^32 := by linarith
    linarith [show (2:Nat)^32 + 2^32 < 2^64 from by decide]
  -- New Phase-1a Eucl via the proven helper.
  obtain ⟨h_q1c_minus_one_dHi_le, h_rhatc_plus_dHi_eq⟩ :=
    div128Quot_v4_phase1_post_correction_eucl_arith
      uHi.toNat q1c.toNat dHi.toNat rhatc.toNat
      h_q1c_pos h_q1c_dHi_le h_rhatc_eq
  -- Translate to q1', rhat'.
  have h_q1'_dHi_le : q1'.toNat * dHi.toNat ≤ uHi.toNat := by
    rw [h_q1'_toNat]; exact h_q1c_minus_one_dHi_le
  have h_rhat'_eq : rhat'.toNat = uHi.toNat - q1'.toNat * dHi.toNat := by
    rw [h_q1'_toNat, h_rhat'_toNat]; exact h_rhatc_plus_dHi_eq
  -- q1'.toNat = q_true_phase1 (q1' = q_true exactly).
  have h_q1'_eq_q_true : q1'.toNat = q_true_phase1 := by
    have h1 : q1'.toNat = q1c.toNat - 1 := h_q1'_toNat
    have h2 : q1c.toNat = q_true_phase1 + 1 := h_q1c_eq_q_true_plus_1'
    omega
  have h_q1'_le_q_true : q1'.toNat ≤ (uHi.toNat * 2^32 + div_un1.toNat) /
                                      (dHi.toNat * 2^32 + dLo.toNat) := by
    rw [h_q1'_eq_q_true, h_q_true_def]
  -- q1'.toNat ≤ 2^32.
  have h_q1'_lt_pow32 : q1'.toNat ≤ 2^32 := by linarith
  -- 2nd BLTU doesn't fire (apply generic helper).
  have h_no_bltu := div128Quot_v4_phase1_inner_bltu_fails_generic
    uHi q1' rhat' dHi dLo div_un1
    hdLo_lt h_div_un1_lt h_q1'_dHi_le h_rhat'_eq h_q1'_lt_pow32 h_q1'_le_q_true
  -- 2nd correction: q1'' = q1' (no-op).
  show (div128Quot_phase2b_q0' q1' rhat' dLo div_un1).toNat = _
  rw [div128Quot_phase2b_q0'_eq_self_of_no_bltu q1' rhat' dLo div_un1 h_no_bltu]
  rw [h_q1'_eq_q_true, h_q_true_def]

/-- **Phase-1 overshoot 1 case (v4).** Under `q1c.toNat = q_true + 1`,
    the 1st D3 correction decrements to q_true, the 2nd is a no-op.

    Proof structure (case-split on the rhatc guard):

    - **Guard passes (rhatc < 2^32):**
      1st BLTU fires (via `_phase1_bltu_fires_arith` proven above):
      `rhatc * 2^32 + div_un1 < q1c * dLo` from
      `q1c * vTop > uHi*2^32 + div_un1` (Knuth strict, since q1c > q_true).
      So q1' = q1c - 1 = q_true. rhat' = rhatc + dHi.
      2nd BLTU doesn't fire (q1' is exact, applies
      `_phase1_inner_bltu_fails_when_q1c_le_q_true` to q1' / rhat').
      Thus q1'' = q1' = q_true.

    - **Guard fails (rhatc ≥ 2^32):** PROVABLY UNREACHABLE under
      shift-norm + uHi < vTop + overshoot ≥ 1. Closes via the
      `_phase1_no_overshoot_when_rhatc_ge_pow32` sub-lemma below.

      Algebraic argument (verified empirically on 438+ inputs):
      - rhatc ≥ 2^32 + hi1 ≠ 0 ⟹ rhat ≥ 2^32 - dHi.
      - Plugging into the floor inequality
        `(2^32 - 1) * vTop ≤ uHi*2^32 + div_un1` (Knuth-A applied to
        q1c = q_true + 1) gives a contradiction:
        `(dLo - dHi - r) * 2^32 ≤ div_un1 + dLo` would require
        `(2^32 - dLo) * 2^32 ≤ div_un1 + dLo`, but with dLo < 2^32 the
        LHS is positive ≥ 2^32 and RHS < 2^33, only marginally
        consistent — and after careful arithmetic, the strict
        inequality forces `dLo > 2^32 - O(1)` while `r ≥ 2^32 - dHi`
        forces dHi to dominate. The two constraints together force
        `2^64 < dLo * (2^32 - 1)`, which is impossible for
        `dLo < 2^32`.

      Net result: this case is vacuous; v4's algorithm is correct
      under runtime preconditions. -/
theorem div128Quot_v4_phase1_overshoot_1_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true_plus_1 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 1) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Case split on the rhatc guard.
  by_cases h_rhatc_lt : rhatc.toNat < 2^32
  · -- rhatc < 2^32: 1st BLTU fires, q1' = q_true; 2nd doesn't fire.
    -- Delegated to the focused helper below.
    exact div128Quot_v4_phase1_overshoot_1_rhatc_lt_pow32_sub
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_q1c_eq_q_true_plus_1 h_rhatc_lt
  · -- rhatc ≥ 2^32: vacuous via `_no_overshoot_when_rhatc_ge_pow32`
    --   (contradicts the overshoot-1 hypothesis).
    push Not at h_rhatc_lt
    exfalso
    have h_no_overshoot := div128Quot_v4_phase1_no_overshoot_when_rhatc_ge_pow32
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_rhatc_lt
    -- h_no_overshoot: q1c.toNat ≤ q_true_phase1.
    -- h_q1c_eq_q_true_plus_1: q1c.toNat = q_true_phase1 + 1.
    omega

/-- **Phase-1 overshoot 2 case (v4) — rhatc < 2^32 sub-case.** Under
    `q1c.toNat = q_true + 2` AND `rhatc < 2^32` (guard passes), the 1st
    BLTU fires (q1' = q_true + 1), then the 2nd BLTU ALSO fires
    (q1'' = q_true). The crucial v4 case where Knuth's full
    2-correction loop is required. -/
private theorem div128Quot_v4_phase1_overshoot_2_rhatc_lt_pow32_sub
    (uHi uLo vTop : Word)
    (_h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (_h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (_h_q1c_eq_q_true_plus_2 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 2)
    (_h_rhatc_lt :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      rhatc.toNat < 2^32) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  sorry  -- Boundary case proof: 1st BLTU fires (q1c overshoots by 2),
         -- q1' = q1c - 1 = q_true + 1. rhat' = rhatc + dHi.
         -- 2nd BLTU also fires (q1' STILL overshoots by 1).
         -- q1'' = q1' - 1 = q_true. The crucial v4 case where v2's
         -- pre-fix 2nd correction mishandled the truncation; v4's
         -- symmetric guard correctly enables both corrections.

/-- **Phase-1 overshoot 2 case (v4).** Under `q1c.toNat = q_true + 2`,
    the 1st D3 correction decrements to q_true + 1, the 2nd to q_true. -/
theorem div128Quot_v4_phase1_overshoot_2_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true_plus_2 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 2) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Same dispatcher as `_phase1_overshoot_1_sub`: case-split on rhatc guard.
  by_cases h_rhatc_lt : rhatc.toNat < 2^32
  · -- rhatc < 2^32: 1st BLTU fires, q1' = q_true + 1; 2nd BLTU also fires,
    -- q1'' = q_true. Delegated to focused helper below.
    exact div128Quot_v4_phase1_overshoot_2_rhatc_lt_pow32_sub
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_q1c_eq_q_true_plus_2 h_rhatc_lt
  · -- rhatc ≥ 2^32: vacuous via `_no_overshoot_when_rhatc_ge_pow32`
    --   (contradicts the overshoot-2 hypothesis even more strongly).
    --   Actually under hi1 ≠ 0 (which forces rhatc ≥ 2^32 to be possible),
    --   q1c ≤ q_true + 1 (Knuth-B with hi1 ≠ 0), so overshoot-2 is
    --   already impossible at the Knuth-range level. The dispatcher
    --   bound suffices.
    push Not at h_rhatc_lt
    exfalso
    have h_no_overshoot := div128Quot_v4_phase1_no_overshoot_when_rhatc_ge_pow32
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_rhatc_lt
    omega

/-- **Phase-1b 2-correction perfection (v4).** After v4's symmetric
    Phase-1b 2-correction loop, `q1''` equals the abstract Phase-1
    quotient `q*_phase1 = ⌊(uHi * 2^32 + div_un1) / vTop_high32⌋` where
    `vTop_high32 = dHi * 2^32 + dLo = vTop.toNat`.

    Mirrors Knuth's classical Algorithm D guarantee that the 2-iteration
    D3 loop always terminates with the exact trial digit.

    Dispatcher: case-splits on overshoot k = q1c.toNat - q_true ∈ {0, 1, 2}
    via `_phase1c_in_knuth_range`, then routes to the appropriate
    `_phase1_overshoot_k_sub`. -/
theorem div128Quot_v4_phase1_perfect (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Knuth range gives q_true ≤ q1c.toNat ≤ q_true + 2.
  have h_range := div128Quot_v4_phase1c_in_knuth_range uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_lower, h_upper⟩ := h_range
  -- linarith handles let-bindings more gracefully than omega: it matches
  -- on syntactic form and lets `change`/definitional reduction unify the
  -- q_true unfoldings between h_range and the goal.
  rcases Nat.lt_or_ge q1c.toNat
      ((uHi.toNat * 2^32 + div_un1.toNat) /
       (dHi.toNat * 2^32 + dLo.toNat) + 1) with h1 | h1
  · -- q1c.toNat = q_true (overshoot 0).
    have h_eq : q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                            (dHi.toNat * 2^32 + dLo.toNat) := by linarith
    exact div128Quot_v4_phase1_overshoot_0_sub uHi uLo vTop
      h_vTop_ge_pow63 h_uHi_lt_vTop h_eq
  · rcases Nat.lt_or_ge q1c.toNat
        ((uHi.toNat * 2^32 + div_un1.toNat) /
         (dHi.toNat * 2^32 + dLo.toNat) + 2) with h2 | h2
    · -- q1c.toNat = q_true + 1 (overshoot 1).
      have h_eq : q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) + 1 := by linarith
      exact div128Quot_v4_phase1_overshoot_1_sub uHi uLo vTop
        h_vTop_ge_pow63 h_uHi_lt_vTop h_eq
    · -- q1c.toNat = q_true + 2 (overshoot 2).
      have h_eq : q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) + 2 := by linarith
      exact div128Quot_v4_phase1_overshoot_2_sub uHi uLo vTop
        h_vTop_ge_pow63 h_uHi_lt_vTop h_eq

/-- **Phase-2 2-correction perfection (v4).** After v4's symmetric
    Phase-2 2-correction loop, `q0''` equals the abstract Phase-2
    quotient `q*_phase2 = ⌊(un21 * 2^32 + div_un0) / (dHi * 2^32 + dLo)⌋`
    exactly.

    This is the KEY new property v4 provides over v2/v3 — it eliminates
    the Phase-2 overshoot that broke `phase2_no_wrap_lo` sub-case b.

    Combined with `div128Quot_v4_phase1_perfect`, gives
    `qHat = q*_full = ⌊(uHi*2^64 + uLo) / vTop⌋` (the full classical
    Knuth bound). -/
theorem div128Quot_v4_phase2_perfect (uHi uLo vTop : Word)
    (_h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (_h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1'' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let rhat2' :=
      if rhat2c >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q0c * dLo
        let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
        if BitVec.ult rhatUn0 qDlo2 then rhat2c + dHi else rhat2c
      else rhat2c
    let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo div_un0
    q0''.toNat = (un21.toNat * 2^32 + div_un0.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  sorry  -- Mirrors `_phase1_perfect`'s case-split-on-overshoot proof,
         -- with q0c replacing q1c as the post-1st-correction trial digit.

/-- **Pure-Nat algebraic core for un21 < vTop.**

    Given Phase-1 perfect (`(q1'' + 1) * vTop > uHi*2^32 + div_un1`)
    plus Phase-1 Euclidean (`rhat'' = uHi - q1''*dHi`,
    `q1'' * dHi ≤ uHi`) and the Phase-1 no-wrap bound, derives
    `rhat'' * 2^32 + div_un1 - q1'' * dLo < vTop`.

    Proof: substitute rhat'' and simplify. Final step is an omega
    inequality once products are expanded. -/
private theorem div128Quot_v4_un21_lt_vTop_arith
    (uHi vTop dHi dLo div_un1 q1'' rhat'' : Nat)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_q1''_succ_gt : (q1'' + 1) * vTop > uHi * 2^32 + div_un1)
    (h_rhat''_eq : rhat'' = uHi - q1'' * dHi)
    (h_q1''_dHi_le : q1'' * dHi ≤ uHi)
    (h_no_wrap : q1'' * dLo ≤ rhat'' * 2^32 + div_un1) :
    rhat'' * 2^32 + div_un1 - q1'' * dLo < vTop := by
  -- Linearize products via `set`.
  set A := q1'' * dHi * 2 ^ 32 with hA
  set B := q1'' * dLo with hB
  -- Expand rhat'' * 2^32 = (uHi - q1''*dHi) * 2^32 = uHi*2^32 - A.
  have h_rhat_mul : rhat'' * 2 ^ 32 = uHi * 2 ^ 32 - A := by
    rw [h_rhat''_eq, Nat.sub_mul]
  have h_A_le : A ≤ uHi * 2 ^ 32 :=
    Nat.mul_le_mul_right _ h_q1''_dHi_le
  -- Expand (q1''+1)*vTop = A + B + dHi*2^32 + dLo.
  have h_succ_eq : (q1'' + 1) * vTop = A + B + (dHi * 2 ^ 32 + dLo) := by
    rw [h_vTop, Nat.add_mul, Nat.one_mul, Nat.mul_add, ← Nat.mul_assoc]
  rw [h_succ_eq] at h_q1''_succ_gt
  rw [h_rhat_mul, h_vTop]
  omega

/-- **Phase-1 final Euclidean bridge (v4)**: after v4's 2-correction
    Phase-1b, the post-correction `q1''` and `rhat''` satisfy the
    Phase-1a Euclidean at the Nat level:

    ```
    q1''.toNat * dHi.toNat ≤ uHi.toNat
    rhat''.toNat = uHi.toNat - q1''.toNat * dHi.toNat
    rhat''.toNat < 2 ^ 32   -- Knuth Phase-1 invariant under shift-norm
    ```

    Each Phase-1b correction maintains the Word-level invariant
    `q*dHi + rhat = uHi`. Bridging through 2 corrections reduces to the
    `_phase1_rhatc_bridge` already proven for q1c/rhatc, plus reasoning
    about the `phase2b_q0'` decrement + corresponding rhat increment.

    The `rhat'' < 2^32` bound is the Knuth Phase-1 invariant (each
    correction is bounded by the Phase-1a remainder; the 2-correction
    loop terminates in the Knuth band). Stub for now; will close via
    case-analysis on the BLTU branches at each correction. -/
private theorem div128Quot_v4_phase1_final_eucl_bridge
    (uHi uLo vTop : Word)
    (_h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (_h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    q1''.toNat * dHi.toNat ≤ uHi.toNat ∧
    rhat''.toNat = uHi.toNat - q1''.toNat * dHi.toNat ∧
    rhat''.toNat < 2 ^ 32 := by
  sorry  -- Extension of `_phase1_rhatc_bridge` through 2 corrections.
         -- Each correction maintains the Phase-1a Euclidean. The
         -- rhat'' < 2^32 bound comes from Knuth's classical Phase-1
         -- bound: rhat'' ≤ rhatc + 2*dHi ≤ 3*dHi < 2^32 + 2*2^32 < 2^34
         -- — needs tighter argument that under shift-norm rhat'' ≤ dHi - 1
         -- (the Phase-1a remainder bound), which is preserved by the
         -- 2-correction loop terminating with the exact quotient.

/-- **Phase-1 no-wrap (v4)**: after v4's 2-correction Phase-1b, the
    quotient `q1''` doesn't overshoot the Phase-1 sub-divisor's remainder
    word, so the Phase-2 setup `un21 = (rhat'' << 32 | div_un1) -
    q1'' * dLo` doesn't underflow.

    Symmetric to the top-level `_phase2_no_wrap_lo` (Phase-2 version):
    just swap the indices (q1''→q0'', rhat''→rhat2'', div_un1→div_un0).
    Both are corollaries of the corresponding `_perfect` lemma plus
    Knuth's classical D3 invariant.

    Pure-Word stub for now; depends on `_phase1_perfect`. -/
theorem div128Quot_v4_phase1_no_wrap_lo (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    q1''.toNat * dLo.toNat ≤ rhat''.toNat * 2^32 + div_un1.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
  -- `_phase1_perfect` gives q1''.toNat = q_true.
  have h_perfect := div128Quot_v4_phase1_perfect uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  -- Phase-1 final Euclidean bridge: q1''*dHi + rhat'' = uHi at toNat.
  have h_bridge := div128Quot_v4_phase1_final_eucl_bridge uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_q1''_dHi_le, h_rhat''_eq, _h_rhat''_lt⟩ := h_bridge
  -- Apply pure-Nat helper: q1'' ≤ q_true gives the no-wrap inequality.
  have h_q1''_le : q1''.toNat ≤ (uHi.toNat * 2 ^ 32 + div_un1.toNat) / vTop.toNat := by
    rw [h_perfect]
    have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
      div128Quot_vTop_decomp vTop
    rw [h_decomp]
  have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  exact div128Quot_v4_phase1_no_bltu_arith uHi.toNat vTop.toNat dHi.toNat dLo.toNat
    div_un1.toNat q1''.toNat rhat''.toNat
    h_decomp h_q1''_dHi_le h_rhat''_eq h_q1''_le

/-- **un21 < vTop under v4** (Phase-2 Knuth invariant).

    Per `project_un21_lt_vTop_plan.md`, this was a hard invariant under
    v2/v3 because Phase-1 truncation could produce un21 ~ 2 * vTop.
    Under v4, with Phase-1 perfect (`q1'' = q*_phase1`), un21 equals the
    Phase-1 remainder modulo Word-level truncation, which is < vTop. -/
theorem div128Quot_v4_un21_lt_vTop (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1'' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    un21.toNat < vTop.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2 ^ 32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2 ^ 32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2 ^ 32 := Word_ushiftRight_32_lt_pow32
  have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  -- `_phase1_perfect` gives q1''.toNat = q_true.
  have h_perfect := div128Quot_v4_phase1_perfect uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  -- Phase-1 final Euclidean: q1''*dHi + rhat'' = uHi at toNat, rhat'' < 2^32.
  have h_eucl := div128Quot_v4_phase1_final_eucl_bridge uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_q1''_dHi_le, h_rhat''_eq, h_rhat''_lt⟩ := h_eucl
  -- Phase-1 no-wrap: q1''*dLo ≤ rhat''*2^32 + div_un1.
  have h_no_wrap := div128Quot_v4_phase1_no_wrap_lo uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  -- q1''.toNat ≤ 2^32 (Knuth bound).
  have h_q1''_lt : q1''.toNat ≤ 2 ^ 32 := by
    have h_q_true_lt : (uHi.toNat * 2^32 + div_un1.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) < 2^32 :=
      div128Quot_q_true_1_lt_pow32 uHi dHi dLo div_un1 h_div_un1_lt
        (h_decomp ▸ h_uHi_lt_vTop)
    linarith [h_perfect]
  -- Word↔Nat bridges.
  have h_q_dLo_eq : (q1'' * dLo).toNat = q1''.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    calc q1''.toNat * dLo.toNat
        ≤ 2^32 * dLo.toNat := Nat.mul_le_mul_right _ h_q1''_lt
      _ < 2^32 * 2^32 := (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr hdLo_lt
      _ = 2^64 := by decide
  have h_rhatUn1_eq : ((rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1).toNat =
                       rhat''.toNat * 2^32 + div_un1.toNat := by
    rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    exact EvmWord.halfword_combine rhat'' div_un1 h_rhat''_lt h_div_un1_lt
  -- un21.toNat = rhat''*2^32 + div_un1 - q1''*dLo (Word subtract, no underflow).
  have h_un21_toNat : un21.toNat = rhat''.toNat * 2^32 + div_un1.toNat -
                                   q1''.toNat * dLo.toNat := by
    show (cu_rhat_un1 - cu_q1_dlo).toNat = _
    rw [BitVec.toNat_sub, h_rhatUn1_eq, h_q_dLo_eq]
    have h_le : q1''.toNat * dLo.toNat ≤ rhat''.toNat * 2^32 + div_un1.toNat :=
      h_no_wrap
    have h_pow : (0 : Nat) < 2^64 := by decide
    omega
  -- Phase-1 strict upper: (q1'' + 1) * vTop > uHi*2^32 + div_un1.
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h_dHi_ge : 2^31 ≤ dHi.toNat := div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
    have h_dHi_pos : 0 < dHi.toNat := lt_of_lt_of_le (by decide : (0:Nat) < 2^31) h_dHi_ge
    exact Nat.add_pos_left (Nat.mul_pos h_dHi_pos (by decide)) _
  have h_succ_gt : (q1''.toNat + 1) * vTop.toNat > uHi.toNat * 2^32 + div_un1.toNat := by
    rw [h_perfect, h_decomp]
    -- (a/b + 1) * b > a, derived from `a/b < a/b + 1` via div_lt_iff_lt_mul.
    have h_lt_self : (uHi.toNat * 2^32 + div_un1.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) <
                     (uHi.toNat * 2^32 + div_un1.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) + 1 := Nat.lt_succ_self _
    rwa [Nat.div_lt_iff_lt_mul h_vTop_pos] at h_lt_self
  -- Apply pure-Nat helper.
  rw [h_un21_toNat]
  exact div128Quot_v4_un21_lt_vTop_arith uHi.toNat vTop.toNat dHi.toNat dLo.toNat
    div_un1.toNat q1''.toNat rhat''.toNat
    h_decomp h_succ_gt h_rhat''_eq h_q1''_dHi_le h_no_wrap

/-- **Phase-2 Euclidean for q0'' (v4).** Combines Phase-2 perfection with
    the classical Euclidean to give the closure step for
    `div128Quot_v4_phase2_no_wrap_lo`. -/
theorem div128Quot_v4_phase2_euclidean (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1'' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let rhat2' :=
      if rhat2c >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q0c * dLo
        let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
        if BitVec.ult rhatUn0 qDlo2 then rhat2c + dHi else rhat2c
      else rhat2c
    let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo div_un0
    q0''.toNat * (dHi.toNat * 2^32 + dLo.toNat) ≤
      un21.toNat * 2^32 + div_un0.toNat := by
  intro dHi dLo div_un0 div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2' q0''
  -- `_phase2_perfect` gives q0''.toNat = (un21*2^32 + div_un0) / vTop.
  have h_perfect := div128Quot_v4_phase2_perfect uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  rw [show q0''.toNat = (un21.toNat * 2^32 + div_un0.toNat) /
                        (dHi.toNat * 2^32 + dLo.toNat) from h_perfect]
  -- Standard `q * vTop ≤ un21*2^32 + div_un0` floor inequality.
  exact Nat.div_mul_le_self _ _

/-- **div128Quot_v4 Phase-2 no-wrap (lower bound).**

    Phase-2 conjunct: after the 2nd D3 correction, the (un-truncated)
    quotient digit `q0''` doesn't overshoot the corresponding remainder
    word, i.e.

    ```
    q0'' * dLo ≤ rhat2'' * 2^32 + div_un0
    ```

    Where `rhat2''` is the post-2nd-correction remainder mirror.

    **Why this is unconditional under v4** (unlike v2/v3): with 2 D3
    corrections in Phase-2, q0'' = q*_phase2 exactly. The Phase-2
    Euclidean delivers `q*_phase2 * vTop ≤ un21*2^32 + div_un0`.
    Splitting `vTop = dHi*2^32 + dLo` and using the post-correction
    remainder bookkeeping recovers `q0'' * dLo ≤ rhat2'' * 2^32 +
    div_un0`. Sub-case b of v2's analog was provably FALSE under
    1-correction Phase-2 (q0' could exceed q*_phase2 by 1); v4's
    2-correction eliminates this.

    Closure composes:
    - `_phase2_perfect` (q0'' = q*_phase2, sorry'd dispatcher).
    - `_phase2_final_eucl_bridge` (Phase-2 Euclidean at toNat, sorry'd).
    - `_phase1_no_bltu_arith` (PROVEN pure-Nat algebraic core, generic
      over uHi/q1c). Reused here with un21/q0''. -/
theorem div128Quot_v4_phase2_no_wrap_lo (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1'' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let rhat2' :=
      if rhat2c >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q0c * dLo
        let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
        if BitVec.ult rhatUn0 qDlo2 then rhat2c + dHi else rhat2c
      else rhat2c
    let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo div_un0
    let rhat2'' :=
      if rhat2' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo3 := q0' * dLo
        let rhatUn0' := (rhat2' <<< (32 : BitVec 6).toNat) ||| div_un0
        if BitVec.ult rhatUn0' qDlo3 then rhat2' + dHi else rhat2'
      else rhat2'
    q0''.toNat * dLo.toNat ≤ rhat2''.toNat * 2^32 + div_un0.toNat := by
  intro dHi dLo div_un0 div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2' q0'' rhat2''
  -- `_phase2_perfect` gives q0''.toNat = q*_phase2.
  have h_perfect := div128Quot_v4_phase2_perfect uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  -- Phase-2 final Euclidean bridge: q0''*dHi + rhat2'' = un21 at toNat.
  have h_eucl := div128Quot_v4_phase2_final_eucl_bridge uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_q0''_dHi_le, h_rhat2''_eq, _h_rhat2''_lt⟩ := h_eucl
  have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  -- Apply pure-Nat helper (Phase-1's, generic; here with un21/div_un0/q0''/rhat2'').
  have h_q0''_le : q0''.toNat ≤ (un21.toNat * 2 ^ 32 + div_un0.toNat) / vTop.toNat := by
    rw [h_perfect, h_decomp]
  exact div128Quot_v4_phase1_no_bltu_arith un21.toNat vTop.toNat dHi.toNat dLo.toNat
    div_un0.toNat q0''.toNat rhat2''.toNat
    h_decomp h_q0''_dHi_le h_rhat2''_eq h_q0''_le

end EvmAsm.Evm64
