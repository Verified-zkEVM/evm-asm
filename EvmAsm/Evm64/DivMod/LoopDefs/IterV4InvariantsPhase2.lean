/-
  EvmAsm.Evm64.DivMod.LoopDefs.IterV4InvariantsPhase2

  Phase-2 invariants of `div128Quot_v4`. Split from
  `IterV4Invariants.lean` for the file-size guardrail (3312 lines
  combined).

  Depends on Phase-1 results (esp. `_un21_lt_vTop`) from
  `IterV4Invariants`.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.IterV4Invariants

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Phase-2c Knuth range (v4).** Mirror of `_phase1c_in_knuth_range`
    for Phase-2: the post-hi2-fix trial digit `q0c` sits in the
    Knuth range `[q*_phase2, q*_phase2 + 2]`.

    Proof: directly invoke the generic Word-level Knuth lemmas with
    `un21` as the dividend and `div_un0` as the lower limb. The
    runtime precondition `un21 < vTop` comes from the just-proven
    `_un21_lt_vTop`. -/
theorem div128Quot_v4_phase2c_in_knuth_range (uHi uLo vTop : Word)
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
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let q_true_phase2 := (un21.toNat * 2^32 + div_un0.toNat) /
                         (dHi.toNat * 2^32 + dLo.toNat)
    q_true_phase2 ≤ q0c.toNat ∧ q0c.toNat ≤ q_true_phase2 + 2 := by
  intro dHi dLo div_un0 div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 q0 hi2 q0c q_true_phase2
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un0_lt : div_un0.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_un21_lt_vTop : un21.toNat < vTop.toNat :=
    div128Quot_v4_un21_lt_vTop uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_un21_lt_decomp : un21.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_un21_lt_vTop
  refine ⟨?lower, ?upper⟩
  case lower =>
    exact div128Quot_q1c_ge_q_true_1 un21 dHi dLo div_un0
      hdHi_ne h_div_un0_lt h_un21_lt_decomp
  case upper =>
    have h_q0_le : q0.toNat ≤ q_true_phase2 + 2 :=
      div128Quot_q1_le_q_true_1_plus_two un21 dHi dLo div_un0
        hdHi_ne hdHi_ge hdLo_lt h_div_un0_lt h_un21_lt_decomp
    have h_q0c_le_q0 : q0c.toNat ≤ q0.toNat := by
      by_cases h_hi2 : hi2 = 0
      · show (if hi2 = 0 then q0 else q0 + signExtend12 4095).toNat ≤ q0.toNat
        rw [if_pos h_hi2]
      · have h_q0_ge : q0.toNat ≥ 2^32 := by
          by_contra h
          push Not at h
          apply h_hi2
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
              Nat.shiftRight_eq_div_pow]
          show q0.toNat / 2^32 = (0 : Word).toNat
          rw [Nat.div_eq_of_lt h]; rfl
        show (if hi2 = 0 then q0 else q0 + signExtend12 4095).toNat ≤ q0.toNat
        rw [if_neg h_hi2, BitVec.toNat_add, signExtend12_4095_toNat]
        have hq0_lt_word : q0.toNat - 1 < 2^64 := by have := q0.isLt; omega
        rw [show q0.toNat + (2^64 - 1) = (q0.toNat - 1) + 2^64 from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hq0_lt_word]
        omega
    linarith

/-- **Phase-2 overshoot 0 case (v4).** Mirror of
    `_phase1_overshoot_0_sub`: under `q0c.toNat = q*_phase2`, the 2
    Phase-2 corrections are no-ops, so `q0''.toNat = q*_phase2`.

    Proof: directly mirror `_phase1_overshoot_0_sub` but with
    `un21`/`div_un0` in place of `uHi`/`div_un1`. -/
private theorem div128Quot_v4_phase2_overshoot_0_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q0c_eq_q_true_phase2 :
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
      let hi2 := q0 >>> (32 : BitVec 6).toNat
      let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
      q0c.toNat = (un21.toNat * 2^32 + div_un0.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat)) :
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
  intro dHi dLo div_un0 div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2' q0''
  -- Standard Word-level facts.
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un0_lt : div_un0.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  -- un21 < vTop (Phase-2 Knuth invariant).
  have h_un21_lt_vTop : un21.toNat < vTop.toNat :=
    div128Quot_v4_un21_lt_vTop uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_un21_lt_decomp : un21.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_un21_lt_vTop
  -- Phase-2a Eucl on (q0c, rhat2c).
  obtain ⟨h_q0c_dHi_le, h_rhat2c_eq⟩ :=
    div128Quot_v4_hi_fix_eucl_generic un21 dHi hdHi_ge hdHi_lt
  -- q0c ≤ 2^32.
  have h_q0c_lt_pow32 : q0c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 un21 dHi dLo hdHi_ge hdLo_lt h_un21_lt_decomp
  -- q0c.toNat ≤ q*_phase2 (from h_q0c_eq_q_true_phase2).
  have h_q0c_le : q0c.toNat ≤ (un21.toNat * 2^32 + div_un0.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) := by
    rw [h_q0c_eq_q_true_phase2]
  -- 1st correction: BLTU doesn't fire (no-op).
  have h_no_bltu :=
    div128Quot_v4_phase1_inner_bltu_fails_generic un21 q0c rhat2c dHi dLo div_un0
      hdLo_lt h_div_un0_lt h_q0c_dHi_le h_rhat2c_eq h_q0c_lt_pow32 h_q0c_le
  -- q0' = q0c.
  have h_q0'_eq : q0' = q0c :=
    div128Quot_phase2b_q0'_eq_self_of_no_bltu q0c rhat2c dLo div_un0 h_no_bltu
  -- rhat2' = rhat2c.
  have h_rhat2'_eq : rhat2' = rhat2c := by
    show (if rhat2c >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                            (q0c * dLo)
             then rhat2c + dHi else rhat2c)
          else rhat2c) = rhat2c
    by_cases h_guard : rhat2c >>> (32 : BitVec 6).toNat = 0
    · rw [if_pos h_guard]
      have h_inner : ¬ BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                                   (q0c * dLo) :=
        fun hb => h_no_bltu ⟨h_guard, hb⟩
      rw [if_neg h_inner]
    · rw [if_neg h_guard]
  -- 2nd correction: q0'' = q0c (same no-op via the same helper).
  show (div128Quot_phase2b_q0' q0' rhat2' dLo div_un0).toNat = _
  rw [h_q0'_eq, h_rhat2'_eq,
      div128Quot_phase2b_q0'_eq_self_of_no_bltu q0c rhat2c dLo div_un0 h_no_bltu]
  exact h_q0c_eq_q_true_phase2

/-- **Phase-2 overshoot 1 case (v4) — rhat2c < 2^32 sub-case.** Under
    `q0c.toNat = q*_phase2 + 1` AND `rhat2c < 2^32` (guard passes), the
    1st BLTU fires (decrements q0' to q*_phase2), the 2nd doesn't fire
    (q0' is exact). Result: q0''.toNat = q*_phase2.

    Mirror of `_phase1_overshoot_1_rhatc_lt_pow32_sub` for Phase-2. -/
private theorem div128Quot_v4_phase2_overshoot_1_rhat2c_lt_pow32_sub
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q0c_eq_q_true_plus_1 :
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
      let hi2 := q0 >>> (32 : BitVec 6).toNat
      let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
      q0c.toNat = (un21.toNat * 2^32 + div_un0.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 1)
    (h_rhat2c_lt :
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
      let q0 := rv64_divu un21 dHi
      let rhat2 := un21 - q0 * dHi
      let hi2 := q0 >>> (32 : BitVec 6).toNat
      let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
      rhat2c.toNat < 2^32) :
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
  intro dHi dLo div_un0 div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2' q0''
  -- Unfold the let-prefixed hypotheses to plain Nat propositions.
  have h_rhat2c_lt' : rhat2c.toNat < 2^32 := h_rhat2c_lt
  -- Set q_true_phase2 alias to bridge let-form mismatches.
  set q_true_phase2 := (un21.toNat * 2^32 + div_un0.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) with h_q_true_def
  -- Standard Word-level facts.
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un0_lt : div_un0.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  -- un21 < dHi*2^32 + dLo.
  have h_un21_lt_vTop : un21.toNat < vTop.toNat :=
    div128Quot_v4_un21_lt_vTop uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_un21_lt_decomp : un21.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_un21_lt_vTop
  -- Phase-2a Eucl on (q0c, rhat2c).
  obtain ⟨h_q0c_dHi_le, h_rhat2c_eq⟩ :=
    div128Quot_v4_hi_fix_eucl_generic un21 dHi hdHi_ge hdHi_lt
  -- q0c.toNat ≤ 2^32.
  have h_q0c_lt_pow32 : q0c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 un21 dHi dLo hdHi_ge hdLo_lt h_un21_lt_decomp
  -- Convert hypothesis to q_true_phase2 form.
  have h_q0c_eq_q_true_plus_1' : q0c.toNat = q_true_phase2 + 1 :=
    h_q0c_eq_q_true_plus_1
  -- 1st BLTU fires (apply generic helper).
  have h_overshoot : q0c.toNat ≥ q_true_phase2 + 1 := by linarith
  have h_bltu_fires := div128Quot_v4_phase1_inner_bltu_fires_generic
    un21 q0c rhat2c dHi dLo div_un0
    hdHi_ge hdLo_lt h_div_un0_lt h_q0c_dHi_le h_rhat2c_eq h_rhat2c_lt'
    h_q0c_lt_pow32 h_overshoot
  -- Outer guard passes.
  have h_guard : rhat2c >>> (32 : BitVec 6).toNat = 0 :=
    div128Quot_v4_word_ushiftRight_32_zero_of_lt_pow32 rhat2c h_rhat2c_lt'
  -- q0' = q0c + signExtend12 4095 (Word).
  have h_q0'_word : q0' = q0c + signExtend12 4095 := by
    show div128Quot_phase2b_q0' q0c rhat2c dLo div_un0 = _
    unfold div128Quot_phase2b_q0'
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- q0c.toNat ≥ 1.
  have h_q0c_pos : q0c.toNat ≥ 1 := by linarith
  -- q0'.toNat = q0c.toNat - 1.
  have h_q0'_toNat : q0'.toNat = q0c.toNat - 1 := by
    rw [h_q0'_word, BitVec.toNat_add, signExtend12_4095_toNat]
    have hq0c_lt_word : q0c.toNat - 1 < 2^64 := by have := q0c.isLt; omega
    rw [show q0c.toNat + (2^64 - 1) = (q0c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq0c_lt_word]
  -- rhat2' = rhat2c + dHi (Word).
  have h_rhat2'_word : rhat2' = rhat2c + dHi := by
    show (if rhat2c >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                            (q0c * dLo)
             then rhat2c + dHi else rhat2c)
          else rhat2c) = rhat2c + dHi
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- rhat2'.toNat = rhat2c.toNat + dHi.toNat (no overflow).
  have h_rhat2'_toNat : rhat2'.toNat = rhat2c.toNat + dHi.toNat := by
    rw [h_rhat2'_word, BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    have h_sum_lt : rhat2c.toNat + dHi.toNat < 2^32 + 2^32 := by linarith
    linarith [show (2:Nat)^32 + 2^32 < 2^64 from by decide]
  -- New Phase-2a Eucl via the proven helper.
  obtain ⟨h_q0c_minus_one_dHi_le, h_rhat2c_plus_dHi_eq⟩ :=
    div128Quot_v4_phase1_post_correction_eucl_arith
      un21.toNat q0c.toNat dHi.toNat rhat2c.toNat
      h_q0c_pos h_q0c_dHi_le h_rhat2c_eq
  -- Translate to q0', rhat2'.
  have h_q0'_dHi_le : q0'.toNat * dHi.toNat ≤ un21.toNat := by
    rw [h_q0'_toNat]; exact h_q0c_minus_one_dHi_le
  have h_rhat2'_eq : rhat2'.toNat = un21.toNat - q0'.toNat * dHi.toNat := by
    rw [h_q0'_toNat, h_rhat2'_toNat]; exact h_rhat2c_plus_dHi_eq
  -- q0'.toNat = q_true_phase2 (q0' = q*_phase2 exactly).
  have h_q0'_eq_q_true : q0'.toNat = q_true_phase2 := by
    have h1 : q0'.toNat = q0c.toNat - 1 := h_q0'_toNat
    have h2 : q0c.toNat = q_true_phase2 + 1 := h_q0c_eq_q_true_plus_1'
    omega
  have h_q0'_le_q_true : q0'.toNat ≤ (un21.toNat * 2^32 + div_un0.toNat) /
                                      (dHi.toNat * 2^32 + dLo.toNat) := by
    rw [h_q0'_eq_q_true, h_q_true_def]
  -- q0'.toNat ≤ 2^32.
  have h_q0'_lt_pow32 : q0'.toNat ≤ 2^32 := by linarith
  -- 2nd BLTU doesn't fire (apply generic helper).
  have h_no_bltu := div128Quot_v4_phase1_inner_bltu_fails_generic
    un21 q0' rhat2' dHi dLo div_un0
    hdLo_lt h_div_un0_lt h_q0'_dHi_le h_rhat2'_eq h_q0'_lt_pow32 h_q0'_le_q_true
  -- 2nd correction: q0'' = q0' (no-op).
  show (div128Quot_phase2b_q0' q0' rhat2' dLo div_un0).toNat = _
  rw [div128Quot_phase2b_q0'_eq_self_of_no_bltu q0' rhat2' dLo div_un0 h_no_bltu]
  rw [h_q0'_eq_q_true, h_q_true_def]

/-- **Phase-2 overshoot 1 case (v4).** Mirror of
    `_phase1_overshoot_1_sub`: under `q0c.toNat = q*_phase2 + 1`,
    the 1st correction decrements to q*_phase2; 2nd is no-op.

    Dispatches on the rhat2c guard:
    - **rhat2c < 2^32**: canonical case via the focused sub-helper.
    - **rhat2c ≥ 2^32**: PROVABLY UNREACHABLE under shift-norm +
      uHi < vTop + overshoot ≥ 1, via the generic no-overshoot lemma. -/
private theorem div128Quot_v4_phase2_overshoot_1_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q0c_eq_q_true_plus_1 :
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
      let hi2 := q0 >>> (32 : BitVec 6).toNat
      let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
      q0c.toNat = (un21.toNat * 2^32 + div_un0.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 1) :
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
  intro dHi dLo div_un0 div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2' q0''
  -- Case split on the rhat2c guard.
  by_cases h_rhat2c_lt : rhat2c.toNat < 2^32
  · -- rhat2c < 2^32: canonical case via the focused sub-helper.
    exact div128Quot_v4_phase2_overshoot_1_rhat2c_lt_pow32_sub
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_q0c_eq_q_true_plus_1 h_rhat2c_lt
  · -- rhat2c ≥ 2^32: vacuous via the generic no-overshoot lemma.
    push Not at h_rhat2c_lt
    exfalso
    have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
    have h_div_un0_lt : div_un0.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
    have hdHi_ge : dHi.toNat ≥ 2^31 :=
      div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
    have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
    have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
      div128Quot_vTop_decomp vTop
    -- un21 < dHi*2^32 + dLo via `_un21_lt_vTop` + decomp.
    have h_un21_lt_vTop : un21.toNat < vTop.toNat :=
      div128Quot_v4_un21_lt_vTop uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop
    have h_un21_lt_decomp : un21.toNat < dHi.toNat * 2^32 + dLo.toNat := by
      rw [← h_vTop_decomp]; exact h_un21_lt_vTop
    -- Phase-2a Eucl on (q0c, rhat2c).
    obtain ⟨h_q0c_dHi_le, h_rhat2c_eq⟩ :=
      div128Quot_v4_hi_fix_eucl_generic un21 dHi hdHi_ge hdHi_lt
    have h_q0c_lt_pow32 : q0c.toNat ≤ 2^32 :=
      div128Quot_q1c_le_pow32 un21 dHi dLo hdHi_ge hdLo_lt h_un21_lt_decomp
    -- Apply generic no-overshoot.
    have h_no_overshoot :=
      div128Quot_v4_phase1_no_overshoot_when_rhat_ge_pow32_generic
        un21 q0c rhat2c dHi dLo div_un0
        hdHi_ge hdLo_lt h_q0c_dHi_le h_rhat2c_eq h_q0c_lt_pow32 h_rhat2c_lt
    -- h_no_overshoot: q0c.toNat ≤ q*_phase2.
    -- h_q0c_eq_q_true_plus_1: q0c.toNat = q*_phase2 + 1. Contradiction.
    -- linarith handles let-bindings more gracefully than omega.
    linarith

/-- **Phase-2 overshoot 2 case (v4) — rhat2c < 2^32 sub-case.** Under
    `q0c.toNat = q*_phase2 + 2` AND `rhat2c < 2^32` (guard passes), both
    Phase-2 BLTU checks fire (q0'' decrements twice from q*_phase2 + 2
    to q*_phase2). The crucial Phase-2 case where Knuth's full
    2-correction loop is required.

    Mirror of `_phase1_overshoot_2_rhatc_lt_pow32_sub` for Phase-2. -/
private theorem div128Quot_v4_phase2_overshoot_2_rhat2c_lt_pow32_sub
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q0c_eq_q_true_plus_2 :
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
      let hi2 := q0 >>> (32 : BitVec 6).toNat
      let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
      q0c.toNat = (un21.toNat * 2^32 + div_un0.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 2)
    (h_rhat2c_lt :
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
      let q0 := rv64_divu un21 dHi
      let rhat2 := un21 - q0 * dHi
      let hi2 := q0 >>> (32 : BitVec 6).toNat
      let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
      rhat2c.toNat < 2^32) :
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
  intro dHi dLo div_un0 div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2' q0''
  -- Unfold let-prefixed hypotheses.
  have h_rhat2c_lt' : rhat2c.toNat < 2^32 := h_rhat2c_lt
  -- Set q_true_phase2 alias.
  set q_true_phase2 := (un21.toNat * 2^32 + div_un0.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) with h_q_true_def
  -- Standard Word-level facts.
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un0_lt : div_un0.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_un21_lt_vTop : un21.toNat < vTop.toNat :=
    div128Quot_v4_un21_lt_vTop uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_un21_lt_decomp : un21.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_un21_lt_vTop
  -- Phase-2a Eucl on (q0c, rhat2c).
  obtain ⟨h_q0c_dHi_le, h_rhat2c_eq⟩ :=
    div128Quot_v4_hi_fix_eucl_generic un21 dHi hdHi_ge hdHi_lt
  -- q0c.toNat ≤ 2^32.
  have h_q0c_lt_pow32 : q0c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 un21 dHi dLo hdHi_ge hdLo_lt h_un21_lt_decomp
  -- Convert hypothesis to q_true_phase2 form.
  have h_q0c_eq_q_true_plus_2' : q0c.toNat = q_true_phase2 + 2 :=
    h_q0c_eq_q_true_plus_2
  -- 1st BLTU fires (overshoot ≥ 1).
  have h_overshoot_1st : q0c.toNat ≥ q_true_phase2 + 1 := by linarith
  have h_bltu_fires := div128Quot_v4_phase1_inner_bltu_fires_generic
    un21 q0c rhat2c dHi dLo div_un0
    hdHi_ge hdLo_lt h_div_un0_lt h_q0c_dHi_le h_rhat2c_eq h_rhat2c_lt'
    h_q0c_lt_pow32 h_overshoot_1st
  -- Outer guard passes.
  have h_guard : rhat2c >>> (32 : BitVec 6).toNat = 0 :=
    div128Quot_v4_word_ushiftRight_32_zero_of_lt_pow32 rhat2c h_rhat2c_lt'
  -- q0' = q0c + signExtend12 4095 (Word).
  have h_q0'_word : q0' = q0c + signExtend12 4095 := by
    show div128Quot_phase2b_q0' q0c rhat2c dLo div_un0 = _
    unfold div128Quot_phase2b_q0'
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  have h_q0c_pos : q0c.toNat ≥ 1 := by linarith
  -- q0'.toNat = q0c.toNat - 1.
  have h_q0'_toNat : q0'.toNat = q0c.toNat - 1 := by
    rw [h_q0'_word, BitVec.toNat_add, signExtend12_4095_toNat]
    have hq0c_lt_word : q0c.toNat - 1 < 2^64 := by have := q0c.isLt; omega
    rw [show q0c.toNat + (2^64 - 1) = (q0c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq0c_lt_word]
  -- rhat2' = rhat2c + dHi (Word).
  have h_rhat2'_word : rhat2' = rhat2c + dHi := by
    show (if rhat2c >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                            (q0c * dLo)
             then rhat2c + dHi else rhat2c)
          else rhat2c) = rhat2c + dHi
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- rhat2'.toNat = rhat2c.toNat + dHi.toNat (no overflow).
  have h_rhat2'_toNat : rhat2'.toNat = rhat2c.toNat + dHi.toNat := by
    rw [h_rhat2'_word, BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    have h_sum_lt : rhat2c.toNat + dHi.toNat < 2^32 + 2^32 := by linarith
    linarith [show (2:Nat)^32 + 2^32 < 2^64 from by decide]
  -- New Phase-2a Eucl via the proven helper.
  obtain ⟨h_q0c_minus_one_dHi_le, h_rhat2c_plus_dHi_eq⟩ :=
    div128Quot_v4_phase1_post_correction_eucl_arith
      un21.toNat q0c.toNat dHi.toNat rhat2c.toNat
      h_q0c_pos h_q0c_dHi_le h_rhat2c_eq
  have h_q0'_dHi_le : q0'.toNat * dHi.toNat ≤ un21.toNat := by
    rw [h_q0'_toNat]; exact h_q0c_minus_one_dHi_le
  have h_rhat2'_eq : rhat2'.toNat = un21.toNat - q0'.toNat * dHi.toNat := by
    rw [h_q0'_toNat, h_rhat2'_toNat]; exact h_rhat2c_plus_dHi_eq
  -- q0'.toNat = q_true_phase2 + 1 (still overshoots by 1).
  have h_q0'_eq : q0'.toNat = q_true_phase2 + 1 := by
    have h1 : q0'.toNat = q0c.toNat - 1 := h_q0'_toNat
    have h2 : q0c.toNat = q_true_phase2 + 2 := h_q0c_eq_q_true_plus_2'
    omega
  have h_q0'_lt_pow32 : q0'.toNat ≤ 2^32 := by linarith
  -- rhat2'.toNat < 2^32: derive via no_overshoot_generic contrapositive.
  have h_rhat2'_lt : rhat2'.toNat < 2^32 := by
    by_contra h
    push Not at h
    have h_no_over := div128Quot_v4_phase1_no_overshoot_when_rhat_ge_pow32_generic
      un21 q0' rhat2' dHi dLo div_un0
      hdHi_ge hdLo_lt h_q0'_dHi_le h_rhat2'_eq h_q0'_lt_pow32 h
    -- h_no_over : q0' ≤ q_true_phase2; h_q0'_eq : q0' = q_true_phase2 + 1.
    linarith
  -- 2nd BLTU fires.
  have h_q0'_overshoot : q0'.toNat ≥ (un21.toNat * 2^32 + div_un0.toNat) /
                                      (dHi.toNat * 2^32 + dLo.toNat) + 1 := by
    rw [h_q0'_eq]
  have h_bltu_fires_2 := div128Quot_v4_phase1_inner_bltu_fires_generic
    un21 q0' rhat2' dHi dLo div_un0
    hdHi_ge hdLo_lt h_div_un0_lt h_q0'_dHi_le h_rhat2'_eq
    h_rhat2'_lt h_q0'_lt_pow32 h_q0'_overshoot
  -- Outer guard passes for the 2nd correction (rhat2' < 2^32).
  have h_guard_2 : rhat2' >>> (32 : BitVec 6).toNat = 0 :=
    div128Quot_v4_word_ushiftRight_32_zero_of_lt_pow32 rhat2' h_rhat2'_lt
  -- q0'' = q0' + signExtend12 4095 = q0' - 1 (Word).
  have h_q0''_word : q0'' = q0' + signExtend12 4095 := by
    show div128Quot_phase2b_q0' q0' rhat2' dLo div_un0 = _
    unfold div128Quot_phase2b_q0'
    simp only [h_guard_2, if_true]
    rw [if_pos h_bltu_fires_2]
  have h_q0''_toNat : q0''.toNat = q0'.toNat - 1 := by
    rw [h_q0''_word, BitVec.toNat_add, signExtend12_4095_toNat]
    have hq0'_lt_word : q0'.toNat - 1 < 2^64 := by have := q0'.isLt; omega
    have h_q0'_pos : q0'.toNat ≥ 1 := by linarith
    rw [show q0'.toNat + (2^64 - 1) = (q0'.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq0'_lt_word]
  -- Conclude q0''.toNat = q_true_phase2.
  have h_q0''_eq : q0''.toNat = q_true_phase2 := by
    have h1 : q0''.toNat = q0'.toNat - 1 := h_q0''_toNat
    have h2 : q0'.toNat = q_true_phase2 + 1 := h_q0'_eq
    have h_q0'_pos : q0'.toNat ≥ 1 := by linarith
    omega
  rw [h_q0''_eq, h_q_true_def]

/-- **Phase-2 overshoot 2 case (v4).** Mirror of
    `_phase1_overshoot_2_sub`: under `q0c.toNat = q*_phase2 + 2`,
    both Phase-2 corrections fire, decrementing q0'' to q*_phase2.

    Dispatches on the rhat2c guard:
    - **rhat2c < 2^32**: canonical case via the focused sub-helper.
    - **rhat2c ≥ 2^32**: PROVABLY UNREACHABLE under shift-norm +
      uHi < vTop + overshoot ≥ 2 (vacuous via the generic
      no-overshoot lemma; overshoot 2 even more strongly contradicts
      `q0c ≤ q*_phase2`). -/
private theorem div128Quot_v4_phase2_overshoot_2_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q0c_eq_q_true_plus_2 :
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
      let hi2 := q0 >>> (32 : BitVec 6).toNat
      let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
      q0c.toNat = (un21.toNat * 2^32 + div_un0.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 2) :
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
  intro dHi dLo div_un0 div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2' q0''
  -- Same dispatcher pattern as `_phase2_overshoot_1_sub`.
  by_cases h_rhat2c_lt : rhat2c.toNat < 2^32
  · -- rhat2c < 2^32: canonical case via the focused sub-helper.
    exact div128Quot_v4_phase2_overshoot_2_rhat2c_lt_pow32_sub
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_q0c_eq_q_true_plus_2 h_rhat2c_lt
  · -- rhat2c ≥ 2^32: vacuous via the generic no-overshoot lemma.
    push Not at h_rhat2c_lt
    exfalso
    have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
    have h_div_un0_lt : div_un0.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
    have hdHi_ge : dHi.toNat ≥ 2^31 :=
      div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
    have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
    have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
      div128Quot_vTop_decomp vTop
    have h_un21_lt_vTop : un21.toNat < vTop.toNat :=
      div128Quot_v4_un21_lt_vTop uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop
    have h_un21_lt_decomp : un21.toNat < dHi.toNat * 2^32 + dLo.toNat := by
      rw [← h_vTop_decomp]; exact h_un21_lt_vTop
    obtain ⟨h_q0c_dHi_le, h_rhat2c_eq⟩ :=
      div128Quot_v4_hi_fix_eucl_generic un21 dHi hdHi_ge hdHi_lt
    have h_q0c_lt_pow32 : q0c.toNat ≤ 2^32 :=
      div128Quot_q1c_le_pow32 un21 dHi dLo hdHi_ge hdLo_lt h_un21_lt_decomp
    have h_no_overshoot :=
      div128Quot_v4_phase1_no_overshoot_when_rhat_ge_pow32_generic
        un21 q0c rhat2c dHi dLo div_un0
        hdHi_ge hdLo_lt h_q0c_dHi_le h_rhat2c_eq h_q0c_lt_pow32 h_rhat2c_lt
    -- h_no_overshoot: q0c ≤ q*_phase2; h_q0c_eq_q_true_plus_2: q0c = q*_phase2 + 2.
    linarith

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
    q0''.toNat = (un21.toNat * 2^32 + div_un0.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un0 div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2' q0''
  have h_range := div128Quot_v4_phase2c_in_knuth_range uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_lower, h_upper⟩ := h_range
  rcases Nat.lt_or_ge q0c.toNat
      ((un21.toNat * 2^32 + div_un0.toNat) /
       (dHi.toNat * 2^32 + dLo.toNat) + 1) with h1 | h1
  · -- q0c.toNat = q*_phase2 (overshoot 0).
    have h_eq : q0c.toNat = (un21.toNat * 2^32 + div_un0.toNat) /
                            (dHi.toNat * 2^32 + dLo.toNat) := by linarith
    exact div128Quot_v4_phase2_overshoot_0_sub uHi uLo vTop
      h_vTop_ge_pow63 h_uHi_lt_vTop h_eq
  · rcases Nat.lt_or_ge q0c.toNat
        ((un21.toNat * 2^32 + div_un0.toNat) /
         (dHi.toNat * 2^32 + dLo.toNat) + 2) with h2 | h2
    · -- q0c.toNat = q*_phase2 + 1 (overshoot 1).
      have h_eq : q0c.toNat = (un21.toNat * 2^32 + div_un0.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) + 1 := by linarith
      exact div128Quot_v4_phase2_overshoot_1_sub uHi uLo vTop
        h_vTop_ge_pow63 h_uHi_lt_vTop h_eq
    · -- q0c.toNat = q*_phase2 + 2 (overshoot 2).
      have h_eq : q0c.toNat = (un21.toNat * 2^32 + div_un0.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) + 2 := by linarith
      exact div128Quot_v4_phase2_overshoot_2_sub uHi uLo vTop
        h_vTop_ge_pow63 h_uHi_lt_vTop h_eq

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

/-- **Phase-2 final Euclidean bridge (v4)**: after Phase-2's 2-correction
    loop, `q0''` and `rhat2''` satisfy the Phase-2 Euclidean at toNat:

    ```
    q0''.toNat * dHi.toNat ≤ un21.toNat
    rhat2''.toNat = un21.toNat - q0''.toNat * dHi.toNat
    ```

    Mirror of `_phase1_final_eucl_bridge` for Phase-2. Closes via the
    proven generic helpers applied with D = un21. -/
private theorem div128Quot_v4_phase2_final_eucl_bridge
    (uHi uLo vTop : Word)
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
    q0''.toNat * dHi.toNat ≤ un21.toNat ∧
    rhat2''.toNat = un21.toNat - q0''.toNat * dHi.toNat := by
  intro dHi dLo div_un0 div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2'
        q0'' rhat2''
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  -- un21 < vTop (Phase-2 Knuth invariant).
  have h_un21_lt_vTop : un21.toNat < vTop.toNat :=
    div128Quot_v4_un21_lt_vTop uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_un21_lt_decomp : un21.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_un21_lt_vTop
  -- Phase-2a Eucl on (q0c, rhat2c).
  obtain ⟨h_q0c_dHi_le, h_rhat2c_eq⟩ :=
    div128Quot_v4_hi_fix_eucl_generic un21 dHi hdHi_ge hdHi_lt
  have h_q0c_lt_pow32 : q0c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 un21 dHi dLo hdHi_ge hdLo_lt h_un21_lt_decomp
  -- rhat2c < 2*dHi, so rhat2c + dHi < 3*dHi < 2^64.
  have h_rhat2c_lt_2_dHi : rhat2c.toNat < 2 * dHi.toNat :=
    div128Quot_v4_hi_fix_rc_lt_2_dHi_generic un21 dHi hdHi_ge hdHi_lt
  have h_rhat2c_dHi_no_overflow : rhat2c.toNat + dHi.toNat < 2^64 := by
    have h1 : rhat2c.toNat + dHi.toNat < 3 * dHi.toNat := by linarith
    have h2 : 3 * dHi.toNat < 3 * 2^32 := by linarith
    linarith [show (3 : Nat) * 2^32 < 2^64 from by decide]
  -- 1st correction: Eucl on (q0', rhat2').
  obtain ⟨h_q0'_dHi_le, h_rhat2'_eq⟩ :=
    div128Quot_v4_phase1_one_correction_eucl
      un21 q0c rhat2c dHi dLo div_un0
      hdHi_lt h_q0c_dHi_le h_rhat2c_eq h_q0c_lt_pow32 h_rhat2c_dHi_no_overflow
  -- q0'.toNat ≤ q0c.toNat ≤ 2^32 via the generic phase2b bound.
  have h_q0'_le_q0c : q0'.toNat ≤ q0c.toNat :=
    div128Quot_v4_phase1b_q_prime_le_q_generic q0c rhat2c dLo div_un0
  have h_q0'_lt_pow32 : q0'.toNat ≤ 2^32 := le_trans h_q0'_le_q0c h_q0c_lt_pow32
  -- rhat2'.toNat ≤ rhat2c.toNat + dHi.toNat via the generic step bound.
  have h_rhat2'_le : rhat2'.toNat ≤ rhat2c.toNat + dHi.toNat :=
    div128Quot_v4_phase1b_rhat_prime_le_step_generic q0c rhat2c dLo div_un0 dHi
      h_rhat2c_dHi_no_overflow
  -- rhat2'.toNat + dHi.toNat < 2^64.
  have h_rhat2'_dHi_no_overflow : rhat2'.toNat + dHi.toNat < 2^64 := by
    have : rhat2'.toNat + dHi.toNat ≤ rhat2c.toNat + 2 * dHi.toNat := by linarith
    have : rhat2c.toNat + 2 * dHi.toNat < 4 * dHi.toNat := by linarith
    have : 4 * dHi.toNat < 4 * 2^32 := by linarith
    linarith [show (4 : Nat) * 2^32 < 2^64 from by decide]
  -- 2nd correction: Eucl on (q0'', rhat2'').
  exact div128Quot_v4_phase1_one_correction_eucl
    un21 q0' rhat2' dHi dLo div_un0
    hdHi_lt h_q0'_dHi_le h_rhat2'_eq h_q0'_lt_pow32 h_rhat2'_dHi_no_overflow

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
  obtain ⟨h_q0''_dHi_le, h_rhat2''_eq⟩ := h_eucl
  have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  -- Apply pure-Nat helper (Phase-1's, generic; here with un21/div_un0/q0''/rhat2'').
  have h_q0''_le : q0''.toNat ≤ (un21.toNat * 2 ^ 32 + div_un0.toNat) / vTop.toNat := by
    rw [h_perfect, h_decomp]
  exact div128Quot_v4_phase1_no_bltu_arith un21.toNat vTop.toNat dHi.toNat dLo.toNat
    div_un0.toNat q0''.toNat rhat2''.toNat
    h_decomp h_q0''_dHi_le h_rhat2''_eq h_q0''_le


end EvmAsm.Evm64
