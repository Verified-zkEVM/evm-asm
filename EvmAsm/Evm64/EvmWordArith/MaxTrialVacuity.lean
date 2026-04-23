/-
  EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity

  Max-trial vacuity: proves `isMaxTrialN4_false_of_shift_nz` — under
  `hshift_nz : (clzResult b3).1 ≠ 0`, the max-trial condition cannot hold.

  This resolves the max+addback stack spec roadmap (Issue #61): all
  max-trial specs under `hshift_nz` describe dead runtime code, so any
  such stack spec with those hypotheses is vacuously provable via
  `exfalso; exact isMaxTrialN4_false_of_shift_nz … hbltu`.

  Theorems (from the 2026-04-20 discovery plan):
  - `clzStep_snd_ge` / `clzPipeline_snd_ge_pow62` (Step 1): pipeline.2 ≥ 2^62.
  - `b3_shifted_ge_pow63` (Step 2): `(b3 <<< clz(b3)).toNat ≥ 2^63`.
  - `u_top_lt_pow63_of_shift_nz` (Step 3): `u_top.toNat < 2^63` under shift ≠ 0.
  - `isMaxTrialN4_false_of_shift_nz` (final): composition.

  See `memory/project_max_trial_vacuous_discovery.md` for the full discovery.
-/

import EvmAsm.Evm64.EvmWordArith.CLZLemmas
import EvmAsm.Evm64.DivMod.Compose.FullPathN4

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CLZ step lower-bound invariant: if input's 2nd component is ≥ 2^(K - M_s)
    (the previous stage's K), the output's 2nd component is ≥ 2^K. Dual to the
    existing `clzStep_invariant_pres` / `clzStep_invariant_and_bound` upper-bound
    machinery.

    * Pass case (`p.2 >>> K ≠ 0`): output.2 = p.2, and `p.2 ≥ 2^K` follows directly
      from `ushiftRight_ne_zero_iff`.
    * Fail case (`p.2 >>> K = 0`): output.2 = `p.2 <<< M_s = p.2.toNat * 2^M_s`
      (no wrap, since `p.2 < 2^K` and `K + M_s = 64`). Then
      `p.2.toNat * 2^M_s ≥ 2^(K - M_s) * 2^M_s = 2^K`. -/
theorem clzStep_snd_ge (K M_s : Nat) (m : Word) (p : Word × Word)
    (hlb : p.2.toNat ≥ 2^(K - M_s))
    (hKMs : K + M_s = 64) (hKM_s_pos : 0 < M_s)
    (hMs_lt_K : M_s ≤ K) :
    (clzStep K M_s m p).2.toNat ≥ 2^K := by
  unfold clzStep; dsimp only []
  by_cases hpass : p.2 >>> K ≠ 0
  · rw [if_pos hpass]
    exact (ushiftRight_ne_zero_iff K).mp hpass
  · rw [if_neg hpass]
    push Not at hpass
    have hp2_lt : p.2.toNat < 2^K := (ushiftRight_eq_zero_iff K).mp hpass
    have hshifted : (p.2 <<< M_s).toNat = p.2.toNat * 2^M_s := by
      rw [BitVec.toNat_shiftLeft]
      simp only [Nat.shiftLeft_eq]
      have : p.2.toNat * 2^M_s < 2^64 := by
        have hpos : 0 < (2 : Nat)^M_s := by positivity
        have : p.2.toNat * 2^M_s < 2^K * 2^M_s := Nat.mul_lt_mul_right hpos |>.mpr hp2_lt
        rw [← pow_add, hKMs] at this; exact this
      exact Nat.mod_eq_of_lt this
    rw [hshifted]
    have hmul : 2^(K - M_s) * 2^M_s = 2^K := by
      rw [← pow_add]; congr 1; omega
    calc p.2.toNat * 2^M_s ≥ 2^(K - M_s) * 2^M_s :=
        Nat.mul_le_mul_right _ hlb
      _ = 2^K := hmul

/-- After all 5 pipeline stages, the value is ≥ 2^62. Threads `clzStep_snd_ge`
    through the K-chain 32 → 48 → 56 → 60 → 62. -/
theorem clzPipeline_snd_ge_pow62 {val : Word} (hval : val ≠ 0) :
    (clzPipeline val).2.toNat ≥ 2^62 := by
  unfold clzPipeline
  have h_init : ((0 : Word), val).2.toNat ≥ 2^0 := by
    simp
    exact Nat.one_le_iff_ne_zero.mpr (fun h => hval (BitVec.eq_of_toNat_eq (by simp [h])))
  have h0 := clzStep_snd_ge 32 32 (signExtend12 32) ((0 : Word), val)
    h_init (by norm_num) (by norm_num) (by norm_num)
  have h1 := clzStep_snd_ge 48 16 (signExtend12 16)
    (clzStep 32 32 (signExtend12 32) ((0 : Word), val))
    h0 (by norm_num) (by norm_num) (by norm_num)
  have h2 := clzStep_snd_ge 56 8 (signExtend12 8)
    (clzStep 48 16 (signExtend12 16) (clzStep 32 32 (signExtend12 32) ((0 : Word), val)))
    h1 (by norm_num) (by norm_num) (by norm_num)
  have h3 := clzStep_snd_ge 60 4 (signExtend12 4)
    (clzStep 56 8 (signExtend12 8)
      (clzStep 48 16 (signExtend12 16) (clzStep 32 32 (signExtend12 32) ((0 : Word), val))))
    h2 (by norm_num) (by norm_num) (by norm_num)
  exact clzStep_snd_ge 62 2 (signExtend12 2)
    (clzStep 60 4 (signExtend12 4)
      (clzStep 56 8 (signExtend12 8)
        (clzStep 48 16 (signExtend12 16) (clzStep 32 32 (signExtend12 32) ((0 : Word), val)))))
    h3 (by norm_num) (by norm_num) (by norm_num)

/-- For `shift.toNat ∈ [1, 63]`, the value `a3 >>> (64 - shift)` is bounded above
    by `2^63`. Concretely, the max-trial algorithm's `u_top` lies in `[0, 2^63)`
    under a non-zero shift.

    Proof chain: `signExtend12 0 - shift = 2^64 - shift.toNat` (Word), its `%64 =
    64 - shift.toNat`, then `BitVec.toNat_ushiftRight` + power split. -/
theorem u_top_lt_pow63_of_shift_nz (a3 shift : Word)
    (h1 : 1 ≤ shift.toNat) (h63 : shift.toNat ≤ 63) :
    (a3 >>> ((signExtend12 (0 : BitVec 12) - shift).toNat % 64)).toNat < 2^63 := by
  have h0 : (signExtend12 (0 : BitVec 12) : Word) = 0 := by decide
  rw [h0]
  have hshift_toNat : ((0 : Word) - shift).toNat = 2^64 - shift.toNat := by
    rw [BitVec.toNat_sub]
    simp
    omega
  rw [hshift_toNat]
  have hmod : (2^64 - shift.toNat) % 64 = 64 - shift.toNat := by
    have : 2^64 - shift.toNat = (2^64 - 64) + (64 - shift.toNat) := by omega
    rw [this, Nat.add_mod]
    have : (2^64 - 64) % 64 = 0 := by decide
    rw [this]
    simp
    omega
  rw [hmod]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have ha3 : a3.toNat < 2^64 := a3.isLt
  have hsplit : (2 : Nat)^64 = 2^shift.toNat * 2^(64 - shift.toNat) := by
    rw [← pow_add, show shift.toNat + (64 - shift.toNat) = 64 from by omega]
  have hlt_pow_shift : a3.toNat / 2^(64 - shift.toNat) < 2^shift.toNat := by
    rw [hsplit, Nat.mul_comm] at ha3
    exact Nat.div_lt_of_lt_mul ha3
  exact lt_of_lt_of_le hlt_pow_shift (Nat.pow_le_pow_right (by norm_num) h63)

/-- After left-shifting `b3` by `(clzResult b3).1` bits, the result is at least `2^63`.
    This is Step 2 of the vacuity chain. Uses case analysis on stage 5 (pass/fail):
    * Pass: clzResult.1 = pipeline.1, and b3 << pipeline.1 = pipeline.2 ≥ 2^63
      (from the pass condition `pipeline.2 >>> 63 ≠ 0`).
    * Fail: clzResult.1 = pipeline.1 + 1, and b3 << (pipeline.1 + 1) = 2 * pipeline.2
      ≥ 2 * 2^62 = 2^63 (by Step 1). -/
theorem b3_shifted_ge_pow63 {b3 : Word} (hb3nz : b3 ≠ 0) :
    (b3 <<< ((clzResult b3).1.toNat % 64)).toNat ≥ 2^63 := by
  obtain ⟨hinv, hcount⟩ := clzPipeline_invariant b3
  have := clzPipeline_snd_ge_pow62 hb3nz
  have hsnd_lt : (clzPipeline b3).2.toNat < 2^64 := (clzPipeline b3).2.isLt
  rw [clzResult_fst_eq]
  by_cases h5 : (clzPipeline b3).2 >>> 63 ≠ 0
  · rw [if_pos h5]
    have hmod : (clzPipeline b3).1.toNat % 64 = (clzPipeline b3).1.toNat := by omega
    rw [hmod]
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hinv]
    rw [Nat.mod_eq_of_lt hsnd_lt]
    exact toNat_ge_of_ushiftRight_63 h5
  · simp only [h5, if_false]
    push Not at h5
    have hp2_lt : (clzPipeline b3).2.toNat < 2^63 :=
      (ushiftRight_eq_zero_iff 63).mp h5
    have hsum_toNat :
        ((clzPipeline b3).1 + signExtend12 (1 : BitVec 12)).toNat =
        (clzPipeline b3).1.toNat + 1 := by
      rw [BitVec.toNat_add]
      have : (signExtend12 (1 : BitVec 12) : Word).toNat = 1 := by decide
      rw [this]
      exact Nat.mod_eq_of_lt (by omega : (clzPipeline b3).1.toNat + 1 < 2^64)
    rw [hsum_toNat]
    have hmod : ((clzPipeline b3).1.toNat + 1) % 64 = (clzPipeline b3).1.toNat + 1 := by omega
    rw [hmod]
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have hinv_doubled : b3.toNat * 2^((clzPipeline b3).1.toNat + 1) =
        2 * (clzPipeline b3).2.toNat := by
      rw [pow_succ, ← Nat.mul_assoc, hinv]; ring
    rw [hinv_doubled]
    rw [Nat.mod_eq_of_lt (by linarith : 2 * (clzPipeline b3).2.toNat < 2^64)]
    linarith

/-- **Max-trial is vacuously false under `hshift_nz`.** Combining Steps 2 and 3:
    `u_top.toNat < 2^63 ≤ (b3 <<< shift).toNat ≤ b3'.toNat` (the last inequality
    by OR monotonicity), so `BitVec.ult u4 b3'` holds, i.e., `¬ isMaxTrialN4`. -/
theorem isMaxTrialN4_false_of_shift_nz (a3 b2 b3 : Word)
    (hb3nz : b3 ≠ 0) (hshift_nz : (clzResult b3).1 ≠ 0) :
    ¬ isMaxTrialN4 a3 b2 b3 := by
  unfold isMaxTrialN4
  simp only [not_not]
  have h_shift_le := clzResult_fst_toNat_le b3
  have h_shift_pos : 1 ≤ (clzResult b3).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b3).1.toNat with h | h
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h_u4 := u_top_lt_pow63_of_shift_nz a3 (clzResult b3).1 h_shift_pos h_shift_le
  have h_b3_shifted := b3_shifted_ge_pow63 hb3nz
  have h_or_ge : (((b3 <<< ((clzResult b3).1.toNat % 64))) |||
                   (b2 >>> ((signExtend12 (0 : BitVec 12) -
                     (clzResult b3).1).toNat % 64))).toNat ≥
                 (b3 <<< ((clzResult b3).1.toNat % 64)).toNat := by
    rw [BitVec.toNat_or]
    exact Nat.left_le_or
  have h_lt : (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)).toNat <
              (b3 <<< ((clzResult b3).1.toNat % 64) |||
                b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)).toNat :=
    Nat.lt_of_lt_of_le h_u4 (le_trans h_b3_shifted h_or_ge)
  exact (EvmWord.ult_iff).mpr h_lt

end EvmAsm.Evm64
