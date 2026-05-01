/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackV2Bounds

  Pure-Nat / val256 / Knuth-B `div128Quot_v2` bounds and helper lemmas.
  Extracted from Spec/CallAddback.lean per #1078 / beads evm-asm-q62k to
  trim the over-cap CallAddback.lean.

  Contents (15 theorems, ~1135 lines, all leaf-level relative to the
  Phase-1 div-invariant cluster that still lives in CallAddback.lean):

  - `div128Quot_v2_q1_prime_prime_le_q1_prime`
  - `div128Quot_v2_q1_prime_prime_dLo_no_wrap`
  - `div128Quot_v2_rhat_prime_lt_2dHi_under_guard`
  - `div128Quot_v2_rhat_prime_prime_lt_pow33`
  - `div128Quot_v2_toNat_eq_strict`
  - `div128Quot_v2_un21_toNat`
  - `div128Quot_v2_un21_toNat_case`
  - `knuth_compose_qHat_vTop_le_nat_v2_untruncated`
  - `div128Quot_v2_un21_toNat_untruncated`
  - `div128Quot_v2_qHat_vTop_le_full`
  - `div128Quot_v2_qHat_vTop_le_full_untruncated`
  - `div128Quot_v2_le_val256_div_plus_two`
  - `div128Quot_v2_le_val256_div_plus_two_untruncated`
  - `div128Quot_v2_le_5limb_shifted_div_plus_two_untruncated`
  - `div128Quot_v2_phase1c_in_knuth_range_under_runtime`

  No proof changes: this is a pure structural move. The downstream
  Phase-1 cluster in CallAddback.lean (overshoot_{0,1,2}_sub plus
  div128Quot_v2_phase1_div_invariant_under_runtime) imports this module
  via the existing CallAddback.lean prelude.

  Issue #1337 algorithm fix migration (decomposition surface).
-/

import EvmAsm.Evm64.DivMod.Spec.CallSkip
import EvmAsm.Evm64.DivMod.Spec.CallAddbackPureNat
import EvmAsm.Evm64.DivMod.Spec.CallAddbackPhase1Stubs
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.AlgDefs
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.AlgEuclideans
import EvmAsm.Evm64.DivMod.Shift0Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)
open EvmAsm.Rv64.Tactics

/-- **`q1'' ≤ q1'`**: the 2nd D3 correction only decreases the trial
    quotient (or leaves it unchanged), never increases it.

    Combined with v1's `div128Quot_q1_prime_le_pow32_plus_one` (which
    gives `q1'.toNat ≤ 2^32 + 1`), this directly yields
    `q1''.toNat ≤ 2^32 + 1`, the no-wrap precondition needed by
    `div128Quot_v2_un21_toNat_case`.

    Proof structure (3-way case split on the guard + check):
    - Guard taken (rhat' >> 32 ≠ 0): q1'' = q1' (refl).
    - Guard fall-through:
      * Check fires: q1'' = q1' - 1, so q1''.toNat ≤ q1'.toNat.
      * Check doesn't fire: q1'' = q1' (refl).

    Issue #1337 algorithm fix migration. -/
theorem div128Quot_v2_q1_prime_prime_le_q1_prime
    (q1' rhat' dLo div_un1 : Word) :
    (div128Quot_phase2b_q0' q1' rhat' dLo div_un1).toNat ≤ q1'.toNat := by
  unfold div128Quot_phase2b_q0'
  by_cases h_guard : rhat' >>> (32 : BitVec 6).toNat = 0
  · rw [if_pos h_guard]
    by_cases h_check :
        BitVec.ult ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1) (q1' * dLo)
    · -- q1'' = q1' + signExtend12 4095 = q1' - 1.
      rw [if_pos h_check]
      have h_q1'_pos : q1'.toNat ≥ 1 :=
        div128Quot_phase1b_check_implies_q1c_pos q1' dLo _ h_check
      -- (q1' + signExtend12 4095).toNat = q1'.toNat - 1 ≤ q1'.toNat.
      rw [BitVec.toNat_add, signExtend12_4095_toNat]
      have h_eq : q1'.toNat + (2^64 - 1) = (q1'.toNat - 1) + 2^64 := by omega
      rw [h_eq, Nat.add_mod_right]
      have hq1'_lt_word : q1'.toNat - 1 < 2^64 := by have := q1'.isLt; omega
      rw [Nat.mod_eq_of_lt hq1'_lt_word]
      omega
    · rw [if_neg h_check]
  · rw [if_neg h_guard]

/-- **`q1'' * dLo` no-wrap for `div128Quot_v2`** — v2 analog of v1's
    `div128Quot_q1_prime_dLo_no_wrap` from `Div128FinalAssembly.lean:52`.

    Combines `div128Quot_v2_q1_prime_prime_le_q1_prime` (q1'' ≤ q1')
    with v1's `div128Quot_q1_prime_le_pow32_plus_one` (q1' ≤ 2^32 + 1)
    to derive q1''.toNat ≤ 2^32 + 1, hence q1'' * dLo doesn't overflow.

    Issue #1337 algorithm fix migration. -/
theorem div128Quot_v2_q1_prime_prime_dLo_no_wrap
    (uHi dHi dLo rhatUn1 div_un1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    (q1'' * dLo).toNat = q1''.toNat * dLo.toNat := by
  intro q1 rhat hi1 q1c rhatc q1' rhat' q1''
  have h_q1'_le : q1'.toNat ≤ 2^32 + 1 :=
    div128Quot_q1_prime_le_pow32_plus_one uHi dHi dLo rhatUn1
      hdHi_ge hdLo_lt huHi_lt_vTop
  have h_q1''_le_q1' : q1''.toNat ≤ q1'.toNat :=
    div128Quot_v2_q1_prime_prime_le_q1_prime q1' rhat' dLo div_un1
  have h_q1''_le : q1''.toNat ≤ 2^32 + 1 := le_trans h_q1''_le_q1' h_q1'_le
  -- q1''.toNat * dLo.toNat < 2^64.
  have h_mul_lt : q1''.toNat * dLo.toNat < 2^64 := by
    have h1 : q1''.toNat * dLo.toNat ≤ (2^32 + 1) * (2^32 - 1) := by
      have hdLo_le : dLo.toNat ≤ 2^32 - 1 := by omega
      exact Nat.mul_le_mul h_q1''_le hdLo_le
    have h2 : (2^32 + 1) * (2^32 - 1) = 2^64 - 1 := by decide
    omega
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h_mul_lt]

/-- **Helper: under v2's 2nd D3 guard fall-through, `rhat' < 2 * dHi`.**

    When the 2nd D3 correction is reachable (guard `rhat' >> 32 = 0`
    fires, meaning `rhat' < 2^32`), combined with the call-trial
    precondition `dHi ≥ 2^31`, we get `rhat' < 2 * dHi` automatically.

    Proof: rhat' < 2^32 (from h_guard) and dHi ≥ 2^31 ⟹ 2 * dHi ≥ 2^32
    > rhat'.

    This is the concrete form of the `h_rhat'_lt` precondition used by
    `div128Quot_v2_phase1b_2nd_post` — automatically dischargeable when
    the 2nd D3 actually fires.

    Issue #1337 algorithm fix migration. -/
theorem div128Quot_v2_rhat_prime_lt_2dHi_under_guard
    (dHi rhat' : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (h_guard : rhat' >>> (32 : BitVec 6).toNat = 0) :
    rhat'.toNat < 2 * dHi.toNat := by
  -- h_guard says (rhat' >> 32).toNat = 0, which means rhat'.toNat < 2^32.
  have h_rhat'_lt_pow32 : rhat'.toNat < 2^32 := by
    have h := congrArg BitVec.toNat h_guard
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h
    -- h : rhat'.toNat / 2^32 = 0.
    have h_word : rhat'.toNat < 2^64 := rhat'.isLt
    omega
  -- 2 * dHi ≥ 2 * 2^31 = 2^32 > rhat'.
  omega

/-- **Phase 1b 2nd D3 weak tightness** — bound `rhat'' < 2^33`.

    Weaker than `rhat'' < 2 * dHi` (which is provably FALSE in Case 2
    when dHi is small): when 2nd D3 fires with rhat' < 2^32 ≤ 2 * dHi,
    we have rhat'' = rhat' + dHi < 2^32 + 2^32 = 2^33.

    The weaker bound `< 2^33` is enough for Phase 1's `rhat'' * 2^32 <
    2^65`, which combined with `div_un1 < 2^32` and `q1'' * dLo` close
    to `rhat'' * 2^32 + div_un1` (Knuth-D correctness) gives the
    no_wrap_untruncated upper-bound conjunct.

    Issue #1337 algorithm fix migration. Path 3 sub-lemma. -/
theorem div128Quot_v2_rhat_prime_prime_lt_pow33
    (uHi dHi q1' rhat' dLo div_un1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (_h_post_1st : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat)
    (h_rhat'_lt : rhat'.toNat < 2 * dHi.toNat) :
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    rhat''.toNat < 2^33 := by
  intro rhat''
  by_cases h_guard : rhat' >>> (32 : BitVec 6).toNat = 0
  · -- Guard taken: rhat' < 2^32 from the guard.
    have h_rhat'_lt_pow32 : rhat'.toNat < 2^32 := by
      have h := congrArg BitVec.toNat h_guard
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h
      have h_word : rhat'.toNat < 2^64 := rhat'.isLt
      omega
    by_cases h_check : BitVec.ult ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1)
                                    (q1' * dLo)
    · -- Check fires: rhat'' = rhat' + dHi.
      have h_rhat'' : rhat'' = rhat' + dHi := by
        show (if rhat' >>> (32 : BitVec 6).toNat = 0 then _ else rhat') = _
        rw [if_pos h_guard, if_pos h_check]
      rw [h_rhat'']
      -- (rhat' + dHi).toNat ≤ rhat'.toNat + dHi.toNat < 2^32 + 2^32 = 2^33.
      have h_sum : (rhat' + dHi).toNat ≤ rhat'.toNat + dHi.toNat := by
        rw [BitVec.toNat_add]; exact Nat.mod_le _ _
      omega
    · -- Check doesn't fire: rhat'' = rhat'. So rhat'' < 2^32 < 2^33.
      have h_rhat'' : rhat'' = rhat' := by
        show (if rhat' >>> (32 : BitVec 6).toNat = 0 then _ else rhat') = _
        rw [if_pos h_guard, if_neg h_check]
      rw [h_rhat'']; omega
  · -- Guard not taken: rhat'' = rhat'. From h_rhat'_lt: rhat' < 2 * dHi < 2^33.
    have h_rhat'' : rhat'' = rhat' := by
      show (if rhat' >>> (32 : BitVec 6).toNat = 0 then _ else rhat') = _
      rw [if_neg h_guard]
    rw [h_rhat'']; omega

/-- **Output formula for `div128Quot_v2` via halfword combine** — v2 analog
    of v1's `div128Quot_toNat_eq_strict` from `Div128FinalAssembly.lean:778`.

    States `(div128Quot_v2 uHi uLo vTop).toNat = q1''.toNat * 2^32 + q0'.toNat`,
    i.e., the v2 algorithm's output decomposes into the two halfwords
    via the OR-shift combine at the end.

    Same algebraic structure as v1, but using `q1''` (post-2nd-D3) instead
    of `q1'` (post-1st-D3). The OR-shift combine `(q1'' << 32) ||| q0'`
    requires `q0' < 2^32` (otherwise OR overlap).

    **Why needed**: this is the only substantive piece remaining for
    `div128Quot_v2_qHat_vTop_le`. Once closed, qHat_vTop_le falls out by
    direct composition with the 5 already-proven v2 sub-lemmas + reusable
    v1 infrastructure (knuth_compose_qHat_vTop_le_nat_v2).

    Issue #1337 algorithm fix migration. -/
theorem div128Quot_v2_toNat_eq_strict (uHi uLo vTop : Word)
    (_hdHi_ge : (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (_hdHi_lt : (vTop >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (_hdLo_lt : ((vTop <<< (32 : BitVec 6).toNat) >>>
                 (32 : BitVec 6).toNat).toNat < 2^32)
    (_huHi_lt_vTop : uHi.toNat <
      (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
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
    q0'.toNat < 2^32 →
    (div128Quot_v2 uHi uLo vTop).toNat = q1''.toNat * 2^32 + q0'.toNat := by
  intro dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        q1'' rhat'' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' hq0
  -- Output is (q1'' << 32) ||| q0' (per div128Quot_v2 def).
  show ((q1'' <<< (32 : BitVec 6).toNat) ||| q0').toNat = q1''.toNat * 2^32 + q0'.toNat
  -- Use halfword_combine_mod to get the modular form, then drop the mod
  -- via q1''.toNat < 2^32.
  have h_q1''_le_q1' : q1''.toNat ≤ q1'.toNat :=
    div128Quot_v2_q1_prime_prime_le_q1_prime q1' rhat' dLo div_un1
  have h_q1'_lt : q1'.toNat < 2^32 :=
    div128Quot_q1_prime_lt_pow32 uHi dHi dLo uLo
      (by simpa using _hdHi_ge) (by simpa using _hdHi_lt)
      (by simpa using _hdLo_lt) (by simpa using _huHi_lt_vTop)
  have h_q1''_lt : q1''.toNat < 2^32 := lt_of_le_of_lt h_q1''_le_q1' h_q1'_lt
  rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
  rw [halfword_combine_mod q1'' q0' hq0, Nat.mod_eq_of_lt h_q1''_lt]

/-- **Modular form of un21 for `div128Quot_v2`** — v2 analog of v1's
    `div128Quot_un21_toNat` from `Div128FinalAssembly.lean:167`.

    States `un21.toNat = (A + 2^64 - B) % 2^64` where:
    - `A = (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat`
    - `B = q1''.toNat * dLo.toNat`

    Proof composes:
    - `div128Quot_cu_rhat_un1_toNat` (existing v1, generic on rhat).
    - `div128Quot_v2_q1_prime_prime_dLo_no_wrap` (just proven for v2).

    Issue #1337 algorithm fix migration. -/
theorem div128Quot_v2_un21_toNat
    (uHi uLo vTop : Word)
    (hdHi_ge : (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdLo_lt : ((vTop <<< (32 : BitVec 6).toNat) >>>
                 (32 : BitVec 6).toNat).toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat <
      (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
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
    un21.toNat = ((rhat''.toNat % 2^32) * 2^32 + div_un1.toNat + 2^64 -
                   q1''.toNat * dLo.toNat) % 2^64 := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat' q1'' rhat''
    cu_rhat_un1 cu_q1_dlo un21
  have h_cu_rhat : cu_rhat_un1.toNat =
      (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat :=
    div128Quot_cu_rhat_un1_toNat rhat'' uLo
  have h_cu_q1 : cu_q1_dlo.toNat = q1''.toNat * dLo.toNat :=
    div128Quot_v2_q1_prime_prime_dLo_no_wrap uHi dHi dLo rhatUn1 div_un1
      hdHi_ge hdLo_lt huHi_lt_vTop
  show (cu_rhat_un1 - cu_q1_dlo).toNat = _
  rw [BitVec.toNat_sub, h_cu_rhat, h_cu_q1]
  congr 1
  omega

/-- **`un21` computation case-analysis for `div128Quot_v2`** (v2 analog
    of `div128Quot_un21_toNat_case` from `Div128FinalAssembly.lean:213`).

    The structure of the un21 computation is identical between v1 and v2 —
    `un21 = (rhat << 32) | div_un1 - q1 * dLo` — but uses `q1''/rhat''`
    (post-2nd-D3) instead of `q1'/rhat'` (post-1st-D3) as inputs.

    For v2, when `rhat'' < 2^32` (the "no-wrap" case), `un21 = A - B`
    where `A = rhat'' * 2^32 + div_un1` and `B = q1'' * dLo`. Otherwise
    Word arithmetic wraps and `un21 = A + 2^64 - B`.

    **Why simpler for v2**: under v2's call-trial preconditions, the
    no-wrap case `rhat'' < 2^32` should hold automatically (since the
    2nd D3 correction targets exactly the rhat ≥ 2^32 case). The wrap
    case is impossible/rare for v2 inputs in the call-trial regime.

    Issue #1337 algorithm fix migration. -/
theorem div128Quot_v2_un21_toNat_case
    (uHi uLo vTop : Word)
    (hdHi_ge : (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdLo_lt : ((vTop <<< (32 : BitVec 6).toNat) >>>
                 (32 : BitVec 6).toNat).toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat <
      (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    -- v2-specific 2nd D3 step:
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
    let A := (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat
    let B := q1''.toNat * dLo.toNat
    (B ≤ A → un21.toNat = A - B) ∧
    (A < B → un21.toNat = A + 2^64 - B) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat' q1'' rhat''
    cu_rhat_un1 cu_q1_dlo un21 A B
  have h_formula : un21.toNat = (A + 2^64 - B) % 2^64 :=
    div128Quot_v2_un21_toNat uHi uLo vTop hdHi_ge hdLo_lt huHi_lt_vTop
  have hA_lt : A < 2^64 := by
    show (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat < 2^64
    have : rhat''.toNat % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
    have : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
    nlinarith
  have hB_lt : B < 2^64 := by
    show q1''.toNat * dLo.toNat < 2^64
    have : cu_q1_dlo.toNat = q1''.toNat * dLo.toNat :=
      div128Quot_v2_q1_prime_prime_dLo_no_wrap uHi dHi dLo rhatUn1 div_un1
        hdHi_ge hdLo_lt huHi_lt_vTop
    have := cu_q1_dlo.isLt
    omega
  refine ⟨?_, ?_⟩
  · intro hBA
    rw [h_formula]
    show (A + 2^64 - B) % 2^64 = A - B
    rw [show A + 2^64 - B = (A - B) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : A - B < 2^64)]
  · intro hAB
    rw [h_formula]
    show (A + 2^64 - B) % 2^64 = A + 2^64 - B
    exact Nat.mod_eq_of_lt (by omega : A + 2^64 - B < 2^64)

/-- **Untruncated KB-Compose V2** — pure-Nat version of
    `knuth_compose_qHat_vTop_le_nat_v2` using the untruncated `rhat'`
    instead of `rhat' % 2^32`. The proof is actually CLEANER than the
    truncated original because we don't need the
    `rhat' = (rhat' / 2^32) * 2^32 + rhat' % 2^32` split — `rhat' * 2^64`
    appears directly.

    Issue #1337 algorithm fix migration. Alternative path 3 supporting lemma. -/
theorem knuth_compose_qHat_vTop_le_nat_v2_untruncated
    (q1' q0' rhat' rhat2' dHi dLo div_un1 div_un0 uHi : Nat)
    (h_ph1_eucl : q1' * dHi + rhat' = uHi)
    (h_ph1_no_wrap_lo : q1' * dLo ≤ rhat' * 2^32 + div_un1)
    (h_un21_ph2 : q0' * dHi + rhat2' = rhat' * 2^32 + div_un1 - q1' * dLo)
    (h_ph2_no_wrap : q0' * dLo ≤ rhat2' * 2^32 + div_un0) :
    (q1' * 2^32 + q0') * (dHi * 2^32 + dLo) ≤
    uHi * 2^64 + div_un1 * 2^32 + div_un0 := by
  have h_un21_plus :
      q0' * dHi + rhat2' + q1' * dLo = rhat' * 2^32 + div_un1 := by omega
  have h_mul : q0' * dHi * 2^32 + rhat2' * 2^32 + q1' * dLo * 2^32 =
               rhat' * 2^64 + div_un1 * 2^32 := by
    have h := congr_arg (· * 2^32) h_un21_plus
    simp only at h
    have h_expand_lhs : (q0' * dHi + rhat2' + q1' * dLo) * 2^32 =
                        q0' * dHi * 2^32 + rhat2' * 2^32 + q1' * dLo * 2^32 := by ring
    have h_expand_rhs : (rhat' * 2^32 + div_un1) * 2^32 =
                        rhat' * 2^64 + div_un1 * 2^32 := by ring
    linarith
  have h_uHi_64 : uHi * 2^64 = q1' * dHi * 2^64 + rhat' * 2^64 := by
    have h := congr_arg (· * 2^64) h_ph1_eucl
    simp only at h
    have : (q1' * dHi + rhat') * 2^64 = q1' * dHi * 2^64 + rhat' * 2^64 := by ring
    linarith
  have h_lhs : (q1' * 2^32 + q0') * (dHi * 2^32 + dLo) =
               q1' * dHi * 2^64 + q1' * dLo * 2^32 +
               q0' * dHi * 2^32 + q0' * dLo := by ring
  rw [h_lhs]
  linarith

/-! Pure-Nat helpers `un21_toNat_untruncated_arith`, `conj2_arith`, and
    `un21_lt_vTop_arith` were moved to `Spec/CallAddbackPureNat.lean`
    (sub-slice of evm-asm-ry8 / #1078). They are pure ℕ algebraic
    identities with no Word/EvmWord/BitVec content, fitting the existing
    `CallAddbackPureNat.lean` charter. References below resolve via
    the existing `import EvmAsm.Evm64.DivMod.Spec.CallAddbackPureNat`. -/

/-- **Untruncated bridge for `un21.toNat`** — the alternative-path-3 helper.

    Under the two-bound untruncated invariant
    `B ≤ A_un` and `A_un - B < 2^64`
    (where `A_un = rhat''.toNat * 2^32 + div_un1.toNat`,
    `B = q1''.toNat * dLo.toNat`),
    `un21.toNat = A_un - B` directly — the truncation of `rhat''` and the
    Word subtraction wrap cancel out exactly.

    **Why this is the right bridge for the call+addback BEQ closure:**
    - The truncated form `un21.toNat = A_trunc - B` (from
      `div128Quot_v2_un21_toNat_case.1`) requires `B ≤ A_trunc`, which is
      provably FALSE under runtime preconditions (see
      `div128Quot_v2_phase1_no_wrap_lo_FALSE_counterexample`).
    - The untruncated form requires `B ≤ A_un` (HOLDS — see
      `div128Quot_v2_phase1_no_wrap_lo_untruncated_HOLDS_on_counterexample`)
      and the additional bound `A_un - B < 2^64`.
    - On the counterexample: `A_un = 2^64`, `B = 2^63 - 2^31`,
      `A_un - B = 2^63 + 2^31 < 2^64`. ✓

    **Proof sketch (stub for now):** `div128Quot_v2_un21_toNat` gives
    `un21.toNat = (A_trunc + 2^64 - B) % 2^64`. Note `A_un = A_trunc +
    k * 2^64` where `k = rhat''.toNat / 2^32`. So `A_trunc + 2^64 - B =
    A_un - (k - 1) * 2^64 - B` (in Int). Since `(k - 1) * 2^64 ≡ 0
    (mod 2^64)` for any integer k, `un21.toNat = (A_un - B) mod 2^64 =
    A_un - B` under the two-bound invariant.

    Issue #1337 algorithm fix migration. Alternative path 3. -/
theorem div128Quot_v2_un21_toNat_untruncated
    (uHi uLo vTop : Word)
    (hdHi_ge : (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdLo_lt : ((vTop <<< (32 : BitVec 6).toNat) >>>
                 (32 : BitVec 6).toNat).toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat <
      (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
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
    let A_un := rhat''.toNat * 2^32 + div_un1.toNat
    let B := q1''.toNat * dLo.toNat
    B ≤ A_un → A_un - B < 2^64 → un21.toNat = A_un - B := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 A_un B hBA hAB
  have h_formula : un21.toNat = ((rhat''.toNat % 2^32) * 2^32 + div_un1.toNat + 2^64 -
                                 q1''.toNat * dLo.toNat) % 2^64 :=
    div128Quot_v2_un21_toNat uHi uLo vTop hdHi_ge hdLo_lt huHi_lt_vTop
  have hB_lt : q1''.toNat * dLo.toNat < 2^64 := by
    have h_cu : (q1'' * dLo).toNat = q1''.toNat * dLo.toNat :=
      div128Quot_v2_q1_prime_prime_dLo_no_wrap uHi dHi dLo rhatUn1 div_un1
        hdHi_ge hdLo_lt huHi_lt_vTop
    have := (q1'' * dLo).isLt
    omega
  have h_rhat_decomp : rhat''.toNat = rhat''.toNat % 2^32 + (rhat''.toNat / 2^32) * 2^32 := by
    omega
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_mod_lt : rhat''.toNat % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
  have h_A_trunc_lt : (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat < 2^64 := by nlinarith
  -- Unfold A_un and B in the goal so we can manipulate with omega.
  show un21.toNat = rhat''.toNat * 2^32 + div_un1.toNat - q1''.toNat * dLo.toNat
  rw [h_formula]
  -- Decompose rhat''.toNat = (rhat''.toNat % 2^32) + (rhat''.toNat / 2^32) * 2^32.
  -- So A_un = A_trunc + (rhat''.toNat / 2^32) * 2^64.
  set k := rhat''.toNat / 2^32 with hk_def
  set A_trunc := (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat with hA_trunc_def
  set B := q1''.toNat * dLo.toNat with hB_def
  -- A_un (as expression) = A_trunc + k * 2^64.
  have hA_un_expr : rhat''.toNat * 2^32 + div_un1.toNat = A_trunc + k * 2^64 := by
    rw [h_rhat_decomp]; ring
  rw [hA_un_expr]
  -- Goal: (A_trunc + 2^64 - B) % 2^64 = A_trunc + k * 2^64 - B.
  -- Need: k ∈ {0, 1}. From hBA + hAB: A_trunc + k * 2^64 < 2^64 + B ≤ 2 * 2^64.
  have hBA' : B ≤ A_trunc + k * 2^64 := by rw [← hA_un_expr]; exact hBA
  have hAB' : A_trunc + k * 2^64 - B < 2^64 := by rw [← hA_un_expr]; exact hAB
  exact un21_toNat_untruncated_arith A_trunc B k h_A_trunc_lt hB_lt hBA' hAB'

/-- **Full v2 qHat_vTop_le with no_wrap hypotheses** (`_full` variant).

    Mirrors v1's `div128Quot_qHat_vTop_le` from `Div128CallSkipClose.lean:149`
    exactly, but uses `div128Quot_v2` instead of `div128Quot`. Composes the
    7 already-proven v2 sub-lemmas + reusable v1 infrastructure.

    The "_full" suffix distinguishes it from `div128Quot_v2_qHat_vTop_le`
    above (which has the simpler signature without no_wrap implications).
    The simple form is downstream of this — use the `_full` variant when
    you can supply the no_wrap hypotheses; otherwise use the simple form
    (which currently still has a sorry).

    Issue #1337 algorithm fix migration. -/
theorem div128Quot_v2_qHat_vTop_le_full
    (uHi uLo vTop : Word)
    (hdHi_ge : (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdLo_lt : ((vTop <<< (32 : BitVec 6).toNat) >>>
                 (32 : BitVec 6).toNat).toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat <
      (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
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
    let rhat2' := if rhat2c >>> (32 : BitVec 6).toNat = 0 then
                    (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                                    (q0c * dLo) then rhat2c + dHi else rhat2c)
                  else rhat2c
    q1''.toNat * dLo.toNat ≤ (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat →
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat →
    q0'.toNat < 2^32 →
    (div128Quot_v2 uHi uLo vTop).toNat * vTop.toNat ≤
      uHi.toNat * 2^64 + uLo.toNat := by
  intro dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        q1'' rhat'' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2'
        h_ph1_no_wrap_lo h_ph2_no_wrap hq0_lt
  -- Algorithm-level setup.
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [show dHi = vTop >>> (32 : BitVec 6).toNat from rfl] at heq
    rw [heq] at hdHi_ge; simp at hdHi_ge
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  -- Phase 1a invariants.
  have h_post1a := div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  -- Phase 1b 1st D3 Euclidean: q1' * dHi + rhat' = uHi.
  have h_ph1_eucl_1st : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat :=
    div128Quot_phase1b_post uHi dHi q1c rhatc dLo rhatUn1 hdHi_lt h_post1a
      (div128Quot_rhatc_lt_2dHi uHi dHi hdHi_ne hdHi_lt)
  -- Phase 1b 2nd D3 Euclidean (using new v2 lemma): q1'' * dHi + rhat'' = uHi.
  have h_ph1_eucl_2nd : q1''.toNat * dHi.toNat + rhat''.toNat = uHi.toNat :=
    div128Quot_v2_phase1b_2nd_post uHi dHi q1' rhat' dLo div_un1
      hdHi_ge hdHi_lt h_ph1_eucl_1st
  -- un21 case (no-wrap): un21.toNat = A - B.
  have h_un21_case := div128Quot_v2_un21_toNat_case uHi uLo vTop
    hdHi_ge hdLo_lt huHi_lt_vTop
  have h_un21 : un21.toNat =
      (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat - q1''.toNat * dLo.toNat :=
    h_un21_case.1 h_ph1_no_wrap_lo
  -- Phase 2a invariants (instantiate Phase 1a on un21).
  have h_post2a := div128Quot_first_round_post un21 dHi hdHi_ne hdHi_lt
  have h_rhat2c_lt := div128Quot_rhatc_lt_2dHi un21 dHi hdHi_ne hdHi_lt
  -- Phase 2b Euclidean against un21.
  have h_ph2b : q0'.toNat * dHi.toNat + rhat2'.toNat = un21.toNat :=
    div128Quot_phase2b_post un21 dHi hdHi_lt q0c rhat2c dLo h_post2a h_rhat2c_lt
  -- Combine h_ph2b + h_un21.
  have h_un21_ph2 : q0'.toNat * dHi.toNat + rhat2'.toNat =
      (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat - q1''.toNat * dLo.toNat := by
    rw [h_ph2b, h_un21]
  -- Pure-Nat KB-Compose V2 (with q1''/rhat'' substituted for q1'/rhat').
  have h_compose := knuth_compose_qHat_vTop_le_nat_v2
    q1''.toNat q0'.toNat rhat''.toNat rhat2'.toNat dHi.toNat dLo.toNat
    div_un1.toNat div_un0.toNat uHi.toNat
    h_ph1_eucl_2nd h_ph1_no_wrap_lo h_un21_ph2 h_ph2_no_wrap
  -- Output formula via div128Quot_v2_toNat_eq_strict.
  have h_div_eq :
      (div128Quot_v2 uHi uLo vTop).toNat = q1''.toNat * 2^32 + q0'.toNat :=
    div128Quot_v2_toNat_eq_strict uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt
      huHi_lt_vTop hq0_lt
  -- vTop and uLo decompositions.
  have h_vtop : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uLo : uLo.toNat = div_un1.toNat * 2^32 + div_un0.toNat :=
    div128Quot_vTop_decomp uLo
  calc (div128Quot_v2 uHi uLo vTop).toNat * vTop.toNat
      = (q1''.toNat * 2^32 + q0'.toNat) * (dHi.toNat * 2^32 + dLo.toNat) := by
          rw [h_div_eq, h_vtop]
    _ ≤ uHi.toNat * 2^64 + div_un1.toNat * 2^32 + div_un0.toNat := h_compose
    _ = uHi.toNat * 2^64 + uLo.toNat := by rw [h_uLo]; ring

/-- **Untruncated `qHat_vTop_le_full`** — alternative path 3.

    Same conclusion as `div128Quot_v2_qHat_vTop_le_full` but uses the
    UNTRUNCATED phase-1 invariant (with the upper-bound conjunct) instead
    of the truncated form (provably FALSE under runtime preconditions).

    Composes:
    - `div128Quot_v2_un21_toNat_untruncated` (bridge — proven).
    - `knuth_compose_qHat_vTop_le_nat_v2_untruncated` (KB-compose — proven).
    - Existing v1/v2 Phase 1a/1b/2a/2b Euclidean lemmas.

    Issue #1337 algorithm fix migration. Alternative path 3. -/
theorem div128Quot_v2_qHat_vTop_le_full_untruncated
    (uHi uLo vTop : Word)
    (hdHi_ge : (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdLo_lt : ((vTop <<< (32 : BitVec 6).toNat) >>>
                 (32 : BitVec 6).toNat).toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat <
      (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
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
    let rhat2' := if rhat2c >>> (32 : BitVec 6).toNat = 0 then
                    (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                                    (q0c * dLo) then rhat2c + dHi else rhat2c)
                  else rhat2c
    -- Untruncated phase-1 (two conjuncts) + phase-2 + q0' bound:
    q1''.toNat * dLo.toNat ≤ rhat''.toNat * 2^32 + div_un1.toNat →
    rhat''.toNat * 2^32 + div_un1.toNat - q1''.toNat * dLo.toNat < 2^64 →
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat →
    q0'.toNat < 2^32 →
    (div128Quot_v2 uHi uLo vTop).toNat * vTop.toNat ≤
      uHi.toNat * 2^64 + uLo.toNat := by
  intro dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        q1'' rhat'' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2'
        h_ph1_no_wrap_lo h_ph1_un21_lt h_ph2_no_wrap hq0_lt
  -- Algorithm-level setup.
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [show dHi = vTop >>> (32 : BitVec 6).toNat from rfl] at heq
    rw [heq] at hdHi_ge; simp at hdHi_ge
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  -- Phase 1a invariants.
  have h_post1a := div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  -- Phase 1b 1st D3 Euclidean: q1' * dHi + rhat' = uHi.
  have h_ph1_eucl_1st : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat :=
    div128Quot_phase1b_post uHi dHi q1c rhatc dLo rhatUn1 hdHi_lt h_post1a
      (div128Quot_rhatc_lt_2dHi uHi dHi hdHi_ne hdHi_lt)
  -- Phase 1b 2nd D3 Euclidean: q1'' * dHi + rhat'' = uHi.
  have h_ph1_eucl_2nd : q1''.toNat * dHi.toNat + rhat''.toNat = uHi.toNat :=
    div128Quot_v2_phase1b_2nd_post uHi dHi q1' rhat' dLo div_un1
      hdHi_ge hdHi_lt h_ph1_eucl_1st
  -- un21 via UNTRUNCATED bridge (path 3): un21.toNat = A_un - B.
  have h_un21 : un21.toNat =
      rhat''.toNat * 2^32 + div_un1.toNat - q1''.toNat * dLo.toNat :=
    div128Quot_v2_un21_toNat_untruncated uHi uLo vTop hdHi_ge hdLo_lt
      huHi_lt_vTop h_ph1_no_wrap_lo h_ph1_un21_lt
  -- Phase 2a + 2b.
  have h_post2a := div128Quot_first_round_post un21 dHi hdHi_ne hdHi_lt
  have h_rhat2c_lt := div128Quot_rhatc_lt_2dHi un21 dHi hdHi_ne hdHi_lt
  have h_ph2b : q0'.toNat * dHi.toNat + rhat2'.toNat = un21.toNat :=
    div128Quot_phase2b_post un21 dHi hdHi_lt q0c rhat2c dLo h_post2a h_rhat2c_lt
  -- Combine: q0' * dHi + rhat2' = rhat'' * 2^32 + div_un1 - q1'' * dLo (UNTRUNCATED).
  have h_un21_ph2 : q0'.toNat * dHi.toNat + rhat2'.toNat =
      rhat''.toNat * 2^32 + div_un1.toNat - q1''.toNat * dLo.toNat := by
    rw [h_ph2b, h_un21]
  -- Pure-Nat KB-Compose UNTRUNCATED.
  have h_compose := knuth_compose_qHat_vTop_le_nat_v2_untruncated
    q1''.toNat q0'.toNat rhat''.toNat rhat2'.toNat dHi.toNat dLo.toNat
    div_un1.toNat div_un0.toNat uHi.toNat
    h_ph1_eucl_2nd h_ph1_no_wrap_lo h_un21_ph2 h_ph2_no_wrap
  -- Output formula.
  have h_div_eq :
      (div128Quot_v2 uHi uLo vTop).toNat = q1''.toNat * 2^32 + q0'.toNat :=
    div128Quot_v2_toNat_eq_strict uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt
      huHi_lt_vTop hq0_lt
  -- vTop and uLo decompositions.
  have h_vtop : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uLo : uLo.toNat = div_un1.toNat * 2^32 + div_un0.toNat :=
    div128Quot_vTop_decomp uLo
  calc (div128Quot_v2 uHi uLo vTop).toNat * vTop.toNat
      = (q1''.toNat * 2^32 + q0'.toNat) * (dHi.toNat * 2^32 + dLo.toNat) := by
          rw [h_div_eq, h_vtop]
    _ ≤ uHi.toNat * 2^64 + div_un1.toNat * 2^32 + div_un0.toNat := h_compose
    _ = uHi.toNat * 2^64 + uLo.toNat := by rw [h_uLo]; ring

/-- **Knuth Theorem B for `div128Quot_v2`** (val256 form, mirroring v1's
    `div128Quot_le_val256_div_plus_two` from
    `EvmAsm/Evm64/EvmWordArith/Div128CallSkipClose.lean:267`).

    Under CLZ-normalized divisor + call-trial range, the v2 algorithm's
    quotient is bounded by:
    ```
    (div128Quot_v2 u4 un3 b3').toNat ≤ val256(a) / val256(b) + 2
    ```

    This is the **new fact unlocked by the v2 algorithm fix**
    (`div128_v2_spec`, PR #1392): the buggy `div128Quot` violates this
    bound on the counterexample (overshoots by 2^32-2). The v2 fix
    closes this by adding the 2nd D3 correction iteration.

    **Why this should be EASIER for v2 than v1**: the v1 version
    (`div128Quot_le_val256_div_plus_two`) requires 3 `no_wrap`
    hypotheses (Tasks 4/5 in the migration plan). For v2, the
    2-correction loop ensures the no-wrap conditions are automatically
    satisfied OR strictly weaker, so the Step 1 lemma
    (`div128Quot_v2_qHat_vTop_le`) can be proven without the
    same level of fragility.

    Proof structure (when filled):
    1. Step 1 (NEW): `div128Quot_v2_qHat_vTop_le` — multiplication form
       `qHat * vTop ≤ uHi * 2^64 + uLo` after 2 D3 corrections.
    2. Step 2 (EXISTING): `knuth_theorem_b_from_clz` from KnuthTheoremB.lean
       composes via `Nat.le_div_iff_mul_le` to give the +2 bound.

    Issue #1337 algorithm fix migration. -/
theorem div128Quot_v2_le_val256_div_plus_two
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let div_un0 := (un3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
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
    let rhat2' := if rhat2c >>> (32 : BitVec 6).toNat = 0 then
                    (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                                    (q0c * dLo) then rhat2c + dHi else rhat2c)
                  else rhat2c
    -- v1-style no-wrap implications (mirror v1's `div128Quot_le_val256_div_plus_two`).
    q1''.toNat * dLo.toNat ≤ (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat →
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat →
    q0'.toNat < 2^32 →
    (div128Quot_v2 u4 un3 b3').toNat ≤
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 2 := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc
        qDlo rhatUn1 q1' rhat' q1'' rhat'' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2
        hi2 q0c rhat2c q0' rhat2' h_ph1_no_wrap_lo h_ph2_no_wrap hq0_lt
  -- Discharge Step 1's preconditions (same as v1's pattern in
  -- div128Quot_le_val256_div_plus_two from Div128CallSkipClose.lean:267).
  have hb3prime_ge_pow63 : b3'.toNat ≥ 2^63 := b3_prime_ge_pow63 b3 b2 hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 := div128Quot_dHi_ge_pow31 b3' hb3prime_ge_pow63
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hu4_lt_b3prime : u4.toNat < b3'.toNat := isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_vtop : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have hu4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vtop]; exact hu4_lt_b3prime
  -- Step 1 (NOW PROVEN via div128Quot_v2_qHat_vTop_le_full): multiplication form.
  have h_step1 := div128Quot_v2_qHat_vTop_le_full u4 un3 b3' hdHi_ge hdLo_lt
    hu4_lt_vTop h_ph1_no_wrap_lo h_ph2_no_wrap hq0_lt
  -- Convert multiplication bound to division bound.
  have hb3prime_pos : 0 < b3'.toNat := by omega
  have h_div_le : (div128Quot_v2 u4 un3 b3').toNat ≤
      (u4.toNat * 2^64 + un3.toNat) / b3'.toNat :=
    (Nat.le_div_iff_mul_le hb3prime_pos).mpr h_step1
  -- Step 2 (existing): Knuth-B abstract bound from CLZ.
  have h_step2 := knuth_theorem_b_from_clz a0 a1 a2 a3 b0 b1 b2 b3
    hb3nz hshift_nz hcall
  -- Transitivity.
  calc (div128Quot_v2 u4 un3 b3').toNat
      ≤ (u4.toNat * 2^64 + un3.toNat) / b3'.toNat := h_div_le
    _ ≤ val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 2 := h_step2

/-- **Untruncated val256 form** — alternative path 3 lift to the val256 level.

    Same conclusion as `div128Quot_v2_le_val256_div_plus_two` but takes the
    UNTRUNCATED phase-1 invariants (with the upper-bound conjunct) instead
    of the truncated form (provably FALSE under runtime preconditions).

    Composes:
    - `div128Quot_v2_qHat_vTop_le_full_untruncated` (new, proven).
    - `Nat.le_div_iff_mul_le` for the division bound.
    - `knuth_theorem_b_from_clz` for the abstract Knuth-B bound (existing).

    Issue #1337 algorithm fix migration. Alternative path 3. -/
theorem div128Quot_v2_le_val256_div_plus_two_untruncated
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let div_un0 := (un3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
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
    let rhat2' := if rhat2c >>> (32 : BitVec 6).toNat = 0 then
                    (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                                    (q0c * dLo) then rhat2c + dHi else rhat2c)
                  else rhat2c
    -- Untruncated phase-1 invariant (2 conjuncts) + phase-2 + q0' bound:
    q1''.toNat * dLo.toNat ≤ rhat''.toNat * 2^32 + div_un1.toNat →
    rhat''.toNat * 2^32 + div_un1.toNat - q1''.toNat * dLo.toNat < 2^64 →
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat →
    q0'.toNat < 2^32 →
    (div128Quot_v2 u4 un3 b3').toNat ≤
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 2 := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc
        qDlo rhatUn1 q1' rhat' q1'' rhat'' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2
        hi2 q0c rhat2c q0' rhat2'
        h_ph1_no_wrap_lo h_ph1_un21_lt h_ph2_no_wrap hq0_lt
  -- Step 1 preconditions (same as the truncated variant).
  have hb3prime_ge_pow63 : b3'.toNat ≥ 2^63 := b3_prime_ge_pow63 b3 b2 hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 := div128Quot_dHi_ge_pow31 b3' hb3prime_ge_pow63
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hu4_lt_b3prime : u4.toNat < b3'.toNat := isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_vtop : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have hu4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vtop]; exact hu4_lt_b3prime
  -- Step 1 via UNTRUNCATED wrapper.
  have h_step1 := div128Quot_v2_qHat_vTop_le_full_untruncated u4 un3 b3' hdHi_ge
    hdLo_lt hu4_lt_vTop h_ph1_no_wrap_lo h_ph1_un21_lt h_ph2_no_wrap hq0_lt
  have hb3prime_pos : 0 < b3'.toNat := by omega
  have h_div_le : (div128Quot_v2 u4 un3 b3').toNat ≤
      (u4.toNat * 2^64 + un3.toNat) / b3'.toNat :=
    (Nat.le_div_iff_mul_le hb3prime_pos).mpr h_step1
  -- Step 2 (existing): Knuth-B abstract bound from CLZ.
  have h_step2 := knuth_theorem_b_from_clz a0 a1 a2 a3 b0 b1 b2 b3
    hb3nz hshift_nz hcall
  calc (div128Quot_v2 u4 un3 b3').toNat
      ≤ (u4.toNat * 2^64 + un3.toNat) / b3'.toNat := h_div_le
    _ ≤ val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 2 := h_step2

/-- **5-limb shifted-domain Knuth-B for v2 — proven path-3 lift.**

    Mirror of `div128Quot_v2_le_val256_div_plus_two_untruncated` but with
    the conclusion in 5-limb shifted-domain form
    `qHat ≤ (u4 * 2^256 + val256 un) / val256 b' + 2`.

    Composes:
    - `div128Quot_v2_qHat_vTop_le_full_untruncated` (existing, proven from
      the four untruncated invariants).
    - `knuth_theorem_b_5limb_shifted_val256` (new in `KnuthTheoremB.lean`).

    Compared to the original-domain version:
    - Sidesteps `val256(a)` algebra entirely (no `u_val256_eq_scaled_with_overflow`).
    - The 5-limb shifted-domain quotient equals `val256(a) / val256(b)` by
      scale invariance, so this is logically the same bound — but stated
      directly in terms of the algorithm's normalized limbs, which is
      what the v2 carry-partition decomposition wants to consume.

    Note: the 4-limb-only analogue (using `val256(un)` in the divisor's
    numerator instead of `u4 * 2^256 + val256(un)`) is generally FALSE
    when `u4 > 0` — see the docstring on `knuth_theorem_b_5limb_shifted_val256`.

    Issue #1337 algorithm fix migration. Alternative path 3, shifted form. -/
theorem div128Quot_v2_le_5limb_shifted_div_plus_two_untruncated
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let un2 := (a2 <<< shift) ||| (a1 >>> antiShift)
    let un1 := (a1 <<< shift) ||| (a0 >>> antiShift)
    let un0 := a0 <<< shift
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let b2' := (b2 <<< shift) ||| (b1 >>> antiShift)
    let b1' := (b1 <<< shift) ||| (b0 >>> antiShift)
    let b0' := b0 <<< shift
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let div_un0 := (un3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
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
    let rhat2' := if rhat2c >>> (32 : BitVec 6).toNat = 0 then
                    (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                                    (q0c * dLo) then rhat2c + dHi else rhat2c)
                  else rhat2c
    -- Untruncated phase-1 invariant (2 conjuncts) + phase-2 + q0' bound:
    q1''.toNat * dLo.toNat ≤ rhat''.toNat * 2^32 + div_un1.toNat →
    rhat''.toNat * 2^32 + div_un1.toNat - q1''.toNat * dLo.toNat < 2^64 →
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat →
    q0'.toNat < 2^32 →
    (div128Quot_v2 u4 un3 b3').toNat ≤
      (u4.toNat * 2^256 + val256 un0 un1 un2 un3) /
        val256 b0' b1' b2' b3' + 2 := by
  intro shift antiShift u4 un3 un2 un1 un0 b3' b2' b1' b0' dHi dLo div_un1 div_un0
        q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat' q1'' rhat'' cu_rhat_un1
        cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2'
        h_ph1_no_wrap_lo h_ph1_un21_lt h_ph2_no_wrap hq0_lt
  -- Step 1: same untruncated lift used by the original-domain variant.
  have hb3prime_ge_pow63 : b3'.toNat ≥ 2^63 := b3_prime_ge_pow63 b3 b2 hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 := div128Quot_dHi_ge_pow31 b3' hb3prime_ge_pow63
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hu4_lt_b3prime : u4.toNat < b3'.toNat := isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_vtop : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have hu4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vtop]; exact hu4_lt_b3prime
  have h_step1 := div128Quot_v2_qHat_vTop_le_full_untruncated u4 un3 b3' hdHi_ge
    hdLo_lt hu4_lt_vTop h_ph1_no_wrap_lo h_ph1_un21_lt h_ph2_no_wrap hq0_lt
  have hb3prime_pos : 0 < b3'.toNat := by omega
  have h_div_le : (div128Quot_v2 u4 un3 b3').toNat ≤
      (u4.toNat * 2^64 + un3.toNat) / b3'.toNat :=
    (Nat.le_div_iff_mul_le hb3prime_pos).mpr h_step1
  -- Step 2: 5-limb shifted Knuth-B (NEW), no original-domain bridging needed.
  have h_step2 := knuth_theorem_b_5limb_shifted_val256
    un0 un1 un2 un3 b0' b1' b2' b3' u4 hb3prime_ge_pow63 hu4_lt_b3prime
  calc (div128Quot_v2 u4 un3 b3').toNat
      ≤ (u4.toNat * 2^64 + un3.toNat) / b3'.toNat := h_div_le
    _ ≤ (u4.toNat * 2^256 + val256 un0 un1 un2 un3) /
        val256 b0' b1' b2' b3' + 2 := h_step2

/-- **Knuth's classical baseline at q1c**: the initial trial `q1c` (after
    Phase-1a's hi1-clamp) lies in `[q*, q* + 2]` where `q* = floor(x/vTop)`.
    This is Knuth's TAOCP Theorem A (lower) + Theorem B (upper) applied at
    the initial trial level.

    PROVEN STUB. Closes via:
    - q1c is a Word-level u4 / dHi (with hi1 fix), so `q1c * dHi ≤ u4 <
      (q1c + 1) * dHi` — the dHi-only Euclidean.
    - Knuth-A at trial: q1c ≥ floor((u4 * 2^32) / (dHi * 2^32 + dLo)).
      Since dLo < 2^32 and dHi ≥ 2^31, dropping dLo can only raise the
      quotient, so q1c ≥ q*.
    - Knuth-B at trial: q1c ≤ q* + 2 (TAOCP 4.3.1 Thm B).

    **Issue #1337 algorithm fix migration. Decomposition sub-stub.** -/
theorem div128Quot_v2_phase1c_in_knuth_range_under_runtime (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hbltu : isCallTrialN4Evm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (_hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let q_true := (u4.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat)
    q_true ≤ q1c.toNat ∧ q1c.toNat ≤ q_true + 2 := by
  -- Composes existing proven Knuth-A (`div128Quot_q1c_ge_q_true_1`) and
  -- Knuth-B (`div128Quot_q1_le_q_true_1_plus_two`) with the hi1-fix bound
  -- q1c ≤ q1.
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 hi1 q1c q_true
  -- Standard arithmetic facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_b3'_ge_pow63 : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) _hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 b3' h_b3'_ge_pow63
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have hu4_lt_b3prime : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      (isCallTrialN4Evm_def ▸ _hbltu)
  have h_b3'_decomp : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have hu4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_b3'_decomp]; exact hu4_lt_b3prime
  refine ⟨?lower, ?upper⟩
  case lower =>
    -- Knuth-A: q_true ≤ q1c via `div128Quot_q1c_ge_q_true_1`.
    have h := div128Quot_q1c_ge_q_true_1 u4 dHi dLo div_un1 hdHi_ne h_div_un1_lt
      hu4_lt_vTop
    simp only [] at h
    exact h
  case upper =>
    -- Knuth-B: q1 ≤ q_true + 2 via `div128Quot_q1_le_q_true_1_plus_two`,
    -- then q1c ≤ q1 via the hi1 fix.
    have h_q1_le : q1.toNat ≤ q_true + 2 :=
      div128Quot_q1_le_q_true_1_plus_two u4 dHi dLo div_un1 hdHi_ne hdHi_ge hdLo_lt
        h_div_un1_lt hu4_lt_vTop
    -- q1c ≤ q1 (hi1 fix only decrements, never increments).
    have h_q1c_le_q1 : q1c.toNat ≤ q1.toNat := by
      show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat ≤ q1.toNat
      by_cases h_hi1 : hi1 = 0
      · rw [if_pos h_hi1]
      · rw [if_neg h_hi1]
        rw [BitVec.toNat_add, signExtend12_4095_toNat]
        -- q1c = q1 + (2^64 - 1) mod 2^64. If q1 ≥ 1 (which hi1 ≠ 0 gives),
        -- q1c = q1 - 1 ≤ q1.
        have h_q1_ge_pow32 : q1.toNat ≥ 2^32 := by
          by_contra hlt
          push Not at hlt
          apply h_hi1
          apply BitVec.eq_of_toNat_eq
          show (q1 >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat
          rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
              Nat.shiftRight_eq_div_pow]
          rw [Nat.div_eq_of_lt hlt]
          rfl
        have h_q1_ge_1 : q1.toNat ≥ 1 := by
          have : (2^32 : Nat) ≥ 1 := by decide
          omega
        have hq1_lt_word : q1.toNat - 1 < 2^64 := by have := q1.isLt; omega
        rw [show q1.toNat + (2^64 - 1) = (q1.toNat - 1) + 2^64 from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hq1_lt_word]
        omega
    omega




end EvmAsm.Evm64
