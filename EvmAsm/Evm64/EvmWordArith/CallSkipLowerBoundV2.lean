/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2

  Replacement for PR #1154 (closed). Proves the call-skip exact lower bound
  `val256(a)/val256(b) ≤ (div128Quot u4 u3 b3').toNat` under shift_nz + hcall
  + hskip, via a **GLOBAL Phase 1+2 compensation argument** instead of the
  per-phase tight bounds that PR #1154 attempted.

  Background (why per-phase fails): see
  `memory/project_knuth_b_lower_large_rhatc.md`. The overall Knuth bound
  `qHat ≥ q_true_full` holds only because Phase 2 compensates Phase 1
  undershoots — a global, not per-phase, property.

  ## Decomposition plan — §A (core) and §B (bridge)

  Each sub-section contains further decomposition into small sub-lemmas.
  Sorrys are focused: each ≤ ~100 lines, addressable in one iteration.

  ### §A: core Knuth-B lower bound at 128/64

  - A1: Knuth-B UPPER form (context, ~100 lines).
  - A2: Knuth-B LOWER form via Phase 1+2 compensation (the hard core, ~300 lines).
  - A4 `div128Quot_ge_q_true_normalized`: wrapper, derived from A2.

  ### §B: val256 → 128/64 bridge

  - B3.1 `nat_trunc_div_add_lt`: (A*K + L) / (B*K) = A/B when 0 < K, 0 < B, L < K.
    Pure Nat lemma, ~20 lines.
  - B3.2 `val256_b_norm_ge_b3prime_mul_pow192`: val256(b_norm) ≥ b3'.toNat * 2^192.
    Immediate from val256 definition, ~10 lines.
  - B3.3 `a_scaled_decomp`: val256(a_norm) + u4 * 2^256 = (u4*2^64 + u3) * 2^192 + lower
    where lower < 2^192 is the val256 of a_norm's bottom 3 limbs.
    ~15 lines via val256 unfolding + bounds.
  - B3.4 `val256_ratio_le_u_total_div_b3_prime`: the target. ~30 lines composing B3.1-B3.3.
  - B4 `q_true_triple_bridge_to_val256_norm`: wrapper around B3.4.
-/

import EvmAsm.Evm64.EvmWordArith.Div128CallSkipClose

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

-- =============================================================================
-- Irreducible bundles for the div128Quot algorithm's intermediate Word values.
-- Used to prevent `maximum recursion depth` when composing Phase 1/Phase 2
-- tight lemmas with A2.S1's deeply nested let-chain hypothesis.
-- (Matches `feedback_bundle_pre_post_no_lets` guidance.)
-- =============================================================================

/-- The algorithm's `un21` output as a function of `(u4, u3, b3')`.
    Full 17-step let-chain: Phase 1a (q1, rhat, hi1 correction), Phase 1b
    (q1c, rhatc, ult correction → q1', rhat'), halfword combine + subtraction. -/
@[irreducible]
def algorithmUn21 (u4 u3 b3' : Word) : Word :=
  let dHi := b3' >>> (32 : BitVec 6).toNat
  let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u3 >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u4 dHi
  let rhat := u4 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  cu_rhat_un1 - cu_q1_dlo

/-- Named unfold for `algorithmUn21`. -/
theorem algorithmUn21_unfold (u4 u3 b3' : Word) :
    algorithmUn21 u4 u3 b3' =
      (let dHi := b3' >>> (32 : BitVec 6).toNat
       let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
       let div_un1 := u3 >>> (32 : BitVec 6).toNat
       let q1 := rv64_divu u4 dHi
       let rhat := u4 - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
       let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
       let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
       let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
       let cu_q1_dlo := q1' * dLo
       cu_rhat_un1 - cu_q1_dlo) := by
  delta algorithmUn21; rfl

/-- The algorithm's Phase-1b output `q1'` as a function of `(u4, u3, b3')`.
    Same let-chain as `algorithmUn21`, but returns `q1'` instead of `un21`.
    Note: takes `u3` as a parameter (even though q1' doesn't directly depend
    on the low bits of u3) so the Phase 1b ult-check input `rhatUn1` —
    which uses `div_un1 = u3 >>> 32` — lines up with the algorithm.
    Marked `@[irreducible]` to keep the 11-step chain from polluting
    type elaboration (matches `algorithmUn21` treatment). -/
@[irreducible]
def algorithmQ1Prime (u4 u3 b3' : Word) : Word :=
  let dHi := b3' >>> (32 : BitVec 6).toNat
  let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u3 >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u4 dHi
  let rhat := u4 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c

/-- Named unfold for `algorithmQ1Prime`. -/
theorem algorithmQ1Prime_unfold (u4 u3 b3' : Word) :
    algorithmQ1Prime u4 u3 b3' =
      (let dHi := b3' >>> (32 : BitVec 6).toNat
       let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
       let div_un1 := u3 >>> (32 : BitVec 6).toNat
       let q1 := rv64_divu u4 dHi
       let rhat := u4 - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
       if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c) := by
  delta algorithmQ1Prime; rfl

/-- The algorithm's Phase-2b output `q0'` as a function of `(u4, u3, b3')`.
    Built on `algorithmUn21` + Phase 2a correction + Phase 2b ult check.
    Marked `@[irreducible]` so Phase 2 tight's internal q0' and
    `div128Quot_toNat_eq_strict`'s internal q0' share the same opaque
    symbol — resolves the q0' syntactic mismatch blocking A2.S1's final
    composition. -/
@[irreducible]
def algorithmQ0Prime (u4 u3 b3' : Word) : Word :=
  let dHi := b3' >>> (32 : BitVec 6).toNat
  let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un21 := algorithmUn21 u4 u3 b3'
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  div128Quot_phase2b_q0' q0c rhat2c dLo div_un0

/-- Named unfold for `algorithmQ0Prime`. -/
theorem algorithmQ0Prime_unfold (u4 u3 b3' : Word) :
    algorithmQ0Prime u4 u3 b3' =
      (let dHi := b3' >>> (32 : BitVec 6).toNat
       let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
       let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
       let un21 := algorithmUn21 u4 u3 b3'
       let q0 := rv64_divu un21 dHi
       let rhat2 := un21 - q0 * dHi
       let hi2 := q0 >>> (32 : BitVec 6).toNat
       let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
       let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
       div128Quot_phase2b_q0' q0c rhat2c dLo div_un0) := by
  delta algorithmQ0Prime; rfl

/-- **Phase 1 tight, wrapped**: Phase 1 tight specialized and folded into
    `algorithmQ1Prime`. Parallel to `algorithmQ0Prime_ge_q_true_0`. -/
theorem algorithmQ1Prime_ge_q_true_1
    (u4 u3 b3' : Word)
    (hdHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hdLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hu4_lt_dHi_pow32 :
      u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (hu4_lt_vTop :
      u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) /
      ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) ≤
    (algorithmQ1Prime u4 u3 b3').toNat := by
  rw [algorithmQ1Prime_unfold]
  exact
    div128Quot_q1_prime_ge_q_true_1_of_uHi_lt_dHi_mul_pow32
      u4
      (b3' >>> (32 : BitVec 6).toNat)
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
      u3
      hdHi_ge hdHi_lt hdLo_lt hu4_lt_dHi_pow32 hu4_lt_vTop

/-- **div128Quot decomposition, wrapped**: `div128Quot.toNat = algorithmQ1Prime.toNat
    * 2^32 + algorithmQ0Prime.toNat` under hcall + `q0' < 2^32`. Folds
    `div128Quot_toNat_eq_strict`'s internal q0'/q1' into the wrappers. -/
theorem div128Quot_toNat_eq_algorithmQ1_Q0
    (u4 u3 b3' : Word)
    (hdHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hdLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hu4_lt_vTop :
      u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat)
    (hq0_lt : (algorithmQ0Prime u4 u3 b3').toNat < 2^32) :
    (div128Quot u4 u3 b3').toNat =
      (algorithmQ1Prime u4 u3 b3').toNat * 2^32 +
      (algorithmQ0Prime u4 u3 b3').toNat := by
  -- Step 1: rewrite div128Quot as halfword_combine of our wrappers.
  rw [show div128Quot u4 u3 b3' =
    ((algorithmQ1Prime u4 u3 b3') <<< (32 : BitVec 6).toNat) |||
    (algorithmQ0Prime u4 u3 b3') from by
      unfold div128Quot
      rw [algorithmQ1Prime_unfold, algorithmQ0Prime_unfold]
      simp only [algorithmUn21_unfold]]
  -- Step 2: halfword_combine.toNat = q1'.toNat * 2^32 + q0'.toNat.
  have hq1_lt : (algorithmQ1Prime u4 u3 b3').toNat < 2^32 := by
    rw [algorithmQ1Prime_unfold]
    exact
      div128Quot_q1_prime_lt_pow32 u4 (b3' >>> (32 : BitVec 6).toNat)
        ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) u3
        hdHi_ge hdHi_lt hdLo_lt hu4_lt_vTop
  rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl]
  exact EvmWord.halfword_combine _ _ hq1_lt hq0_lt

/-- **Phase 2 tight, wrapped**: Phase 2 tight specialized to our inputs
    and folded into the `algorithmQ0Prime` wrapper. Removes the q0'
    syntactic-mismatch blocker for downstream composition. -/
theorem algorithmQ0Prime_ge_q_true_0
    (u4 u3 b3' : Word)
    (hdHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hdLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (h_un21_lt_dHi_pow32 :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_vTop :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    ((algorithmUn21 u4 u3 b3').toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) /
      ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) ≤
    (algorithmQ0Prime u4 u3 b3').toNat := by
  rw [algorithmQ0Prime_unfold]
  exact
    div128Quot_q0_prime_ge_q_true_0_of_un21_lt_dHi_mul_pow32
      (algorithmUn21 u4 u3 b3')
      (b3' >>> (32 : BitVec 6).toNat)
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
      u3
      hdHi_ge hdHi_lt hdLo_lt h_un21_lt_dHi_pow32 h_un21_lt_vTop

/-- **Bridge sub-A (weak, `+2`)**: `algorithmQ1Prime.toNat ≤ q_true_1 + 2`
    stepping stone. Combines Phase 1b's q1' ≤ u4/dHi with Knuth-B trial_le
    giving u4/dHi ≤ q_true_1 + 2 (under normalization). -/
theorem algorithmQ1Prime_le_q_true_1_plus_two
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat + 2 := by
  set dHi := b3' >>> (32 : BitVec 6).toNat with hdHi_def
  set dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat with hdLo_def
  set div_un1 := u3 >>> (32 : BitVec 6).toNat with hdiv_un1_def
  have h_dHi_lt : dHi.toNat < 2^32 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dLo_lt : dLo.toNat < 2^32 := by
    show ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_div_un1_lt : div_un1.toNat < 2^32 := by
    show (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_vTop_decomp : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact hu4_lt_b3'
  have h_dHi_ne : dHi ≠ 0 := by
    intro heq
    have : dHi.toNat = 0 := by rw [heq]; rfl
    omega
  have h_trial_le :=
    EvmWord.trial_quotient_le u4.toNat div_un1.toNat dHi.toNat dLo.toNat
      h_dHi_lt h_dLo_lt h_div_un1_lt h_u4_lt_vTop h_dHi_ge
  rw [algorithmQ1Prime_unfold]
  simp only []
  let rhatUn1 : Word := (((if (rv64_divu u4 dHi) >>> (32 : BitVec 6).toNat = 0
      then u4 - rv64_divu u4 dHi * dHi
      else u4 - rv64_divu u4 dHi * dHi + dHi) <<< (32 : BitVec 6).toNat)
      ||| div_un1)
  have h_q1'_le := (div128Quot_phase1b_quotient_bound u4 dHi h_dHi_ne h_dHi_lt
    dLo rhatUn1).2
  rw [h_vTop_decomp]
  exact Nat.le_trans h_q1'_le (by omega)

/-- **_plus_one sub-step 1**: Phase 1a Euclidean at Nat level. Under
    hcall, `q1c.toNat * dHi.toNat + rhatc.toNat = u4.toNat`.
    Direct wrap of `div128Quot_first_round_post`. -/
theorem algorithmQ1Prime_step1_phase1a_euclidean
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    q1c.toNat * dHi.toNat + rhatc.toNat = u4.toNat := by
  have h_dHi_ne : (b3' >>> (32 : BitVec 6).toNat) ≠ 0 := by
    intro heq
    have h : (b3' >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [heq]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  exact div128Quot_first_round_post u4 (b3' >>> (32 : BitVec 6).toNat)
    h_dHi_ne h_dHi_lt

/-- **_plus_one sub-step 2**: KB-LB3 wrapped. `q_true_1 ≤ q1c.toNat`. -/
theorem algorithmQ1Prime_step2_q1c_ge_q_true_1
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
      ≤ q1c.toNat := by
  have h_dHi_ne : (b3' >>> (32 : BitVec 6).toNat) ≠ 0 := by
    intro heq
    have h : (b3' >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [heq]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_div_un1_lt : (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    h_v_eq ▸ hu4_lt_b3'
  rw [h_v_eq]
  exact div128Quot_q1c_ge_q_true_1 u4 (b3' >>> (32 : BitVec 6).toNat)
    ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
    (u3 >>> (32 : BitVec 6).toNat) h_dHi_ne h_div_un1_lt h_u4_lt_vTop

/-- **_plus_one sub-step 3**: `q1c ≤ q_true_1 + 2` via trial_quotient_le
    + Phase 1a monotonicity. -/
theorem algorithmQ1Prime_step3_q1c_le_q_true_1_plus_two
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat + 2 := by
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_div_un1_lt : (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    h_v_eq ▸ hu4_lt_b3'
  have h_dHi_ne : (b3' >>> (32 : BitVec 6).toNat) ≠ 0 := by
    intro heq
    have : (b3' >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [heq]; rfl
    omega
  -- q1.toNat = u4.toNat / dHi.toNat
  have h_q1_eq : (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)).toNat =
      u4.toNat / (b3' >>> (32 : BitVec 6).toNat).toNat :=
    EvmWord.rv64_divu_toNat u4 _ h_dHi_ne
  -- q1c ≤ q1 (Phase 1a monotonicity).
  have h_q1c_le_q1 := div128Quot_q1c_le_q1 u4 (b3' >>> (32 : BitVec 6).toNat)
  -- q1 ≤ q_true_1 + 2 (trial_quotient_le).
  have h_q1_le :=
    EvmWord.trial_quotient_le u4.toNat (u3 >>> (32 : BitVec 6).toNat).toNat
      (b3' >>> (32 : BitVec 6).toNat).toNat
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
      h_dHi_lt h_dLo_lt h_div_un1_lt h_u4_lt_vTop h_dHi_ge
  rw [h_v_eq]
  omega

/-- **_plus_one sub-step 4**: `rhatc.toNat < 2^32` under `u4 < dHi*2^32`.
    Direct wrapping of `div128Quot_rhatc_lt_pow32_of_uHi_lt_dHi_mul_pow32`. -/
theorem algorithmQ1Prime_step4_rhatc_lt_pow32
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    rhatc.toNat < 2^32 := by
  have h_dHi_ne : (b3' >>> (32 : BitVec 6).toNat) ≠ 0 := by
    intro heq
    have h : (b3' >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [heq]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  exact div128Quot_rhatc_lt_pow32_of_uHi_lt_dHi_mul_pow32 u4
    (b3' >>> (32 : BitVec 6).toNat) h_dHi_ne hu4_lt_dHi_pow32 h_dHi_lt

/-- **_plus_one sub-step 5**: Word↔Nat ult bridge. Under hcall,
    `BitVec.ult rhatUn1 (q1c*dLo) ↔ q1c.toNat * dLo.toNat
     > rhatc.toNat * 2^32 + div_un1.toNat`. -/
theorem algorithmQ1Prime_step5_ult_bridge
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    (BitVec.ult rhatUn1 (q1c * dLo) = true) ↔
      (q1c.toNat * dLo.toNat >
       rhatc.toNat * 2^32 + div_un1.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc rhatUn1
  have h_dHi_lt : dHi.toNat < 2^32 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dLo_lt : dLo.toNat < 2^32 := by
    show ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_div_un1_lt : div_un1.toNat < 2^32 := by
    show (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := h_v_eq ▸ hu4_lt_b3'
  -- q1c ≤ 2^32 (Phase 1a bound).
  have h_q1c_le : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 u4 dHi dLo h_dHi_ge h_dLo_lt h_u4_lt_vTop
  -- rhatc < 2^32 (step4).
  have h_rhatc_lt : rhatc.toNat < 2^32 :=
    algorithmQ1Prime_step4_rhatc_lt_pow32 u4 u3 b3' hb3'_ge hu4_lt_dHi_pow32
  -- q1c * dLo no-wrap.
  have h_q1c_dLo_lt : q1c.toNat * dLo.toNat < 2^64 := by
    have : q1c.toNat * dLo.toNat ≤ 2^32 * (2^32 - 1) := by
      have h : dLo.toNat ≤ 2^32 - 1 := by omega
      exact Nat.mul_le_mul h_q1c_le h
    have : (2^32 : Nat) * (2^32 - 1) = 2^64 - 2^32 := by decide
    omega
  -- rhatUn1.toNat via halfword_combine.
  have h_rhatUn1_eq : rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat := by
    show ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1).toNat = _
    rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl]
    exact EvmWord.halfword_combine _ _ h_rhatc_lt h_div_un1_lt
  -- Apply ult_iff and chain the equalities.
  rw [EvmWord.ult_iff, BitVec.toNat_mul, Nat.mod_eq_of_lt h_q1c_dLo_lt,
      h_rhatUn1_eq]

/-- **_plus_one sub-step 6**: Word-level if → Nat-level if bridge for q1'.
    The algorithm's q1' (Word if on ult) equals at the .toNat level the
    Nat if on the underlying comparison. Decomposes into 2 cases: when
    ult fires (q1' = q1c - 1, needs q1c > 0 via phase1b_check_implies_q1c_pos),
    and when it doesn't (q1' = q1c).

    Body deferred — requires careful handling of `q1c + signExtend12 4095`
    as Nat subtraction by 1 (safe via phase1b_check_implies_q1c_pos). -/
theorem algorithmQ1Prime_step6_word_nat_if_bridge
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    (algorithmQ1Prime u4 u3 b3').toNat =
      (if q1c.toNat * dLo.toNat > rhatc.toNat * 2^32 + div_un1.toNat
       then q1c.toNat - 1 else q1c.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc
  have h_ult_bridge := algorithmQ1Prime_step5_ult_bridge u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32
  simp only [] at h_ult_bridge
  rw [algorithmQ1Prime_unfold]
  show (if BitVec.ult _ (q1c * dLo) then q1c + signExtend12 4095 else q1c).toNat = _
  by_cases h_word_ult : BitVec.ult
      ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1) (q1c * dLo) = true
  · rw [if_pos h_word_ult]
    have h_nat := h_ult_bridge.mp h_word_ult
    rw [if_pos h_nat]
    have h_q1c_pos :=
      div128Quot_phase1b_check_implies_q1c_pos q1c dLo
        ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1) h_word_ult
    rw [BitVec.toNat_add, signExtend12_4095_toNat]
    have h_q1c_lt : q1c.toNat < 2^64 := q1c.isLt
    rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : q1c.toNat - 1 < 2^64)]
  · rw [if_neg h_word_ult]
    have h_not_nat : ¬ (q1c.toNat * dLo.toNat > rhatc.toNat * 2^32 + div_un1.toNat) := by
      intro h
      exact h_word_ult (h_ult_bridge.mpr h)
    rw [if_neg h_not_nat]

/-- **Bridge sub-A** (Knuth-B upper at Phase 1b): under standard hcall,
    `algorithmQ1Prime.toNat ≤ (u4*2^32 + div_un1) / b3' + 1`.

    **Composition** (once all 6 sub-steps are filled):
    1. `algorithmQ1Prime_step1_phase1a_euclidean` — q1c*dHi + rhatc = u4.
    2. `algorithmQ1Prime_step2_q1c_ge_q_true_1` — q_true_1 ≤ q1c.
    3. `algorithmQ1Prime_step3_q1c_le_q_true_1_plus_two` — q1c ≤ q_true_1 + 2.
    4. `half_round_overestimate_le_one` (or `correction_step_overestimate_le_one`)
       — q' ≤ q_true_1 + 1 where q' is the Nat-level if-then-else.
    5. `algorithmQ1Prime_step5_ult_bridge` — Word ult ↔ Nat comparison.
    6. `algorithmQ1Prime_step6_word_nat_if_bridge` — bridge algorithmQ1Prime.toNat
       to the Nat-level if-then-else (given step5's Word↔Nat bridge). -/
theorem algorithmQ1Prime_le_q_true_1_plus_one
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat + 1 := by
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_eucl := algorithmQ1Prime_step1_phase1a_euclidean u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32
  have h_q1c_le := algorithmQ1Prime_step3_q1c_le_q_true_1_plus_two u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32
  have h_if_bridge := algorithmQ1Prime_step6_word_nat_if_bridge u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32
  simp only [] at h_eucl h_q1c_le h_if_bridge
  rw [h_v_eq] at h_q1c_le
  -- Rewrite goal using step6 (algorithmQ1Prime.toNat = Nat-if).
  rw [h_if_bridge]
  -- Rewrite divisor using h_v_eq.
  conv_rhs => rw [h_v_eq]
  have h_vTop_pos :
      0 < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
          ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq]; have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_q1c_mul_le :
      (if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
           (32 : BitVec 6).toNat = 0 then
        rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)
      else rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) + signExtend12 4095).toNat *
      (b3' >>> (32 : BitVec 6).toNat).toNat ≤ u4.toNat := by omega
  have h_rhatc_eq :
      (if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
           (32 : BitVec 6).toNat = 0 then
        u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
          (b3' >>> (32 : BitVec 6).toNat)
      else u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
          (b3' >>> (32 : BitVec 6).toNat) + (b3' >>> (32 : BitVec 6).toNat)).toNat =
      u4.toNat -
      (if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
           (32 : BitVec 6).toNat = 0 then
        rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)
      else rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) + signExtend12 4095).toNat *
      (b3' >>> (32 : BitVec 6).toNat).toNat := by omega
  exact EvmWord.correction_step_overestimate_le_one u4.toNat
    (u3 >>> (32 : BitVec 6).toNat).toNat
    (b3' >>> (32 : BitVec 6).toNat).toNat
    ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
    ((if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
           (32 : BitVec 6).toNat = 0 then
        rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)
      else rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) + signExtend12 4095).toNat)
    ((if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
           (32 : BitVec 6).toNat = 0 then
        u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
          (b3' >>> (32 : BitVec 6).toNat)
      else u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
          (b3' >>> (32 : BitVec 6).toNat) + (b3' >>> (32 : BitVec 6).toNat)).toNat)
    (B := 2^32) h_vTop_pos h_rhatc_eq h_q1c_mul_le h_q1c_le

/-- **_of_tight sub-case "exact"**: when `q1' = q_true_1` (Phase 1b exactly
    tight), the algorithm's un21 equals the mathematical remainder r1_math.

    **TODO** (~40 lines): from Phase 1b Euclidean + KB-3m (un21 additive
    identity under no-wrap, which holds when q1' = q_true_1). -/
theorem algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_q1_prime_eq : (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (algorithmUn21 u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat := by
  -- Setup standard preconditions.
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    h_v_eq ▸ hu4_lt_b3'
  -- Apply KB-3m (un21 additive identity) with rhatUn1 as the actual one.
  -- We need: un21 + (rhat'/2^32) * 2^64 + q1' * vTop = u4*2^32 + div_un1
  -- under no-wrap B ≤ A.
  -- Strategy: show no-wrap via contradiction (if wrap, Word bound violated).
  -- This requires considerable Word analysis; deferred.
  sorry

/-- **_of_tight sub-case "off-by-one"**: when `q1' = q_true_1 + 1` (Phase 1b
    false-alarms once), the algorithm's un21 = r1_math + (2^64 - V), which is
    ≥ r1_math.

    **TODO** (~40 lines): from Phase 1b Euclidean + Word wrap analysis. -/
theorem algorithmUn21_ge_r1_math_of_q1_prime_eq_q_true_1_plus_one
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_q1_prime_eq : (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat + 1) :
    (algorithmUn21 u4 u3 b3').toNat ≥
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat := by
  sorry

/-- **Bridge sub-B** (algebraic consequence): given `q1' ≤ q_true_1 + 1` and
    `un21 < dHi*2^32`, the algorithm's un21 cannot be less than `r1_math`. -/
theorem algorithmUn21_eq_r1_math_of_tight
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_dHi_pow32 :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_tight :
      (algorithmUn21 u4 u3 b3').toNat <
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat) :
    False := by
  -- Derive q1' ∈ {q_true_1, q_true_1 + 1}.
  have h_q1_le := algorithmQ1Prime_le_q_true_1_plus_one u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32
  -- Lower bound: q1' ≥ q_true_1 (wrapped form). Need to establish.
  have h_q1_ge : (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
      ≤ (algorithmQ1Prime u4 u3 b3').toNat := by
    -- Use algorithmQ1Prime_ge_q_true_1 (already proven) + dHi bounds derivation.
    have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
      rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
    have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
      rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      have : b3'.toNat < 2^64 := b3'.isLt
      exact Nat.div_lt_of_lt_mul (by omega)
    have h_dLo_lt :
        ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
      rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
        (b3' <<< (32 : BitVec 6).toNat : Word).isLt
      exact Nat.div_lt_of_lt_mul (by omega)
    have h_v_eq := div128Quot_vTop_decomp b3'
    have h_u4_lt_vTop : u4.toNat <
        (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
        ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
      h_v_eq ▸ hu4_lt_b3'
    have h := algorithmQ1Prime_ge_q_true_1 u4 u3 b3'
      h_dHi_ge h_dHi_lt h_dLo_lt hu4_lt_dHi_pow32 h_u4_lt_vTop
    rw [← h_v_eq] at h; exact h
  -- q1' is q_true_1 or q_true_1 + 1.
  set q_true_1 := (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
  have h_q1'_or : (algorithmQ1Prime u4 u3 b3').toNat = q_true_1 ∨
                  (algorithmQ1Prime u4 u3 b3').toNat = q_true_1 + 1 := by
    omega
  rcases h_q1'_or with h_eq | h_eq_plus_one
  · -- Case q1' = q_true_1: un21 = r1_math. Contradicts h_tight.
    have h_un21_eq := algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1 u4 u3 b3'
      hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32 h_eq
    omega
  · -- Case q1' = q_true_1 + 1: un21 ≥ r1_math. Contradicts h_tight.
    have h_un21_ge := algorithmUn21_ge_r1_math_of_q1_prime_eq_q_true_1_plus_one u4 u3 b3'
      hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32 h_eq_plus_one
    omega

/-- **Bridge**: under standard hcall + `un21 < dHi*2^32`, the algorithm's un21
    is at least the mathematical remainder `(u4*2^32 + div_un1) % b3'`.

    Composes via `by_contra` + the `algorithmUn21_eq_r1_math_of_tight`
    structural impossibility of un21 < r1_math (under hcall + un21 < dHi*2^32,
    Phase 1b's ult correction guarantees un21 ≥ r1_math — if
    un21 < r1_math held, Phase 1b would have undercorrected, contradicting
    its design).

    **TODO** (~80 lines in the sub-lemma): formalize via KB-3j (un21 wrap
    case split) + Phase 1b ult-check semantics. -/
theorem algorithmUn21_ge_r1_math
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_dHi_pow32 :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    (algorithmUn21 u4 u3 b3').toNat ≥
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat := by
  by_contra h_lt
  push Not at h_lt
  exact algorithmUn21_eq_r1_math_of_tight u4 u3 b3' hb3'_ge hu4_lt_b3'
    hu4_lt_dHi_pow32 h_un21_lt_dHi_pow32 h_lt

-- =============================================================================
-- §A — Core Knuth-B lower bound (128/64 level)
--
-- The main theorem uses `div128Quot_ge_q_true_normalized` (A4), which in
-- turn uses `div128Quot_qHat_plus_one_times_b3_gt_u` (A2). The Knuth-B
-- UPPER form (previously scaffolded as "A1") is not on the critical path
-- and has been dropped to simplify the file.
--
-- A2's proof is decomposed into sub-lemmas (A2.S1–A2.S4 below).
-- =============================================================================

/-- **A2.S1.alg** (pure algebra): if `q1' * 2^32 + q0' ≥ u / vTop`, then
    `(q1'*2^32 + q0' + 1) * vTop > u`. Wraps `Nat.div` semantics.

    Used downstream to convert the "tight qHat" statement (qHat ≥ q_true)
    into the "gap" statement (qHat + 1 > q_true), which is what A2 asks. -/
theorem nat_succ_mul_gt_of_div_le (q u vTop : Nat) (hvTop_pos : 0 < vTop)
    (h_div_le : u / vTop ≤ q) :
    (q + 1) * vTop > u := by
  have h_div_mod : u = vTop * (u / vTop) + u % vTop := (Nat.div_add_mod u vTop).symm
  have h_mod_lt : u % vTop < vTop := Nat.mod_lt u hvTop_pos
  have h_mul : vTop * (u / vTop) ≤ vTop * q := Nat.mul_le_mul_left _ h_div_le
  calc u = vTop * (u / vTop) + u % vTop := h_div_mod
    _ ≤ vTop * q + u % vTop := by omega
    _ < vTop * q + vTop := by omega
    _ = (q + 1) * vTop := by ring

/-- **A2.S1.comp** (pure algebra): tight per-halfword combine.
    If `q1' ≥ q_true_1` AND `q0' ≥ q_true_0` AND `q0' < 2^32` AND
    `q_true_0 < 2^32`, then `q1'*2^32 + q0' ≥ q_true_1*2^32 + q_true_0`.
    Used to combine Phase 1 and Phase 2 tight bounds into the halfword
    `qHat ≥ q_true` bound. -/
theorem halfword_combine_ge_of_tight (q1' q0' q_true_1 q_true_0 : Nat)
    (h_q1'_ge : q1' ≥ q_true_1)
    (h_q0'_ge : q0' ≥ q_true_0) :
    q1' * 2^32 + q0' ≥ q_true_1 * 2^32 + q_true_0 := by
  have h1 : q_true_1 * 2^32 ≤ q1' * 2^32 := Nat.mul_le_mul_right _ h_q1'_ge
  exact Nat.add_le_add h1 h_q0'_ge

/-- **A2.S1.div_id** (pure Nat): two-step schoolbook division identity.
    `(A*2^64 + a1*2^32 + a0) / V = ((A*2^32+a1)/V)*2^32 + ((rem*2^32+a0)/V)`
    where `rem = (A*2^32+a1) % V`. This is the halfword-pair decomposition of
    the 128-bit division, showing that successive halfword divisions recover
    the true quotient. Foundational for the Knuth-B tight-phases reduction. -/
theorem two_step_div_identity (A a1 a0 V : Nat) (hV_pos : 0 < V) :
    (A * 2^64 + a1 * 2^32 + a0) / V =
    ((A * 2^32 + a1) / V) * 2^32 +
    ((((A * 2^32 + a1) % V) * 2^32 + a0) / V) := by
  set q1 := (A * 2^32 + a1) / V with hq1_def
  set r1 := (A * 2^32 + a1) % V with hr1_def
  set q0 := (r1 * 2^32 + a0) / V with hq0_def
  set r0 := (r1 * 2^32 + a0) % V with hr0_def
  have h_decomp_1 : A * 2^32 + a1 = V * q1 + r1 := (Nat.div_add_mod _ V).symm
  have h_decomp_0 : r1 * 2^32 + a0 = V * q0 + r0 := (Nat.div_add_mod _ V).symm
  have h_r0_lt : r0 < V := Nat.mod_lt _ hV_pos
  have h_full : A * 2^64 + a1 * 2^32 + a0 = r0 + (q1 * 2^32 + q0) * V := by
    calc A * 2^64 + a1 * 2^32 + a0
        = (A * 2^32 + a1) * 2^32 + a0 := by ring
      _ = (V * q1 + r1) * 2^32 + a0 := by rw [h_decomp_1]
      _ = V * q1 * 2^32 + (r1 * 2^32 + a0) := by ring
      _ = V * q1 * 2^32 + (V * q0 + r0) := by rw [h_decomp_0]
      _ = r0 + (q1 * 2^32 + q0) * V := by ring
  rw [h_full, Nat.add_mul_div_right _ _ hV_pos, Nat.div_eq_of_lt h_r0_lt,
      Nat.zero_add]

/-- **A2.S1.body** (pure Nat + abstract phase hypotheses): if the algorithm's
    qHat decomposes as `q1'*2^32 + q0'` (halfword combine output) AND the
    phase-wise tight bounds `q_true_1 ≤ q1'` and `q_true_0 ≤ q0'` hold AND
    the halfword division identity ties `q_true_1`, `q_true_0` to the true
    128/64 quotient, then A2's conclusion follows.

    This is the clean "last-mile" composition: given the phase tight bounds
    abstractly, derive `(qHat+1)*vTop > u`. Pure Nat — doesn't touch the
    algorithm's let-chains. -/
theorem qHat_plus_one_gt_u_via_tight_phases
    (u q1' q0' q_true_1 q_true_0 V : Nat)
    (hV_pos : 0 < V)
    (h_qHat_decomp : u / V = q_true_1 * 2^32 + q_true_0)
    (h_ph1 : q_true_1 ≤ q1')
    (h_ph2 : q_true_0 ≤ q0') :
    (q1' * 2^32 + q0' + 1) * V > u := by
  have h_ge : u / V ≤ q1' * 2^32 + q0' := by
    rw [h_qHat_decomp]
    exact halfword_combine_ge_of_tight q1' q0' q_true_1 q_true_0 h_ph1 h_ph2
  exact nat_succ_mul_gt_of_div_le (q1' * 2^32 + q0') u V hV_pos h_ge

/-- **A2.S1**: Case "normal" — when `un21 < dHi*2^32` (Phase 2 Case A),
    both Phase 1 and Phase 2 tight bounds from existing infrastructure apply
    directly.

    Takes the stricter `un21 < dHi*2^32` as hypothesis (stronger than
    `un21 < vTop`), which covers exactly the region where
    `div128Quot_q0_prime_ge_q_true_0_of_un21_lt_dHi_mul_pow32` is applicable.

    **Sub-decomposition**: closes via:
    1. A2.S1.q1_eq_true_1: `q1'.toNat = q_true_1` (Phase 1 tight).
    2. A2.S1.un21_eq_true_rem: algorithm un21 = mathematical remainder.
    3. Phase 2 tight `_of_un21_lt_dHi_mul_pow32` (applies directly).
    4. `two_step_div_identity` + `qHat_plus_one_gt_u_via_tight_phases`.

    **TODO**: ~100 lines. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_normal
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_dHi_pow32 :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  -- Standard precondition derivations.
  have hb3'_pos : 0 < b3'.toNat := by omega
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_vTop_decomp : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  -- u3 halfword split: u3 = div_un1 * 2^32 + div_un0
  -- where div_un1 = u3 >>> 32 (high 32 bits), div_un0 = u3 % 2^32 (low 32 bits).
  have h_u3_decomp : u3.toNat =
      (u3 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp u3
  -- div_un1 and div_un0 bounds.
  have h_div_un1_lt :
      (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_div_un0_lt :
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (u3 <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (u3 <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  -- All Phase tight bounds + halfword decomp via the wrapped lemmas.
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    Nat.lt_of_lt_of_le hu4_lt_dHi_pow32 (Nat.le_add_right _ _)
  have h_un21_lt_vTop : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    Nat.lt_of_lt_of_le h_un21_lt_dHi_pow32 (Nat.le_add_right _ _)
  -- Phase 1 tight (wrapped).
  have h_ph1_tight :=
    algorithmQ1Prime_ge_q_true_1 u4 u3 b3'
      h_dHi_ge h_dHi_lt h_dLo_lt hu4_lt_dHi_pow32 h_u4_lt_vTop
  -- Phase 2 tight (wrapped).
  have h_ph2_tight :=
    algorithmQ0Prime_ge_q_true_0 u4 u3 b3'
      h_dHi_ge h_dHi_lt h_dLo_lt h_un21_lt_dHi_pow32 h_un21_lt_vTop
  -- q0' < 2^32 (wrapped form — derive via algorithmQ0Prime_unfold).
  have h_q0'_lt : (algorithmQ0Prime u4 u3 b3').toNat < 2^32 := by
    rw [algorithmQ0Prime_unfold]
    exact
      div128Quot_q0_prime_lt_pow32 (algorithmUn21 u4 u3 b3')
        (b3' >>> (32 : BitVec 6).toNat)
        ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) u3
        h_dHi_ge h_dHi_lt h_dLo_lt h_un21_lt_vTop
  -- qHat halfword decomp (wrapped).
  have h_qHat_decomp :=
    div128Quot_toNat_eq_algorithmQ1_Q0 u4 u3 b3'
      h_dHi_ge h_dHi_lt h_dLo_lt
      (by rw [h_vTop_decomp] at hu4_lt_b3'; exact hu4_lt_b3') h_q0'_lt
  -- True-quotient halfword decomposition.
  have h_two_step :=
    two_step_div_identity u4.toNat
      (u3 >>> (32 : BitVec 6).toNat).toNat
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
      b3'.toNat hb3'_pos
  -- Bridge: algorithm un21 ≥ r1_math.
  have h_un21_ge_rmath :=
    algorithmUn21_ge_r1_math u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32
      h_un21_lt_dHi_pow32
  -- Monotonicity: lift Phase 2 tight from algorithm un21 to r1_math.
  have h_mono_num :
      (u4.toNat * 2 ^ 32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat * 2 ^ 32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat ≤
      (algorithmUn21 u4 u3 b3').toNat * 2 ^ 32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    apply Nat.add_le_add_right
    exact Nat.mul_le_mul_right _ h_un21_ge_rmath
  have h_q_true_0_le :
      ((u4.toNat * 2 ^ 32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat * 2 ^ 32 +
       ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) /
      ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
       ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) ≤
      (algorithmQ0Prime u4 u3 b3').toNat :=
    Nat.le_trans (Nat.div_le_div_right h_mono_num) h_ph2_tight
  -- Rewrite goal.
  rw [h_u3_decomp, h_qHat_decomp]
  have h_u_rewrite : u4.toNat * 2^64 +
      ((u3 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
       ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) =
      u4.toNat * 2^64 +
        (u3 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
        ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by ring
  rw [h_u_rewrite]
  -- Use h_vTop_decomp to normalize b3'.
  have h_v_eq := h_vTop_decomp.symm
  rw [h_v_eq] at h_q_true_0_le
  -- Normalize h_two_step and h_ph1_tight by converting divisor b3' ↔ decomp.
  rw [← h_vTop_decomp] at h_ph1_tight
  -- Apply the final composition.
  apply qHat_plus_one_gt_u_via_tight_phases _ _ _ _ _ _ hb3'_pos h_two_step h_ph1_tight
  exact h_q_true_0_le

/-- **A2.S2.narrow_u4_tight_un21**: narrow u4 (Phase 1a corrects) AND
    un21 < dHi*2^32 (Phase 2 Case A works). The compensation comes
    from Phase 1a's q1c = q1 - 1 getting propagated. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_tight_un21
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_ge : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  sorry

/-- **A2.S2.narrow_u4_wide_un21**: narrow u4 (Phase 1a corrects) AND
    un21 ≥ dHi*2^32. Compounded compensation from Phase 1a + Phase 2. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_wide_un21
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_ge : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge : (algorithmUn21 u4 u3 b3').toNat ≥
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  sorry

/-- **A2.S2.narrow_u4**: compensation case when `u4 ≥ dHi*2^32`.
    Dispatches to tight-un21 / wide-un21 sub-cases. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_ge : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_tight_un21
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_ge h
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_wide_un21
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_ge (by omega)

/-- **A2.S2.wide_un21_narrow**: Phase 2 narrow-range false-alarm
    (un21 ∈ [dHi*2^32, vTop)). Phase 1 still tight. Phase 2 may
    false-alarm producing q0' = q_true_0 - 1, requiring halfword
    combine to absorb the gap. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_narrow
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge_dHi_pow32 : (algorithmUn21 u4 u3 b3').toNat ≥
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_vTop : (algorithmUn21 u4 u3 b3').toNat < b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  sorry

/-- **A2.S2.wide_un21_wide**: un21 ≥ vTop means Phase 1 false-alarmed.
    Need Phase 1+2 global compensation via halfword combine truncation. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_wide
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge_vTop : (algorithmUn21 u4 u3 b3').toNat ≥ b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  sorry

/-- **A2.S2.wide_un21**: compensation case when `u4 < dHi*2^32` but
    `un21 ≥ dHi*2^32`. Dispatches to narrow/wide sub-cases. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge : (algorithmUn21 u4 u3 b3').toNat ≥
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h : (algorithmUn21 u4 u3 b3').toNat < b3'.toNat
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_narrow
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt h_un21_ge h
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_wide
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt (by omega)

/-- **A2.S2**: Case "compensation" — when `u4 ≥ dHi*2^32 ∨ un21 ≥ dHi*2^32`.
    Dispatches to `_narrow_u4` or `_wide_un21` sub-cases. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_compensation
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (h_compensation : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 ∨
      (algorithmUn21 u4 u3 b3').toNat ≥
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases hu4 : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4 u4 u3 b3' hb3'_ge
      hu4_lt_b3' hu4
  · push Not at hu4
    have h_un21 : (algorithmUn21 u4 u3 b3').toNat ≥
        (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 := by
      rcases h_compensation with h | h
      · omega
      · exact h
    exact div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21 u4 u3 b3' hb3'_ge
      hu4_lt_b3' hu4 h_un21

/-- **A2**: Knuth-B lower form (divisibility). `(qHat + 1) * b3' > u`.
    Composed via case split on `un21 < dHi*2^32` (normal) vs
    `un21 ≥ dHi*2^32` (compensation). -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h_u4 :
    u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · by_cases h_un21 :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
    · exact div128Quot_qHat_plus_one_times_b3_gt_u_normal u4 u3 b3' hb3'_ge
        hu4_lt_b3' h_u4 h_un21
    · apply div128Quot_qHat_plus_one_times_b3_gt_u_compensation u4 u3 b3' hb3'_ge hu4_lt_b3'
      right; omega
  · apply div128Quot_qHat_plus_one_times_b3_gt_u_compensation u4 u3 b3' hb3'_ge hu4_lt_b3'
    left; omega

/-- **A4** (the §A target, derived from A2). -/
theorem div128Quot_ge_q_true_normalized
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    (u4.toNat * 2^64 + u3.toNat) / b3'.toNat ≤
      (div128Quot u4 u3 b3').toNat := by
  have hb3'_pos : 0 < b3'.toNat := by
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_core := div128Quot_qHat_plus_one_times_b3_gt_u u4 u3 b3' hb3'_ge hu4_lt_b3'
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb3'_pos).mpr h_core)

-- =============================================================================
-- §B — Bridge from val256 to 128/64 (normalization)
-- =============================================================================

/-- **B3.1**: pure Nat truncation-division identity.
    `(A * K + L) / (B * K) = A / B` when `0 < K, 0 < B, L < K`.

    Proof: A = B*q + r with r < B. Then A*K + L = B*K*q + (r*K + L) with
    r*K + L < B*K. Apply Nat.add_mul_div_right / Nat.div_eq_of_lt_of_lt. -/
theorem nat_trunc_div_add_lt (A B K L : Nat)
    (hK_pos : 0 < K) (hB_pos : 0 < B) (hL_lt : L < K) :
    (A * K + L) / (B * K) = A / B := by
  have hBK_pos : 0 < B * K := Nat.mul_pos hB_pos hK_pos
  have hA_eq : A = B * (A / B) + A % B := (Nat.div_add_mod A B).symm
  have hr_lt : A % B < B := Nat.mod_lt A hB_pos
  have h_expand : A * K + L = (A / B) * (B * K) + ((A % B) * K + L) := by
    conv_lhs => rw [hA_eq]
    ring
  have h_rem_bound : (A % B) * K + L < B * K := by
    have h_rK : (A % B) * K ≤ (B - 1) * K := Nat.mul_le_mul_right _ (by omega)
    have h_step : (B - 1) * K + K = B * K := by
      have : B = (B - 1) + 1 := by omega
      conv_rhs => rw [this]
      ring
    omega
  rw [h_expand]
  rw [show A / B * (B * K) + (A % B * K + L) = (A % B * K + L) + B * K * (A / B) from by ring]
  rw [Nat.add_mul_div_left _ _ hBK_pos]
  rw [Nat.div_eq_of_lt h_rem_bound]
  omega

/-- **B3.2**: val256(b_norm) is at least b3' * 2^192.
    Trivial from val256 definition (b3' is the top limb, other limbs ≥ 0). -/
theorem val256_ge_top_limb_mul_pow192 (b0 b1 b2 b3 : Word) :
    val256 b0 b1 b2 b3 ≥ b3.toNat * 2^192 := by
  unfold val256; omega

/-- **B3.3**: decomposition of the normalized+overflow dividend.
    `val256(a_norm) + u4 * 2^256 = (u4*2^64 + u3) * 2^192 + lower` where
    `lower = val256(a_norm.getLimbN 0, 1, 2, 0) < 2^192` (bottom 3 limbs).
    The u3 is a_norm's top limb.

    Specialized form: takes the 4 normalized limbs explicitly. -/
theorem a_scaled_decomp (u_norm0 u_norm1 u_norm2 u3 u4 : Word) :
    val256 u_norm0 u_norm1 u_norm2 u3 + u4.toNat * 2^256 =
    (u4.toNat * 2^64 + u3.toNat) * 2^192 +
      (u_norm0.toNat + u_norm1.toNat * 2^64 + u_norm2.toNat * 2^128) := by
  unfold val256; ring

/-- The lower-3-limb val256 is bounded by 2^192 (since each limb < 2^64). -/
theorem val256_lower3_lt_pow192 (x0 x1 x2 : Word) :
    x0.toNat + x1.toNat * 2^64 + x2.toNat * 2^128 < 2^192 := by
  have h0 := x0.isLt
  have h1 := x1.isLt
  have h2 := x2.isLt
  calc x0.toNat + x1.toNat * 2^64 + x2.toNat * 2^128
      ≤ (2^64 - 1) + (2^64 - 1) * 2^64 + (2^64 - 1) * 2^128 := by
        have h1' : x1.toNat * 2^64 ≤ (2^64 - 1) * 2^64 :=
          Nat.mul_le_mul_right _ (by omega)
        have h2' : x2.toNat * 2^128 ≤ (2^64 - 1) * 2^128 :=
          Nat.mul_le_mul_right _ (by omega)
        omega
    _ < 2^192 := by decide

/-- **B3.4** (the §B target-minus-one): val256 ratio bound via normalization.
    `val256(a) / val256(b) ≤ (u4*2^64 + u3) / b3'`.

    Proof: cancel 2^shift in LHS, apply normalization identities
    `u_val256_eq_scaled_with_overflow` + `b3_prime_val256_eq_scaled`,
    then use `Nat.div_le_div_left` + `a_scaled_decomp` + `nat_trunc_div_add_lt`. -/
theorem val256_ratio_le_u_total_div_b3_prime
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat := by
  simp only []
  -- Step 1: cancel 2^shift via Nat.mul_div_mul_right.
  have h_pow_pos : (0 : Nat) < 2^(clzResult b3).1.toNat := by positivity
  have h_cancel :
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 =
      (val256 a0 a1 a2 a3 * 2^(clzResult b3).1.toNat) /
      (val256 b0 b1 b2 b3 * 2^(clzResult b3).1.toNat) :=
    (Nat.mul_div_mul_right _ _ h_pow_pos).symm
  rw [h_cancel]
  -- Step 2: rewrite numerator via `u_val256_eq_scaled_with_overflow`.
  have h_norm_u := u_val256_eq_scaled_with_overflow a0 a1 a2 a3 b3 hshift_nz
  -- Step 3: rewrite denominator via `b3_prime_val256_eq_scaled`.
  have h_norm_v := b3_prime_val256_eq_scaled b0 b1 b2 b3 hshift_nz
  rw [← h_norm_u, ← h_norm_v]
  -- Goal: (val256(a_norm) + u4*2^256) / val256(b_norm) ≤ (u4*2^64+u3)/b3'.
  set b3_prime := (b3 <<< ((clzResult b3).1.toNat % 64)) |||
    (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))
    with hb3_prime_def
  set u4 := a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)
    with hu4_def
  set u3 := (a3 <<< ((clzResult b3).1.toNat % 64)) |||
    (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))
    with hu3_def
  -- Step 4: val256(b_norm) ≥ b3' * 2^192.
  have h_b_ge : (val256
    (b0 <<< ((clzResult b3).1.toNat % 64))
    ((b1 <<< ((clzResult b3).1.toNat % 64)) |||
       (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    ((b2 <<< ((clzResult b3).1.toNat % 64)) |||
       (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    b3_prime) ≥ b3_prime.toNat * 2^192 := val256_ge_top_limb_mul_pow192 _ _ _ _
  -- Step 5: b3' > 0 (to apply div_le_div_left).
  have hb3_prime_ge_pow63 : b3_prime.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz _
  have hb3_prime_pos : 0 < b3_prime.toNat := by omega
  have hb3_prime_pow_pos : 0 < b3_prime.toNat * 2^192 := by
    have : (0 : Nat) < 2^192 := by positivity
    exact Nat.mul_pos hb3_prime_pos this
  -- Step 6: Nat.div_le_div_left with the ≥ relationship.
  have h_step1 :
      (val256
         (a0 <<< ((clzResult b3).1.toNat % 64))
         ((a1 <<< ((clzResult b3).1.toNat % 64)) |||
            (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
         ((a2 <<< ((clzResult b3).1.toNat % 64)) |||
            (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
         u3 + u4.toNat * 2^256) /
        (val256
          (b0 <<< ((clzResult b3).1.toNat % 64))
          ((b1 <<< ((clzResult b3).1.toNat % 64)) |||
             (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
          ((b2 <<< ((clzResult b3).1.toNat % 64)) |||
             (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
          b3_prime) ≤
      (val256
         (a0 <<< ((clzResult b3).1.toNat % 64))
         ((a1 <<< ((clzResult b3).1.toNat % 64)) |||
            (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
         ((a2 <<< ((clzResult b3).1.toNat % 64)) |||
            (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
         u3 + u4.toNat * 2^256) / (b3_prime.toNat * 2^192) :=
    Nat.div_le_div_left h_b_ge hb3_prime_pow_pos
  refine Nat.le_trans h_step1 ?_
  -- Step 7: use a_scaled_decomp + nat_trunc_div_add_lt.
  rw [a_scaled_decomp]
  -- Goal: ((u4*2^64+u3)*2^192 + lower) / (b3'*2^192) ≤ (u4*2^64+u3)/b3'.
  have h_lower_lt : (a0 <<< ((clzResult b3).1.toNat % 64)).toNat +
      ((a1 <<< ((clzResult b3).1.toNat % 64)) |||
         (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))).toNat *
        2^64 +
      ((a2 <<< ((clzResult b3).1.toNat % 64)) |||
         (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))).toNat *
        2^128 < 2^192 := val256_lower3_lt_pow192 _ _ _
  have h_pow192_pos : (0 : Nat) < 2^192 := by positivity
  rw [nat_trunc_div_add_lt _ _ _ _ h_pow192_pos hb3_prime_pos h_lower_lt]

/-- **B4** (the §B target, wrapper form). -/
theorem q_true_triple_bridge_to_val256_norm
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat :=
  val256_ratio_le_u_total_div_b3_prime a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz hb3nz

-- =============================================================================
-- Main theorem: composition
-- =============================================================================

/-- **Call-skip exact lower bound** (the target of PR #1154 replacement). -/
theorem div128Quot_call_skip_ge_val256_div_v2
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (_hskip : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3
  have h_bridge := q_true_triple_bridge_to_val256_norm a0 a1 a2 a3 b0 b1 b2 b3
    hshift_nz hb3nz
  simp only [] at h_bridge
  have h_b3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz _
  have h_u4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_core := div128Quot_ge_q_true_normalized u4 u3 b3' h_b3'_ge h_u4_lt_b3'
  exact Nat.le_trans h_bridge h_core

end EvmAsm.Evm64
