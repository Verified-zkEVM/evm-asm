/-
  EvmAsm.Evm64.EvmWordArith.Div128NoWrapDischarge

  Discharge bridge: prove `Div128AllPhasesNoWrapInv` (or its weaker
  `Div128PhaseNoWrapInv` cousin) from algorithmic runtime conditions
  (`isSkipBorrowN4Call`, `isAddbackBorrowN4Call`, etc.).

  This is approach (a) from the n4CallAddbackBeq closure plan: prove
  the no-wrap invariant via Phase-1-level reasoning, which then makes
  KB-6d unconditional and unblocks the addback-BEQ semantic predicate.

  **Background**: a numerical counterexample
  (`memory/project_n4calladdbackbeq_counterexample.md`) shows that
  approach (b) — direct val256-level Knuth-B without Phase-1 reasoning —
  is impossible. The bound `qHat ≤ q_true + 2` is genuinely false for
  some inputs satisfying just `hcall + hshift_nz + hb3nz`. Phase-1
  reasoning is the only viable path.

  **Decomposition** (planned, ~300-500 LOC total):

  - **D1**: Phase 1 tight equality `q1' = q_top_phase1` from
    skip-borrow + Knuth-B/C check correctness. Sub-decomposed into:
    - **D1a**: Phase 1b check post-condition `q1' ≤ q_top_phase1 + 1`.
    - **D1b**: Combined with `algorithmQ1Prime_ge_q_true_1`
      (q1' ≥ q_top_phase1) gives `q1' ∈ {q_top_phase1, q_top_phase1+1}`.
    - **D1c**: Skip-borrow excludes the `q_top_phase1+1` case
      (overshoot-by-1 would cause mulsub to borrow at val256 level).

  - **D2**: From q1' = q_top_phase1, derive:
    - **D2a**: `un21.toNat = (rhat'%2^32)*2^32 + div_un1 - q1'*dLo`
      (no-wrap form; combines Phase 1b post + KB-3j case-split).
    - **D2b**: From Phase 1 Euclidean `q1'*dHi + rhat' = uHi`,
      derive `un21 < vTop` (the first conjunct).

  - **D3**: From un21 < vTop, derive Phase 1 no-wrap conjunct
    `q1' * dLo ≤ (rhat'%2^32)*2^32 + div_un1` (the second conjunct).
    Direct from D2a + non-negativity of un21.

  - **D4**: Phase 2 mirror — under un21 < vTop (D2b), Phase 2 satisfies
    its own no-wrap invariant `q0' * dLo ≤ rhat2'*2^32 + div_un0`
    (the third conjunct).

  - **D5**: Compose D2b + D3 + D4 into `Div128AllPhasesNoWrapInv`
    (or `Div128PhaseNoWrapInv` if Phase 2 conjunct is dropped).

  Each sub-stub will be proven incrementally; this file accumulates
  them with `sorry` placeholders, then the parent bridge composes.

  This file is intentionally separate from `Div128CallSkipClose.lean`
  to keep that file (and PR #1353) sorry-free. The bridge work-in-
  progress lives here on a follow-up branch.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2
import EvmAsm.Evm64.EvmWordArith.Div128CallSkipClose

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (bv6_toNat_32)
open EvmWord (val256)

-- ============================================================================
-- D1c: Phase 1 tight under skip-borrow (the key structural lemma)
-- ============================================================================

/-- **D1c (STUB)**: Under `isSkipBorrowN4Call`, Phase 1 trial is tight:
    `q1' = q_top_phase1` exactly (no Knuth-C overshoot remains).

    **Proof sketch**: The skip-borrow condition (`c3 ≤ u4` from
    `c3_le_u4_of_skip_borrow_call`) implies the outer mulsub
    `qHat * val256(b) ≤ val256(a)`, hence `qHat ≤ q_true`. Combined
    with the closed lower bound `qHat ≥ q_true` (Knuth-A normalized),
    we get `qHat = q_true` (already in `div128Quot_call_skip_eq_val256_div`).

    From `qHat = q_true < 2^64` and `q1' < 2^32` (KB-3e'''), the OR
    decomposition `qHat = (q1' << 32) | q0'` admits a unique digit
    decomposition. Combined with the Phase 1 lower bound
    `q1' ≥ q_top_phase1` (KB-LB7), we can pin `q1' = q_top_phase1` AND
    `q0' < 2^32`. The latter is exactly KB-6b's precondition.

    Estimated: ~80-100 LOC. Needs careful BitVec OR decomposition. -/
theorem div128Quot_q1_prime_eq_q_top_phase1_of_skip_borrow
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (_hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0)
    (_hcall : isCallTrialN4 a3 b2 b3)
    (_hborrow : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    q1'.toNat =
      (u4.toNat * 2^32 + div_un1.toNat) /
        (b3' >>> (32 : BitVec 6).toNat).toNat := by
  sorry

-- ============================================================================
-- D2a + D3: Phase 1 no-wrap from tight Phase 1
-- ============================================================================

/-- **D2/D3 (STUB)**: From `q1' = q_top_phase1`, derive Phase 1 no-wrap
    `q1' * dLo ≤ (rhat'%2^32)*2^32 + div_un1`.

    **Proof sketch**: From q1' = q_top_phase1 = (u4*2^32 + div_un1)/b3',
    we have q1' * b3' ≤ u4*2^32 + div_un1. Expanding b3' = dHi*2^32 + dLo:
    q1' * dHi * 2^32 + q1' * dLo ≤ u4 * 2^32 + div_un1. From Phase 1b
    Euclidean q1' * dHi + rhat' = uHi (the un-shifted version), we have
    q1' * dHi * 2^32 = (uHi - rhat') * 2^32. Substituting and rearranging:
    q1' * dLo ≤ rhat' * 2^32 + div_un1 - some_correction. Under
    rhat' < 2^32 (Phase 1b post-condition under skip-borrow), this
    simplifies to the desired no-wrap inequality.

    Estimated: ~50 LOC of Nat arithmetic. -/
theorem div128Quot_phase1_no_wrap_of_q1_prime_eq_q_top_phase1
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (_hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0)
    (_hcall : isCallTrialN4 a3 b2 b3)
    (_h_q1_eq :  -- this hypothesis comes from D1c
      let shift := (clzResult b3).1.toNat % 64
      let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
      let u4 := a3 >>> antiShift
      let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
      let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
      let dHi := b3' >>> (32 : BitVec 6).toNat
      let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := un3 >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu u4 dHi
      let rhat := u4 - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      let qDlo := q1c * dLo
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
      let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
      q1'.toNat = (u4.toNat * 2^32 + div_un1.toNat) / dHi.toNat) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat := by
  sorry

-- ============================================================================
-- D2b: un21 < vTop from tight Phase 1
-- ============================================================================

/-- **D2b (STUB)**: Under `q1' = q_top_phase1` AND Phase 1 no-wrap,
    derive `un21 < vTop`.

    **Proof sketch**: From the no-wrap form (D3), the BitVec subtraction
    `un21 = cu_rhat_un1 - cu_q1_dlo` doesn't wrap. Hence
    `un21.toNat = (rhat'%2^32)*2^32 + div_un1 - q1'*dLo`. Combined with
    KB-3m's additive identity (which holds under no-wrap), we get
    `un21 + r1*2^64 + q1'*vTop = uHi*2^32 + div_un1` where
    `r1 := rhat'/2^32`. Rearranging:
    `un21 = uHi*2^32 + div_un1 - q1'*vTop - r1*2^64`.
    Under `q1' = q_top_phase1 = (uHi*2^32 + div_un1)/vTop`:
    `q1'*vTop ≤ uHi*2^32 + div_un1 < (q1'+1)*vTop`, so
    `0 ≤ uHi*2^32 + div_un1 - q1'*vTop < vTop`.
    Combined with `r1 ≥ 0`: `un21 ≤ uHi*2^32 + div_un1 - q1'*vTop < vTop`.

    Estimated: ~40 LOC. -/
theorem div128Quot_un21_lt_vTop_from_phase1_tight
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (_hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0)
    (_hcall : isCallTrialN4 a3 b2 b3)
    (_h_q1_eq :  -- q1' = q_top_phase1 (from D1c)
      let shift := (clzResult b3).1.toNat % 64
      let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
      let u4 := a3 >>> antiShift
      let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
      let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
      let dHi := b3' >>> (32 : BitVec 6).toNat
      let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := un3 >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu u4 dHi
      let rhat := u4 - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      let qDlo := q1c * dLo
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
      let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
      q1'.toNat = (u4.toNat * 2^32 + div_un1.toNat) / dHi.toNat)
    (_h_no_wrap_phase1 :  -- Phase 1 no-wrap (from D3)
      let shift := (clzResult b3).1.toNat % 64
      let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
      let u4 := a3 >>> antiShift
      let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
      let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
      let dHi := b3' >>> (32 : BitVec 6).toNat
      let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := un3 >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu u4 dHi
      let rhat := u4 - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      let qDlo := q1c * dLo
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
      let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
      let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
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
    let un21 := cu_rhat_un1 - cu_q1_dlo
    un21.toNat < dHi.toNat * 2^32 + dLo.toNat := by
  sorry

-- ============================================================================
-- D5: Compose into Div128PhaseNoWrapInv
-- ============================================================================

/-- **D5 (STUB)**: Skip-borrow implies `Div128PhaseNoWrapInv`.

    Composes D1c (Phase 1 tight) → D2a/D3 (Phase 1 no-wrap) → D2b
    (un21 < vTop). This is the core bridge for the call+skip path.

    For the call+addback path, similar reasoning via
    `isAddbackBorrowN4Call` instead of skip-borrow — the analogous
    Phase 1 tight lemma needs to be developed (D1c-addback variant).

    Note: this version targets `Div128PhaseNoWrapInv` (2 conjuncts:
    un21<vTop + Phase 1 no-wrap), NOT `Div128AllPhasesNoWrapInv`. The
    Phase 2 no-wrap conjunct (D4) is left as a separate piece since
    the strict KB-6c/KB-6d closure only needs Phase 1 no-wrap. -/
theorem div128_phase_no_wrap_of_skip_borrow
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (_hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0)
    (_hcall : isCallTrialN4 a3 b2 b3)
    (_hborrow : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    Div128PhaseNoWrapInv u4 un3 b3' := by
  sorry

end EvmAsm.Evm64
