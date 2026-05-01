-- file-size-exception: tracked by #66 / #61 (call-addback BEQ Word-level wrappers + closure are still being filled in; further sub-split deferred until the chain stabilizes).
/-
  EvmAsm.Evm64.DivMod.Spec.CallAddback

  Call+addback BEQ semantic predicates and stack specs (n=4, shift ≠ 0).
  Split from the call-skip stack-spec surface to isolate the addback branch.

  Contents:
  - `n4CallAddbackBeqSemanticHolds` predicate.
  - n=4 call+addback BEQ DIV/MOD stack specs.
  - Sub-stub: qHat = a/b + 1 (single-addback) and qHat ≥ 2 (double-addback).
  - Pure-Nat algebra (post1_val_eq_amod_pow_s_pure_nat,
    abPrime_val_eq_amod_pow_s_pure_nat, qHat_ge_two_abstract).
  - Irreducible bundles for the algorithm's intermediate Word/Nat values
    (algCallAddbackBeqCarry, algCallAddbackBeqMsC3, algCallAddbackBeqU4,
    algCallAddbackBeqMsLowVal, algCallAddbackBeqPost1Val,
    algCallAddbackBeqPost1Limb{0..3}, algCallAddbackBeqUn{0..3}Out,
    algCallAddbackBeqAbPrimeLimb{0..3}, algCallAddbackBeqAbPrimeVal).
  - Word-level wrappers (post1_val_eq_amod_pow_s_of_single_addback,
    abPrime_val_eq_amod_pow_s_of_double_addback).
  - Adapter / parent + final stack specs.

  The trailing leaf cluster (qHat = a/b + k sub-stubs and the
  algCallAddbackBeq_* Word-level Euclideans / val256 bounds) lives in
  `Spec/CallAddbackSubStubs.lean` (#1078 sub-slice).
-/

import EvmAsm.Evm64.DivMod.Spec.CallSkip
import EvmAsm.Evm64.DivMod.Spec.CallAddbackPureNat
import EvmAsm.Evm64.DivMod.Spec.CallAddbackPhase1Stubs
import EvmAsm.Evm64.DivMod.Spec.CallAddbackV2Bounds
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.AlgDefs
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.AlgEuclideans
import EvmAsm.Evm64.DivMod.Shift0Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Call+addback BEQ semantic predicates and stack specs (n=4, shift ≠ 0)
-- ============================================================================

/-- Semantic-correctness precondition for the n=4 call+addback-BEQ sub-path:
    the final `q_out` (= `qHat - 1` single-addback or `qHat - 2` double-addback)
    equals `⌊val256(a)/val256(b)⌋`.

    Unlike `n4CallSkipSemanticHolds` which states a lower-bound on the raw
    `div128Quot`, this predicate directly states that the post-addback
    corrected quotient is the true quotient. Proving it from first
    principles requires the Knuth TAOCP Theorem B overestimate bound
    (`q̂ ≤ q_true + 2`) plus the algorithm's addback-correction semantics,
    which combine to ensure q_out is exactly correct. Deferred to a future
    task; the stack spec delegates the proof to callers.

    **🚨 STATUS (2026-04-27, updated): real correctness bug in algorithm**.

    Verified via `lean_run_code`: with
    `a3 = 2^63 + 2^33, a2 = a1 = a0 = 0, b3 = 1, b2 = 2^33 - 1,
    b1 = b0 = 0`, the input satisfies ALL runtime preconditions for
    the call-addback-BEQ branch (hbnz, hb3nz, hshift_nz, hbltu,
    hborrow, hcarry2_nz), but the algorithm computes
    `q_out = qHat - 1 = 2^63 + 2^33 - 4 = 9223372045444710396` while
    `q_true = val256(a) / val256(b) = 2^63 + 2^32 - 2 = 9223372041149743102`.
    The discrepancy is `2^32 - 2` ≈ 4.3 × 10⁹.

    **Root cause**: our `div128Quot` does only 1 Phase 1b correction
    (vs Knuth classical 2-correction loop), so qHat can overshoot at
    val256 level by up to ~2^33. The actual RISC-V program at
    `Program.lean:386` has an addback LOOP (`BEQ x7 x0` jumps back if
    x7 = 0), but the loop-exit heuristic "limb-3 carry of addback ≠ 0"
    fires after 1 addback in this case — leaving q_out = qHat - 1,
    still ~2^32 too large.

    **Implication**: the algorithm is genuinely buggy on this input
    class. The `n4CallAddbackBeqSemanticHolds` predicate is provably
    FALSE on runtime-reachable inputs. Closure
    (`n4CallAddbackBeqSemanticHolds_of_*`) cannot be proven; the
    user-facing `evm_div_n4_full_call_addback_beq_stack_pre_spec` and
    its relatives are vacuous on this input class.

    See `memory/project_n4callbeq_addback_overshoot_2pow32.md` and
    `memory/project_knuth_d_one_correction_design.md` for the full
    analysis.

    **Remediation options**:
    1. Modify `div128Quot` to do 2 Phase 1b corrections (matching Knuth
       classical D3 loop). Restores Knuth Theorem B's per-digit ≤ 2
       overshoot bound. Requires changing both Lean abstraction and
       RISC-V code.
    2. Modify the addback loop's exit condition to detect 2^32-scale
       overshoots (e.g., bound iteration count by some explicit limit
       and re-check). Non-trivial.
    3. Document the input class as out-of-scope and gate it externally.
       Pragmatically blocks complete EVM-level verification.

    Mirror of `n4CallSkipSemanticHolds` for the call+addback branch. -/
def n4CallAddbackBeqSemanticHolds (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let q_out : Word :=
    if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
    else qHat + signExtend12 4095
  q_out.toNat =
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

-- The v1 counterexample, v2 fix-verification, v2-buggy-confirmation and
-- the v2 mirror predicate `n4CallAddbackBeqSemanticHolds_v2` (plus its
-- sanity check on the v1 counterexample input) live in
-- `EvmAsm/Evm64/DivMod/Spec/CallAddbackCounterexamples.lean` (extracted
-- 2026 toward the #1078 file-size cap; see beads evm-asm-b5i).

-- NOTE: `div128Quot_v2_qHat_vTop_le` (the simple form, without no_wrap
-- implications) was previously a sorry stub here. It was provably FALSE
-- in general (the no_wrap conditions don't hold automatically, per
-- `div128Quot_v2_phase1_no_wrap_lo_FALSE_counterexample`), so the simple
-- form was unprovable.
--
-- Use `div128Quot_v2_qHat_vTop_le_full` (defined below, after the 7
-- proven sub-lemmas) instead — it takes the 3 v1-style no_wrap
-- implications as preconditions and is FULLY PROVEN by direct
-- composition.




/-- **Phase-1 division invariant — overshoot=0 case** (q1c = q_true exactly).

    When q1c lands at the true quotient, no corrections should fire and
    `q1'' = q1' = q1c = q_true`. The first BLTU check should be FALSE
    (since `q1c * vTop ≤ x`); the Phase-2b guard/check should also leave
    q1' alone.

    **No truncation under runtime preconditions** (numerically validated
    2026-04-28): `_hshift_nz` forces `shift ∈ [1, 63]`, hence
    `antiShift = 64 - shift ∈ [1, 63]`. So `u4 = a3 >>> antiShift` is
    bounded by `2^shift ≤ 2^63`, i.e., `u4 < 2^63`. Combined with
    `dHi ≥ 2^31` (from `b3' ≥ 2^63`), we get
    `q1 = u4 / dHi < 2^63 / 2^31 = 2^32`. Hence `hi1 = q1 >>> 32 = 0`
    ALWAYS, so `q1c = q1` and `rhatc = rhat = u4 mod dHi < dHi < 2^32`.

    Sub-case 0b (hi1 ≠ 0) NEVER OCCURS under runtime preconditions, so
    no truncation issue exists for the 1st BLTU. The algorithm's
    `(uHi, uLo, vTop)`-level bug at `uHi ≥ 2^63` (validated numerically:
    on input `(2^64-2^32+1, 0, 2^64-1)` the algorithm undershoots by
    `2^32-1`) is unreachable from valid `(a, b)` inputs.

    Closure plan: invoke `_phase1b_check_iff_overshoot_under_runtime` in
    reverse direction (q1c not overshooting → 1st BLTU false). Stub 2's
    preconditions `rhatc < 2^32 ∧ q1c < 2^32` are AUTOMATIC under
    runtime preconditions (q1c = q1 < 2^32, rhatc < dHi < 2^32). -/
private theorem div128Quot_v2_phase1_div_invariant_overshoot_0_sub
    (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hbltu : isCallTrialN4Evm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (_hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b)
    (_h_overshoot :
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
      q1c.toNat = (u4.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat)) :
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
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (u4.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1
        q1' rhat' q1''
  set q_true := (u4.toNat * 2^32 + div_un1.toNat) /
                (dHi.toNat * 2^32 + dLo.toNat) with h_q_true_def
  -- Bridge facts.
  have h_rhatc_lt : rhatc.toNat < 2^32 :=
    div128Quot_v2_case_0_rhatc_lt_pow32_under_runtime a b _hb3nz _hshift_nz
      _hbltu _hcarry2_nz _hborrow_v2
  have h_q_true_lt : q_true < 2^32 :=
    div128Quot_v2_q_true_lt_pow32_under_runtime a b _hb3nz _hshift_nz _hbltu
  have h_q1c_eq : q1c.toNat = q_true := _h_overshoot
  have h_q1c_lt : q1c.toNat < 2^32 := by rw [h_q1c_eq]; exact h_q_true_lt
  -- Standard arithmetic facts.
  have h_b3'_ge_pow63 : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) _hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 b3' h_b3'_ge_pow63
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have h_b3'_decomp : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_b3prime : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      (isCallTrialN4Evm_def ▸ _hbltu)
  have h_u4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_b3'_decomp]; exact h_u4_lt_b3prime
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h1 : dHi.toNat * 2^32 ≥ 2^31 * 2^32 := Nat.mul_le_mul_right _ hdHi_ge
    have h2 : (2^31 * 2^32 : Nat) = 2^63 := by decide
    omega
  -- Stub 2 (in reverse): no overshoot → 1st BLTU FALSE.
  have h_stub2 := div128Quot_v2_phase1b_check_iff_overshoot_under_runtime a b
    _hb3nz _hshift_nz _hbltu _hcarry2_nz _hborrow_v2
  simp only [] at h_stub2
  have h_iff := h_stub2 h_rhatc_lt h_q1c_lt
  -- In case 0: q1c * vTop = q_true * vTop ≤ x. So no overshoot.
  have h_q_true_vTop_le_x :
      q_true * (dHi.toNat * 2^32 + dLo.toNat) ≤ u4.toNat * 2^32 + div_un1.toNat := by
    have := Nat.div_mul_le_self (u4.toNat * 2^32 + div_un1.toNat)
                                (dHi.toNat * 2^32 + dLo.toNat)
    rw [← h_q_true_def] at this
    linarith
  have h_no_overshoot :
      ¬ (q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) > u4.toNat * 2^32 + div_un1.toNat) := by
    rw [h_q1c_eq]
    omega
  have h_BLTU_false : ¬ BitVec.ult rhatUn1 qDlo := h_iff.not.mpr h_no_overshoot
  -- q1' = q1c (since BLTU FALSE).
  have h_q1'_eq : q1' = q1c := by
    show (if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c) = q1c
    rw [if_neg h_BLTU_false]
  -- rhat' = rhatc (since BLTU FALSE).
  have h_rhat'_eq : rhat' = rhatc := by
    show (if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) = rhatc
    rw [if_neg h_BLTU_false]
  -- Phase-2b: q1'' = div128Quot_phase2b_q0' q1' rhat' dLo div_un1.
  -- Guard: rhat'.toNat = rhatc.toNat < 2^32, so rhat' >> 32 = 0.
  have h_rhat'_shr_zero : rhat' >>> (32 : BitVec 6).toNat = 0 := by
    rw [h_rhat'_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt h_rhatc_lt]; rfl
  -- Phase-2b's BLTU check semantics: similar to Stub 2 but with q1'/rhat'
  -- in place of q1c/rhatc. With q1' = q_true and rhat' = rhatc, the
  -- untruncated check is q_true * vTop > x — FALSE.
  have h_q1'_eq_q_true : q1'.toNat = q_true := by rw [h_q1'_eq]; exact h_q1c_eq
  -- Compute Phase-2b output.
  show (div128Quot_phase2b_q0' q1' rhat' dLo div_un1).toNat = q_true
  unfold div128Quot_phase2b_q0'
  rw [if_pos h_rhat'_shr_zero]
  -- Now check the inner BLTU: rhat' << 32 ||| div_un1 < q1' * dLo?
  -- With rhat' = rhatc < 2^32 and q1' = q_true < 2^32, no truncation.
  have h_q1'_dLo_lt_pow64 : q1'.toNat * dLo.toNat < 2^64 := by
    rw [h_q1'_eq_q_true]
    have h := Nat.mul_lt_mul_of_lt_of_lt h_q_true_lt hdLo_lt
    have h_pow : (2^32 * 2^32 : Nat) = 2^64 := by decide
    omega
  have h_q1'_dLo_word : (q1' * dLo).toNat = q1'.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt h_q1'_dLo_lt_pow64
  have h_rhat'_lt : rhat'.toNat < 2^32 := by rw [h_rhat'_eq]; exact h_rhatc_lt
  have h_rhatUn0 : ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1).toNat
      = rhat'.toNat * 2^32 + div_un1.toNat := by
    rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    exact EvmWord.halfword_combine rhat' div_un1 h_rhat'_lt h_div_un1_lt
  -- Phase-1a Euclidean: q1c * dHi + rhatc = u4. With q1c = q_true:
  have h_post1a : q1c.toNat * dHi.toNat + rhatc.toNat = u4.toNat :=
    div128Quot_first_round_post u4 dHi hdHi_ne hdHi_lt
  -- Untruncated comparison: rhatc * 2^32 + div_un1 ≥ q_true * dLo (since
  -- q_true * vTop ≤ x).
  have h_untruncated_ge :
      rhatc.toNat * 2^32 + div_un1.toNat ≥ q_true * dLo.toNat := by
    -- rhatc = u4 - q_true * dHi (from h_post1a + h_q1c_eq).
    have h_rhatc_eq : rhatc.toNat = u4.toNat - q_true * dHi.toNat := by
      have := h_post1a
      rw [h_q1c_eq] at this
      omega
    rw [h_rhatc_eq, Nat.sub_mul]
    -- Goal: (u4 - q_true * dHi) * 2^32 + div_un1 ≥ q_true * dLo.
    -- u4 * 2^32 + div_un1 ≥ q_true * vTop = q_true * (dHi * 2^32 + dLo)
    --                    = q_true * dHi * 2^32 + q_true * dLo.
    -- So u4 * 2^32 - q_true * dHi * 2^32 + div_un1 ≥ q_true * dLo.
    have h_q_true_dHi_le : q_true * dHi.toNat * 2^32 ≤ u4.toNat * 2^32 := by
      have h_q_dHi_le : q_true * dHi.toNat ≤ u4.toNat := by
        rw [← h_q1c_eq]; omega
      exact Nat.mul_le_mul_right _ h_q_dHi_le
    have h_x_ge_qvTop_arith :
        u4.toNat * 2^32 - q_true * dHi.toNat * 2^32 + div_un1.toNat
          ≥ q_true * dLo.toNat := by
      have h_eucl : q_true * (dHi.toNat * 2^32 + dLo.toNat) =
                    q_true * dHi.toNat * 2^32 + q_true * dLo.toNat := by ring
      have h_x_ge : q_true * dHi.toNat * 2^32 + q_true * dLo.toNat
                    ≤ u4.toNat * 2^32 + div_un1.toNat := by
        rw [← h_eucl]; exact h_q_true_vTop_le_x
      omega
    exact h_x_ge_qvTop_arith
  -- BLTU check is FALSE: rhatUn0 ≥ qDlo'.
  have h_inner_BLTU_false :
      ¬ BitVec.ult ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1) (q1' * dLo) := by
    rw [EvmWord.ult_iff, h_rhatUn0, h_q1'_dLo_word, h_q1'_eq_q_true, h_rhat'_eq]
    push Not
    omega
  rw [if_neg h_inner_BLTU_false]
  -- Returns q1', whose toNat = q_true.
  exact h_q1'_eq_q_true

/-- **Phase-1 division invariant — overshoot=1 case** (q1c = q_true + 1).

    1st BLTU check fires (Stub 2 forward) → q1' = q1c - 1 = q_true,
    rhat' = rhatc + dHi. Phase-2b: q1' = q_true is correct, so 2nd
    check should not fire → q1'' = q1' = q_true. -/
private theorem div128Quot_v2_phase1_div_invariant_overshoot_1_sub
    (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hbltu : isCallTrialN4Evm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (_hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b)
    (_h_overshoot :
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
      q1c.toNat = (u4.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 1) :
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
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (u4.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1
        q1' rhat' q1''
  set q_true := (u4.toNat * 2^32 + div_un1.toNat) /
                (dHi.toNat * 2^32 + dLo.toNat) with h_q_true_def
  -- Bridge facts. The `_case_0_rhatc_lt_pow32` bridge depends only on
  -- runtime preconditions (which force `hi1 = 0`), not on the overshoot
  -- value, so it applies to case 1 too.
  have h_rhatc_lt : rhatc.toNat < 2^32 :=
    div128Quot_v2_case_0_rhatc_lt_pow32_under_runtime a b _hb3nz _hshift_nz
      _hbltu _hcarry2_nz _hborrow_v2
  have h_q_true_lt : q_true < 2^32 :=
    div128Quot_v2_q_true_lt_pow32_under_runtime a b _hb3nz _hshift_nz _hbltu
  have h_q1c_eq : q1c.toNat = q_true + 1 := _h_overshoot
  -- Algorithm-level bound: q1 < 2^32 (under runtime preconditions),
  -- so hi1 = 0 always, so q1c = q1 < 2^32. Hence q_true + 1 < 2^32.
  have h_q1c_lt : q1c.toNat < 2^32 := by
    -- This follows from the bridge's intermediate step (hi1 = 0 → q1c = q1 < 2^32).
    -- Re-derive q1 < 2^32 here via the same chain as the bridge.
    have hshift_le_63 := clzResult_fst_toNat_le (b.getLimbN 3)
    have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
      by_contra h
      push Not at h
      apply _hshift_nz
      apply BitVec.eq_of_toNat_eq
      rw [EvmAsm.Rv64.AddrNorm.word_toNat_0]; omega
    have h_u4_lt : u4.toNat < 2^63 :=
      u_top_lt_pow63_of_shift_nz (a.getLimbN 3) (clzResult (b.getLimbN 3)).1
        hshift_pos hshift_le_63
    have h_b3'_ge_pow63 : b3'.toNat ≥ 2^63 :=
      b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) _hb3nz _
    have hdHi_ge : dHi.toNat ≥ 2^31 :=
      div128Quot_dHi_ge_pow31 b3' h_b3'_ge_pow63
    have hdHi_ne : dHi ≠ 0 := by
      intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
    have h_q1_lt : q1.toNat < 2^32 := by
      show (rv64_divu u4 dHi).toNat < 2^32
      rw [rv64_divu_toNat u4 dHi hdHi_ne]
      have h1 : u4.toNat / dHi.toNat ≤ u4.toNat / 2^31 :=
        Nat.div_le_div_left hdHi_ge (by decide)
      have h2 : u4.toNat / 2^31 < 2^32 :=
        Nat.div_lt_of_lt_mul (by
          have h_pow : (2^32 * 2^31 : Nat) = 2^63 := by decide
          omega)
      omega
    have h_hi1_zero : hi1 = 0 := by
      show q1 >>> (32 : BitVec 6).toNat = 0
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
          Nat.shiftRight_eq_div_pow]
      rw [Nat.div_eq_of_lt h_q1_lt]; rfl
    show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat < 2^32
    rw [if_pos h_hi1_zero]
    exact h_q1_lt
  -- Standard arithmetic facts.
  have h_b3'_ge_pow63 : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) _hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 b3' h_b3'_ge_pow63
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have h_b3'_decomp : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_b3prime : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      (isCallTrialN4Evm_def ▸ _hbltu)
  have h_u4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_b3'_decomp]; exact h_u4_lt_b3prime
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h1 : dHi.toNat * 2^32 ≥ 2^31 * 2^32 := Nat.mul_le_mul_right _ hdHi_ge
    have h2 : (2^31 * 2^32 : Nat) = 2^63 := by decide
    omega
  -- Stub 2 forward: overshoot ⟹ 1st BLTU TRUE.
  have h_stub2 := div128Quot_v2_phase1b_check_iff_overshoot_under_runtime a b
    _hb3nz _hshift_nz _hbltu _hcarry2_nz _hborrow_v2
  simp only [] at h_stub2
  have h_iff := h_stub2 h_rhatc_lt h_q1c_lt
  -- Case 1: q1c = q_true + 1, so overshoot (q1c * vTop > x).
  have h_overshoot :
      q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) > u4.toNat * 2^32 + div_un1.toNat := by
    rw [h_q1c_eq]
    have h_x_lt := x_lt_succ_div_mul (u4.toNat * 2^32 + div_un1.toNat)
      (dHi.toNat * 2^32 + dLo.toNat) h_vTop_pos
    rw [← h_q_true_def] at h_x_lt
    exact h_x_lt
  have h_BLTU_true : BitVec.ult rhatUn1 qDlo := h_iff.mpr h_overshoot
  -- q1' = q1c + signExtend12 4095 = q1c - 1 (mod 2^64) = q_true.
  have h_q1'_toNat : q1'.toNat = q_true := by
    show (if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c).toNat = q_true
    rw [if_pos h_BLTU_true]
    rw [BitVec.toNat_add, signExtend12_4095_toNat]
    -- (q1c.toNat + (2^64 - 1)) mod 2^64 = q1c.toNat - 1 (when q1c ≥ 1) = q_true.
    have h_q1c_ge_1 : 1 ≤ q1c.toNat := by rw [h_q1c_eq]; exact Nat.succ_pos _
    have h_q1c_isLt : q1c.toNat < 2^64 := q1c.isLt
    have h_q1c_minus_1_lt : q1c.toNat - 1 < 2^64 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_q1c_isLt
    have h_rearrange : q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 := by
      have h := Nat.sub_add_cancel h_q1c_ge_1
      have h_pow : (2^64 : Nat) ≥ 1 := by decide
      omega
    rw [h_rearrange, Nat.add_mod_right, Nat.mod_eq_of_lt h_q1c_minus_1_lt]
    rw [h_q1c_eq]
    exact Nat.add_sub_cancel q_true 1
  -- rhat' = rhatc + dHi.
  have h_rhat'_eq : rhat' = rhatc + dHi := by
    show (if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) = rhatc + dHi
    rw [if_pos h_BLTU_true]
  -- rhat'.toNat = rhatc.toNat + dHi.toNat (no overflow since rhatc < 2^32, dHi < 2^32).
  have h_rhatc_dHi_lt_pow64 : rhatc.toNat + dHi.toNat < 2^64 := by
    have : (2^32 + 2^32 : Nat) ≤ 2^64 := by decide
    omega
  have h_rhat'_toNat : rhat'.toNat = rhatc.toNat + dHi.toNat := by
    rw [h_rhat'_eq, BitVec.toNat_add]
    exact Nat.mod_eq_of_lt h_rhatc_dHi_lt_pow64
  -- Phase-1a: q1c * dHi + rhatc = u4. With q1c = q_true + 1.
  have h_post1a : q1c.toNat * dHi.toNat + rhatc.toNat = u4.toNat :=
    div128Quot_first_round_post u4 dHi hdHi_ne hdHi_lt
  -- rhatc + dHi = u4 - q_true * dHi (Nat). Hence rhat'.toNat = u4 - q_true * dHi.
  have h_rhat'_eq_nat : rhat'.toNat = u4.toNat - q_true * dHi.toNat := by
    rw [h_rhat'_toNat]
    have h_q1c_dHi : q1c.toNat * dHi.toNat = (q_true + 1) * dHi.toNat := by
      rw [h_q1c_eq]
    have h_qt_plus_1_dHi : (q_true + 1) * dHi.toNat = q_true * dHi.toNat + dHi.toNat := by ring
    have h_qt_dHi_le : q_true * dHi.toNat ≤ u4.toNat := by
      rw [h_q1c_dHi, h_qt_plus_1_dHi] at h_post1a; omega
    omega
  -- Phase-2b: compute q1''.
  show q1''.toNat = q_true
  show (div128Quot_phase2b_q0' q1' rhat' dLo div_un1).toNat = q_true
  unfold div128Quot_phase2b_q0'
  by_cases h_rhat'_shr : rhat' >>> (32 : BitVec 6).toNat = 0
  · -- Sub-case 1a: rhat' < 2^32. Guard passes. Inner BLTU: untruncated check
    -- is q_true * vTop > x, which is FALSE.
    rw [if_pos h_rhat'_shr]
    have h_rhat'_lt : rhat'.toNat < 2^32 := by
      have h_eq : rhat'.toNat / 2^32 = 0 := by
        have h : (rhat' >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat := by
          rw [h_rhat'_shr]
        rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
            Nat.shiftRight_eq_div_pow,
            EvmAsm.Rv64.AddrNorm.word_toNat_0] at h
        exact h
      have h_lt : rhat'.toNat < 2^32 :=
        (Nat.div_eq_zero_iff_lt (by decide : (0:Nat) < 2^32)).mp h_eq
      exact h_lt
    have h_q1'_dLo_lt_pow64 : q1'.toNat * dLo.toNat < 2^64 := by
      rw [h_q1'_toNat]
      have h := Nat.mul_lt_mul_of_lt_of_lt h_q_true_lt hdLo_lt
      have h_pow : (2^32 * 2^32 : Nat) = 2^64 := by decide
      omega
    have h_q1'_dLo_word : (q1' * dLo).toNat = q1'.toNat * dLo.toNat := by
      rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt h_q1'_dLo_lt_pow64
    have h_rhatUn0_eq : ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1).toNat
        = rhat'.toNat * 2^32 + div_un1.toNat := by
      rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
      exact EvmWord.halfword_combine rhat' div_un1 h_rhat'_lt h_div_un1_lt
    have h_q_true_vTop_le_x :
        q_true * (dHi.toNat * 2^32 + dLo.toNat) ≤ u4.toNat * 2^32 + div_un1.toNat := by
      have := Nat.div_mul_le_self (u4.toNat * 2^32 + div_un1.toNat)
                                  (dHi.toNat * 2^32 + dLo.toNat)
      rw [← h_q_true_def] at this
      linarith
    have h_qt_dHi_le : q_true * dHi.toNat ≤ u4.toNat :=
      qt_dHi_le_u4_case_1 q_true q1c.toNat dHi.toNat rhatc.toNat u4.toNat
        h_post1a h_q1c_eq
    have h_inner_BLTU_false :
        ¬ BitVec.ult ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1) (q1' * dLo) := by
      rw [EvmWord.ult_iff, h_rhatUn0_eq, h_q1'_dLo_word]
      push Not
      rw [h_rhat'_eq_nat, h_q1'_toNat]
      have h_eucl : q_true * (dHi.toNat * 2^32 + dLo.toNat) =
                    q_true * dHi.toNat * 2^32 + q_true * dLo.toNat := by ring
      have h_x_ge : q_true * dHi.toNat * 2^32 + q_true * dLo.toNat
                    ≤ u4.toNat * 2^32 + div_un1.toNat := by
        rw [← h_eucl]; exact h_q_true_vTop_le_x
      have h_sub : (u4.toNat - q_true * dHi.toNat) * 2^32 =
                   u4.toNat * 2^32 - q_true * dHi.toNat * 2^32 := by
        rw [Nat.sub_mul]
      rw [h_sub]
      omega
    rw [if_neg h_inner_BLTU_false]
    exact h_q1'_toNat
  · -- Sub-case 1b: rhat' ≥ 2^32. Guard FAILS. Phase-2b returns q1' = q_true.
    rw [if_neg h_rhat'_shr]
    exact h_q1'_toNat

/-- **Phase-1 division invariant — overshoot=2 case** (q1c = q_true + 2).

    1st check fires → q1' = q1c - 1 = q_true + 1.
    2nd guard fires (Stub 3) → 2nd check evaluates.
    Since q1' still overshoots by 1, 2nd check fires →
    q1'' = q1' - 1 = q_true. -/
private theorem div128Quot_v2_phase1_div_invariant_overshoot_2_sub
    (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hbltu : isCallTrialN4Evm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (_hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b)
    (_h_overshoot :
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
      q1c.toNat = (u4.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 2) :
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
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (u4.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1
        q1' rhat' q1''
  set q_true := (u4.toNat * 2^32 + div_un1.toNat) /
                (dHi.toNat * 2^32 + dLo.toNat) with h_q_true_def
  -- Bridge facts (rhatc < 2^32, q_true < 2^32, q1c < 2^32).
  have h_rhatc_lt : rhatc.toNat < 2^32 :=
    div128Quot_v2_case_0_rhatc_lt_pow32_under_runtime a b _hb3nz _hshift_nz
      _hbltu _hcarry2_nz _hborrow_v2
  have h_q_true_lt : q_true < 2^32 :=
    div128Quot_v2_q_true_lt_pow32_under_runtime a b _hb3nz _hshift_nz _hbltu
  have h_q1c_eq : q1c.toNat = q_true + 2 := _h_overshoot
  -- q1c < 2^32 from algorithm-level u4 < 2^63.
  have h_q1c_lt : q1c.toNat < 2^32 := by
    have hshift_le_63 := clzResult_fst_toNat_le (b.getLimbN 3)
    have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
      by_contra h
      push Not at h
      apply _hshift_nz
      apply BitVec.eq_of_toNat_eq
      rw [EvmAsm.Rv64.AddrNorm.word_toNat_0]; omega
    have h_u4_lt : u4.toNat < 2^63 :=
      u_top_lt_pow63_of_shift_nz (a.getLimbN 3) (clzResult (b.getLimbN 3)).1
        hshift_pos hshift_le_63
    have h_b3'_ge_pow63 : b3'.toNat ≥ 2^63 :=
      b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) _hb3nz _
    have hdHi_ge : dHi.toNat ≥ 2^31 :=
      div128Quot_dHi_ge_pow31 b3' h_b3'_ge_pow63
    have hdHi_ne : dHi ≠ 0 := by
      intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
    have h_q1_lt : q1.toNat < 2^32 := by
      show (rv64_divu u4 dHi).toNat < 2^32
      rw [rv64_divu_toNat u4 dHi hdHi_ne]
      have h1 : u4.toNat / dHi.toNat ≤ u4.toNat / 2^31 :=
        Nat.div_le_div_left hdHi_ge (by decide)
      have h2 : u4.toNat / 2^31 < 2^32 :=
        Nat.div_lt_of_lt_mul (by
          have h_pow : (2^32 * 2^31 : Nat) = 2^63 := by decide
          omega)
      omega
    have h_hi1_zero : hi1 = 0 := by
      show q1 >>> (32 : BitVec 6).toNat = 0
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
          Nat.shiftRight_eq_div_pow]
      rw [Nat.div_eq_of_lt h_q1_lt]; rfl
    show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat < 2^32
    rw [if_pos h_hi1_zero]
    exact h_q1_lt
  -- Standard arithmetic facts.
  have h_b3'_ge_pow63 : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) _hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 b3' h_b3'_ge_pow63
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have h_b3'_decomp : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_b3prime : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      (isCallTrialN4Evm_def ▸ _hbltu)
  have h_u4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_b3'_decomp]; exact h_u4_lt_b3prime
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h1 : dHi.toNat * 2^32 ≥ 2^31 * 2^32 := Nat.mul_le_mul_right _ hdHi_ge
    have h2 : (2^31 * 2^32 : Nat) = 2^63 := by decide
    omega
  -- Stub 2 forward: overshoot ⟹ 1st BLTU TRUE.
  have h_stub2 := div128Quot_v2_phase1b_check_iff_overshoot_under_runtime a b
    _hb3nz _hshift_nz _hbltu _hcarry2_nz _hborrow_v2
  simp only [] at h_stub2
  have h_iff := h_stub2 h_rhatc_lt h_q1c_lt
  -- Case 2: q1c = q_true + 2, so overshoot.
  have h_overshoot :
      q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) > u4.toNat * 2^32 + div_un1.toNat := by
    rw [h_q1c_eq]
    -- (q_true + 2) * vTop > x. From x < (q_true + 1) * vTop ≤ (q_true + 2) * vTop.
    have h_x_lt := x_lt_succ_div_mul (u4.toNat * 2^32 + div_un1.toNat)
      (dHi.toNat * 2^32 + dLo.toNat) h_vTop_pos
    rw [← h_q_true_def] at h_x_lt
    have h_succ_le : (q_true + 1) * (dHi.toNat * 2^32 + dLo.toNat) ≤
                     (q_true + 2) * (dHi.toNat * 2^32 + dLo.toNat) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h_BLTU_true : BitVec.ult rhatUn1 qDlo := h_iff.mpr h_overshoot
  -- q1' = q_true + 1.
  have h_q1'_toNat : q1'.toNat = q_true + 1 := by
    show (if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c).toNat = q_true + 1
    rw [if_pos h_BLTU_true]
    rw [BitVec.toNat_add, signExtend12_4095_toNat]
    have h_q1c_ge_1 : 1 ≤ q1c.toNat := by rw [h_q1c_eq]; exact Nat.succ_pos _
    have h_q1c_isLt : q1c.toNat < 2^64 := q1c.isLt
    have h_q1c_minus_1_lt : q1c.toNat - 1 < 2^64 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_q1c_isLt
    have h_rearrange : q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 := by
      have h := Nat.sub_add_cancel h_q1c_ge_1
      have h_pow : (2^64 : Nat) ≥ 1 := by decide
      omega
    rw [h_rearrange, Nat.add_mod_right, Nat.mod_eq_of_lt h_q1c_minus_1_lt]
    rw [h_q1c_eq]
    -- (q_true + 2) - 1 = q_true + 1.
    omega
  -- rhat' = rhatc + dHi.
  have h_rhat'_eq : rhat' = rhatc + dHi := by
    show (if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) = rhatc + dHi
    rw [if_pos h_BLTU_true]
  have h_rhatc_dHi_lt_pow64 : rhatc.toNat + dHi.toNat < 2^64 := by
    have : (2^32 + 2^32 : Nat) ≤ 2^64 := by decide
    omega
  have h_rhat'_toNat : rhat'.toNat = rhatc.toNat + dHi.toNat := by
    rw [h_rhat'_eq, BitVec.toNat_add]
    exact Nat.mod_eq_of_lt h_rhatc_dHi_lt_pow64
  -- Stub 3: rhat' < 2^32 (since q1c overshoots by 2).
  have h_stub3 := div128Quot_v2_phase1b_2nd_guard_under_runtime a b
    _hb3nz _hshift_nz _hbltu _hcarry2_nz _hborrow_v2
  simp only [] at h_stub3
  have h_rhat'_lt : rhat'.toNat < 2^32 := h_stub3 _h_overshoot
  -- Phase-2b guard: rhat' >> 32 = 0.
  have h_rhat'_shr_zero : rhat' >>> (32 : BitVec 6).toNat = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt h_rhat'_lt]; rfl
  -- Phase-1a Euclidean: q1c * dHi + rhatc = u4. With q1c = q_true + 2:
  have h_post1a : q1c.toNat * dHi.toNat + rhatc.toNat = u4.toNat :=
    div128Quot_first_round_post u4 dHi hdHi_ne hdHi_lt
  -- Phase-2b: q1'' = div128Quot_phase2b_q0' q1' rhat' dLo div_un1.
  show (div128Quot_phase2b_q0' q1' rhat' dLo div_un1).toNat = q_true
  unfold div128Quot_phase2b_q0'
  rw [if_pos h_rhat'_shr_zero]
  -- Inner BLTU check: q1' = q_true + 1 overshoots, so check FIRES.
  -- Untruncated check is (q_true + 1) * vTop > x, which is TRUE.
  have h_q1'_lt : q1'.toNat < 2^32 := by rw [h_q1'_toNat]; omega
  have h_q1'_dLo_lt_pow64 : q1'.toNat * dLo.toNat < 2^64 := by
    have h := Nat.mul_lt_mul_of_lt_of_lt h_q1'_lt hdLo_lt
    have h_pow : (2^32 * 2^32 : Nat) = 2^64 := by decide
    omega
  have h_q1'_dLo_word : (q1' * dLo).toNat = q1'.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt h_q1'_dLo_lt_pow64
  have h_rhatUn0_eq : ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1).toNat
      = rhat'.toNat * 2^32 + div_un1.toNat := by
    rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    exact EvmWord.halfword_combine rhat' div_un1 h_rhat'_lt h_div_un1_lt
  -- (q_true + 1) * vTop > x via x < (q_true + 1) * vTop.
  have h_x_lt_succ := x_lt_succ_div_mul (u4.toNat * 2^32 + div_un1.toNat)
    (dHi.toNat * 2^32 + dLo.toNat) h_vTop_pos
  rw [← h_q_true_def] at h_x_lt_succ
  -- q_true * dHi ≤ u4 (case 2: q1c = q_true + 2 → q1c * dHi = (q_true + 2) * dHi
  -- ≤ u4, so q_true * dHi ≤ u4 - 2*dHi ≤ u4).
  have h_qt_dHi_le : q_true * dHi.toNat ≤ u4.toNat := by
    rw [h_q1c_eq] at h_post1a
    have h_eq : (q_true + 2) * dHi.toNat = q_true * dHi.toNat + 2 * dHi.toNat := by ring
    omega
  have h_inner_BLTU_true :
      BitVec.ult ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1) (q1' * dLo) := by
    rw [EvmWord.ult_iff, h_rhatUn0_eq, h_q1'_dLo_word]
    -- rhat' * 2^32 + div_un1 < q1' * dLo where q1' = q_true + 1, rhat' = rhatc + dHi.
    rw [h_rhat'_toNat, h_q1'_toNat]
    -- (rhatc + dHi) * 2^32 + div_un1 < (q_true + 1) * dLo? Convert via Phase-1a.
    -- rhatc + dHi = u4 - q_true * dHi (from Phase-1a with q1c = q_true + 2):
    --   q1c * dHi + rhatc = u4 → (q_true + 2) * dHi + rhatc = u4
    --   → rhatc = u4 - (q_true + 2) * dHi = u4 - q_true * dHi - 2 * dHi.
    --   → rhatc + dHi = u4 - q_true * dHi - dHi.
    -- (rhatc + dHi) * 2^32 + div_un1 = u4*2^32 - q_true*dHi*2^32 - dHi*2^32 + div_un1
    --                                = x - q_true*dHi*2^32 - dHi*2^32
    -- Goal: this < (q_true + 1) * dLo
    -- ⟺ x < q_true*dHi*2^32 + dHi*2^32 + (q_true + 1) * dLo
    --     = (q_true + 1) * (dHi*2^32 + dLo)
    --     = (q_true + 1) * vTop
    -- which is TRUE.
    have h_rhatc_eq : rhatc.toNat = u4.toNat - q_true * dHi.toNat - 2 * dHi.toNat := by
      rw [h_q1c_eq] at h_post1a
      have h_eq : (q_true + 2) * dHi.toNat = q_true * dHi.toNat + 2 * dHi.toNat := by ring
      omega
    have h_succ_vTop : (q_true + 1) * (dHi.toNat * 2^32 + dLo.toNat) =
        (q_true + 1) * dHi.toNat * 2^32 + (q_true + 1) * dLo.toNat := by ring
    have h_qt_succ_dHi : (q_true + 1) * dHi.toNat = q_true * dHi.toNat + dHi.toNat := by ring
    -- Compute LHS step by step.
    have h_q1c_dHi_le : (q_true + 2) * dHi.toNat ≤ u4.toNat := by
      rw [h_q1c_eq] at h_post1a; omega
    have h_rhatc_plus_dHi : rhatc.toNat + dHi.toNat = u4.toNat - q_true * dHi.toNat - dHi.toNat := by
      rw [h_rhatc_eq]
      have h_eq : (q_true + 2) * dHi.toNat = q_true * dHi.toNat + 2 * dHi.toNat := by ring
      have h_2dHi : 2 * dHi.toNat = dHi.toNat + dHi.toNat := by ring
      omega
    have h_lhs : (rhatc.toNat + dHi.toNat) * 2^32 + div_un1.toNat
        = u4.toNat * 2^32 - q_true * dHi.toNat * 2^32 - dHi.toNat * 2^32 + div_un1.toNat := by
      rw [h_rhatc_plus_dHi]
      have h_sub_mul : (u4.toNat - q_true * dHi.toNat - dHi.toNat) * 2^32 =
          u4.toNat * 2^32 - q_true * dHi.toNat * 2^32 - dHi.toNat * 2^32 := by
        rw [Nat.sub_mul, Nat.sub_mul]
      rw [h_sub_mul]
    rw [h_lhs]
    -- Goal: u4 * 2^32 - q_true*dHi*2^32 - dHi*2^32 + div_un1 < (q_true + 1) * dLo
    -- Use h_x_lt_succ: x = u4*2^32 + div_un1 < (q_true + 1) * (dHi*2^32 + dLo).
    -- Rearrange.
    have h_succ_vTop_expand : (q_true + 1) * (dHi.toNat * 2^32 + dLo.toNat) =
        q_true * dHi.toNat * 2^32 + dHi.toNat * 2^32 + (q_true + 1) * dLo.toNat := by
      rw [h_succ_vTop, h_qt_succ_dHi]
      ring
    rw [h_succ_vTop_expand] at h_x_lt_succ
    -- u4 * 2^32 + div_un1 < q_true*dHi*2^32 + dHi*2^32 + (q_true + 1) * dLo.
    -- ⟺ u4 * 2^32 - q_true*dHi*2^32 - dHi*2^32 + div_un1 < (q_true + 1) * dLo.
    have h_qt_dHi_2pow32_le : q_true * dHi.toNat * 2^32 ≤ u4.toNat * 2^32 :=
      Nat.mul_le_mul_right _ h_qt_dHi_le
    have h_dHi_2pow32_le : dHi.toNat * 2^32 ≤ u4.toNat * 2^32 - q_true * dHi.toNat * 2^32 := by
      -- Use a pure-Nat helper to avoid maxRecDepth in the larger context.
      have h_q1c_dHi_2pow32 : (q_true + 2) * dHi.toNat * 2^32 ≤ u4.toNat * 2^32 :=
        Nat.mul_le_mul_right _ h_q1c_dHi_le
      exact case_2_dHi_2pow32_le_arith q_true dHi.toNat (u4.toNat * 2^32)
        (q_true * dHi.toNat * 2^32) (dHi.toNat * 2^32)
        (by ring) (by ring) h_q1c_dHi_2pow32
    omega
  rw [if_pos h_inner_BLTU_true]
  -- Returns q1' + signExtend12 4095 = q1' - 1 = q_true.
  rw [BitVec.toNat_add, signExtend12_4095_toNat]
  have h_q1'_ge_1 : 1 ≤ q1'.toNat := by rw [h_q1'_toNat]; exact Nat.succ_pos _
  have h_q1'_isLt : q1'.toNat < 2^64 := q1'.isLt
  have h_q1'_minus_1_lt : q1'.toNat - 1 < 2^64 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_q1'_isLt
  have h_rearrange : q1'.toNat + (2^64 - 1) = (q1'.toNat - 1) + 2^64 := by
    have h := Nat.sub_add_cancel h_q1'_ge_1
    have h_pow : (2^64 : Nat) ≥ 1 := by decide
    omega
  rw [h_rearrange, Nat.add_mod_right, Nat.mod_eq_of_lt h_q1'_minus_1_lt]
  rw [h_q1'_toNat]
  omega

/-- The Phase-1 division invariant — derived from the 3 Knuth-D
    decomposition stubs. The invariant body composes the trio:
    1. `_phase1c_in_knuth_range`: q1c ∈ [q*, q*+2].
    2. `_phase1b_check_iff_overshoot`: 1st check ⟺ q1c overshoots.
    3. `_phase1b_2nd_guard`: when 2nd correction needed, guard fires.

    Combined with the proven Phase-1 Euclideans
    (`div128Quot_first_round_post`, `div128Quot_phase1b_post`,
    `div128Quot_v2_phase1b_2nd_post`), they pin q1'' = q*.

    Composition strategy: `_phase1c_in_knuth_range_under_runtime` gives
    `q_true ≤ q1c.toNat ≤ q_true + 2`, so the overshoot
    `k = q1c.toNat - q_true ∈ {0, 1, 2}`. Dispatch via case-split to
    `_overshoot_{0,1,2}_sub` sub-lemmas. -/
theorem div128Quot_v2_phase1_div_invariant_under_runtime (a b : EvmWord)
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
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (u4.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo
        rhatUn1 q1' rhat' q1''
  -- Stub 1 gives q_true ≤ q1c.toNat ≤ q_true + 2. Force the
  -- types into local-let form via explicit type annotations
  -- (definitional equality between Stub-1's full expression and our lets).
  have h_q_true_le :
      (u4.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat) ≤
        q1c.toNat :=
    (div128Quot_v2_phase1c_in_knuth_range_under_runtime a b _hb3nz _hshift_nz
      _hbltu _hcarry2_nz _hborrow_v2).1
  have h_q1c_le :
      q1c.toNat ≤
        (u4.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat) + 2 :=
    (div128Quot_v2_phase1c_in_knuth_range_under_runtime a b _hb3nz _hshift_nz
      _hbltu _hcarry2_nz _hborrow_v2).2
  -- Case-split on overshoot k = q1c.toNat - q_true ∈ {0, 1, 2}, where
  -- q_true = (u4 * 2^32 + div_un1) / (dHi * 2^32 + dLo). Use the
  -- expression directly to avoid definitional unification issues.
  rcases Nat.lt_or_ge q1c.toNat
      ((u4.toNat * 2^32 + div_un1.toNat) /
       (dHi.toNat * 2^32 + dLo.toNat) + 1) with h1 | h1
  · -- q1c.toNat = q_true (overshoot 0).
    have h_eq : q1c.toNat = (u4.toNat * 2^32 + div_un1.toNat) /
                            (dHi.toNat * 2^32 + dLo.toNat) := by omega
    exact div128Quot_v2_phase1_div_invariant_overshoot_0_sub a b
      _hb3nz _hshift_nz _hbltu _hcarry2_nz _hborrow_v2 h_eq
  · rcases Nat.lt_or_ge q1c.toNat
        ((u4.toNat * 2^32 + div_un1.toNat) /
         (dHi.toNat * 2^32 + dLo.toNat) + 2) with h2 | h2
    · -- q1c.toNat = q_true + 1 (overshoot 1).
      have h_eq : q1c.toNat = (u4.toNat * 2^32 + div_un1.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) + 1 := by omega
      exact div128Quot_v2_phase1_div_invariant_overshoot_1_sub a b
        _hb3nz _hshift_nz _hbltu _hcarry2_nz _hborrow_v2 h_eq
    · -- q1c.toNat = q_true + 2 (overshoot 2).
      have h_eq : q1c.toNat = (u4.toNat * 2^32 + div_un1.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) + 2 := by omega
      exact div128Quot_v2_phase1_div_invariant_overshoot_2_sub a b
        _hb3nz _hshift_nz _hbltu _hcarry2_nz _hborrow_v2 h_eq

theorem div128Quot_v2_knuth_A_under_runtime (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
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
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    -- Knuth-A v2: q1'' is at least the true Phase-1 quotient.
    q1''.toNat ≥ (u4.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat) := by
  -- From the invariant `q1'' = floor(x/vTop)`, Knuth-A v2 (q1'' ≥ floor(x/vTop))
  -- follows trivially by `Nat.le_of_eq` (in fact, equality holds).
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo
        rhatUn1 q1' rhat' q1''
  have h_inv := div128Quot_v2_phase1_div_invariant_under_runtime a b hb3nz hshift_nz
    hbltu hcarry2_nz hborrow_v2
  simp only [] at h_inv
  exact Nat.le_of_eq h_inv.symm

/-- **Phase-1 no-wrap lower (untruncated) under runtime preconditions** —
    the standalone version of Conj 1 of
    `div128Quot_v2_no_wrap_under_call_addback_beq_untruncated`.

    Extracted as a standalone stub so consumers (`un21_lt_vTop_under_runtime`,
    no_wrap's conj1) can both invoke it without a circular forward
    reference (no_wrap is defined AFTER `un21_lt_vTop`, so un21_lt_vTop
    can't invoke no_wrap to extract conj1).

    Equivalent (via the algebraic identity `rhat'' * 2^32 + div_un1 -
    q1'' * dLo = x - q1'' * vTop`, where `x = uHi * 2^32 + div_un1`)
    to `q1'' * vTop ≤ x`, i.e. `q1'' ≤ x / vTop`. This is the Knuth-D
    2-correction invariant: after the second Phase 1b correction (the
    v2 fix), the trial quotient doesn't overshoot.

    **Closure plan (DUAL of `div128Quot_v2_knuth_A_under_runtime`).**

    This is the UPPER bound (q1'' ≤ floor(x/vTop)); the dual is the
    LOWER bound (q1'' ≥ floor(x/vTop)). Together they pin q1'' = floor(x/vTop).

    The proof follows Knuth's classical D3 analysis from the OPPOSITE
    direction (Knuth-B):

    1. **Initial trial overshoot bound (Knuth-B baseline)**: by
       `rv64_divu`, q1c ≥ floor(uHi/dHi) - 1 (with hi1-clamping),
       which gives q1c * vTop ≥ x - vTop - dHi*2^32 - dLo (initial
       overshoot can be up to 2 by Knuth's analysis).

    2. **Phase 1b 1st correction effect**: q1' = q1c if check doesn't
       fire (q1c not overshooting), or q1' = q1c - 1 if check fires
       (q1c overshooting by ≥ 1, so q1c - 1 ≤ floor(x/vTop) + 1).
       After 1 correction, q1' ≤ floor(x/vTop) + 1 (i.e., overshoot
       ≤ 1).

    3. **Phase 1b 2nd correction effect (v2-specific KEY)**: when
       q1' overshoots by 1 (i.e., q1' * dLo > rhat' * 2^32 + div_un1),
       the BLTU check fires and decrements q1' → q1'' = q1' - 1.
       After 2 corrections: q1'' ≤ floor(x/vTop) (i.e., overshoot 0).

    4. **CRITICAL trigger condition (the v2 fix)**: the 2nd D3 correction
       fires only when guard `rhat' < 2^32` AND check
       `(rhat' << 32) | div_un1 < q1' * dLo`. The contrapositive:
       if either guard fails (rhat' ≥ 2^32) or check fails
       (rhat' * 2^32 + div_un1 ≥ q1' * dLo), then q1'' = q1' and
       Phase-1 no_wrap_lo holds directly (the latter case is
       definitional; the former requires showing q1' * vTop ≤ x even
       when guard fails).

    **Concrete dependencies (all PROVEN, same as Knuth-A v2):**
    - `div128Quot_first_round_post` (Phase 1a Euclidean).
    - `div128Quot_phase1b_post` (Phase 1b 1st post Euclidean).
    - `div128Quot_v2_phase1b_2nd_post` (Phase 1b 2nd post Euclidean).
    - `div128Quot_phase1b_check_implies_q1c_pos` (BLTU → q1c ≥ 1).

    **Pure-Nat algebraic core**: introduce a private helper
    `phase1_no_wrap_lo_v2_pure_nat` taking the Phase-1 Euclidean facts
    and BLTU check semantics, returning the no_wrap upper bound. This
    factors out the Word/Nat noise.

    **Strategy: prove DUALLY with Knuth-A v2.** Since the same
    algebraic Euclidean facts and BLTU semantics drive both proofs,
    one strategy is:
    a. Define a single private "Phase-1 invariant" `phase1_eucl_inv`
       capturing the post-Phase-1b-2nd state (Euclidean + correction
       relations as a record).
    b. Prove the invariant from runtime preconds (1 stub).
    c. Derive both Knuth-A v2 (lower) and phase1_no_wrap_lo (upper)
       from the invariant by pure-Nat algebra (2 helpers).

    This factoring would close BOTH sorries with one substantive
    proof (the invariant) plus two mechanical algebra helpers.

    **Estimated proof length**: ~120-150 lines for the invariant +
    ~30 lines per Word-Nat bridge × 2.

    Issue #1337 algorithm fix migration. Path-3 substantive blocker. -/
theorem div128Quot_v2_phase1_no_wrap_lo_under_runtime (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
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
    q1''.toNat * dLo.toNat ≤ rhat''.toNat * 2^32 + div_un1.toNat := by
  -- Closure via the Phase-1 division invariant + Phase-1 Euclidean.
  --
  -- From invariant: q1''.toNat = floor(x / vTop) where x = u4*2^32 + div_un1,
  -- vTop = dHi*2^32 + dLo. Hence q1'' * vTop ≤ x (Nat.div_mul_le_self).
  --
  -- From Phase-1 Euclidean (proven via div128Quot_v2_phase1b_2nd_post):
  -- q1'' * dHi + rhat'' = u4. Substituting into the goal converts
  -- (q1'' * dLo ≤ rhat'' * 2^32 + div_un1) ⟺ (q1'' * vTop ≤ x).
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo
        rhatUn1 q1' rhat' q1'' rhat''
  -- Standard arithmetic facts.
  have h_b3'_ge_pow63 : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 b3' h_b3'_ge_pow63
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  -- Phase-1 Euclidean: q1'' * dHi + rhat'' = u4.
  have h_post1a := div128Quot_first_round_post u4 dHi hdHi_ne hdHi_lt
  have h_eucl_1st : q1'.toNat * dHi.toNat + rhat'.toNat = u4.toNat :=
    div128Quot_phase1b_post u4 dHi q1c rhatc dLo rhatUn1 hdHi_lt h_post1a
      (div128Quot_rhatc_lt_2dHi u4 dHi hdHi_ne hdHi_lt)
  have h_eucl_2nd : q1''.toNat * dHi.toNat + rhat''.toNat = u4.toNat :=
    div128Quot_v2_phase1b_2nd_post u4 dHi q1' rhat' dLo div_un1
      hdHi_ge hdHi_lt h_eucl_1st
  -- Phase-1 division invariant: q1'' = floor(x/vTop).
  have h_inv := div128Quot_v2_phase1_div_invariant_under_runtime a b
    hb3nz hshift_nz hbltu hcarry2_nz hborrow_v2
  simp only [] at h_inv
  -- vTop > 0 (= dHi*2^32 + dLo > 0).
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h1 : dHi.toNat * 2^32 ≥ 2^31 * 2^32 := Nat.mul_le_mul_right _ hdHi_ge
    have h_pow : (2 ^ 31 * 2 ^ 32 : ℕ) = 2 ^ 63 := by decide
    omega
  -- From invariant: q1'' * vTop ≤ x.
  have h_q1pp_vTop_le_x :
      q1''.toNat * (dHi.toNat * 2^32 + dLo.toNat) ≤ u4.toNat * 2^32 + div_un1.toNat := by
    rw [h_inv]
    -- (x/vTop) * vTop ≤ x via Nat.div_mul_le_self.
    have h := Nat.div_mul_le_self (u4.toNat * 2^32 + div_un1.toNat)
      (dHi.toNat * 2^32 + dLo.toNat)
    exact h
  -- Algebra: q1'' * vTop ≤ x ⟺ q1'' * dLo ≤ rhat'' * 2^32 + div_un1.
  -- Both directions use the Euclidean h_eucl_2nd: rhat'' = u4 - q1'' * dHi.
  have h_q1pp_dHi_le : q1''.toNat * dHi.toNat ≤ u4.toNat := by linarith [h_eucl_2nd]
  have h_q1pp_dHi_2pow32_le : q1''.toNat * dHi.toNat * 2^32 ≤ u4.toNat * 2^32 :=
    Nat.mul_le_mul_right _ h_q1pp_dHi_le
  have h_rhat_eq : rhat''.toNat = u4.toNat - q1''.toNat * dHi.toNat := by omega
  have h_rhat_2pow32 : rhat''.toNat * 2^32 = u4.toNat * 2^32 - q1''.toNat * dHi.toNat * 2^32 := by
    rw [h_rhat_eq, Nat.sub_mul]
  have h_q1pp_vTop : q1''.toNat * (dHi.toNat * 2^32 + dLo.toNat) =
      q1''.toNat * dHi.toNat * 2^32 + q1''.toNat * dLo.toNat := by ring
  omega

/-- **un21 < vTop under runtime preconditions** — the strong Phase-1
    upper bound that Conj 2 of `div128Quot_v2_no_wrap_under_call_addback_beq_untruncated`
    only weakly captures (`< 2^64` instead of `< vTop`).

    Decomposes into:
    - `div128Quot_v2_knuth_A_under_runtime` (substantive stub) —
      the algorithm-level Knuth-A claim `q1'' ≥ floor(x/vTop)`.
    - `div128Quot_v2_phase1_no_wrap_lo_under_runtime` (substantive stub) —
      the q1'' upper bound (extracted from no_wrap's conj1).
    - Algorithm Phase-1 Euclidean (existing helpers, mechanical).

    The 2-correction structure of v2 makes Knuth-A tractable in principle,
    but it remains the substantive Phase-1 blocker.

    **Consumers:**
    - `div128Quot_v2_no_wrap_under_call_addback_beq_untruncated` Conj 4:
      chains via `div128Quot_q0_prime_lt_pow32` to `q0' < 2^32`.
    - `div128Quot_v2_no_wrap_under_call_addback_beq_untruncated` Conj 2:
      `un21 < vTop ≤ 2^64` directly implies the < 2^64 conjunct.

    Issue #1337 algorithm fix migration. Path-3 derived blocker (composes
    Knuth-A + phase1_no_wrap_lo + algebra). -/
theorem div128Quot_v2_un21_lt_vTop_under_runtime (a b : EvmWord)
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
    un21.toNat < dHi.toNat * 2^32 + dLo.toNat := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo
        rhatUn1 q1' rhat' q1'' rhat'' cu_rhat_un1 cu_q1_dlo un21
  -- Setup standard arithmetic facts.
  have h_b3'_ge_pow63 : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) _hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 b3' h_b3'_ge_pow63
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  -- Phase 1 Euclidean (1st + 2nd D3).
  have h_post1a := div128Quot_first_round_post u4 dHi hdHi_ne hdHi_lt
  have h_eucl_1st : q1'.toNat * dHi.toNat + rhat'.toNat = u4.toNat :=
    div128Quot_phase1b_post u4 dHi q1c rhatc dLo rhatUn1 hdHi_lt h_post1a
      (div128Quot_rhatc_lt_2dHi u4 dHi hdHi_ne hdHi_lt)
  have h_eucl_2nd : q1''.toNat * dHi.toNat + rhat''.toNat = u4.toNat :=
    div128Quot_v2_phase1b_2nd_post u4 dHi q1' rhat' dLo div_un1
      hdHi_ge hdHi_lt h_eucl_1st
  -- Knuth-A v2 (sorry'd).
  have h_knuthA := div128Quot_v2_knuth_A_under_runtime a b _hb3nz _hshift_nz
    _hbltu _hcarry2_nz _hborrow_v2
  simp only [] at h_knuthA
  -- conj1 (sorry'd, via standalone helper).
  have h_conj1 := div128Quot_v2_phase1_no_wrap_lo_under_runtime a b _hb3nz _hshift_nz
    _hbltu _hcarry2_nz _hborrow_v2
  simp only [] at h_conj1
  -- conj2 (PROVEN via algebraic combiner).
  have h_conj2 : rhat''.toNat * 2^32 + div_un1.toNat - q1''.toNat * dLo.toNat < 2^64 :=
    conj2_arith u4.toNat div_un1.toNat q1''.toNat rhat''.toNat
      dHi.toNat dLo.toNat h_eucl_2nd hdHi_lt hdLo_lt hdHi_ge h_knuthA
  -- Apply un21<vTop algebraic combiner (PROVEN, returns A_un - B < vTop).
  have h_alg : rhat''.toNat * 2^32 + div_un1.toNat - q1''.toNat * dLo.toNat <
      dHi.toNat * 2^32 + dLo.toNat :=
    un21_lt_vTop_arith u4.toNat div_un1.toNat q1''.toNat rhat''.toNat
      dHi.toNat dLo.toNat h_eucl_2nd hdHi_lt hdLo_lt hdHi_ge h_knuthA
  -- Bridge: un21.toNat = (A_un - B) via _un21_toNat_untruncated, under conj1+conj2.
  have huHi_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    have h_b3'_decomp : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
      div128Quot_vTop_decomp b3'
    have hu4_lt_b3' : u4.toNat < b3'.toNat :=
      isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
        (isCallTrialN4Evm_def ▸ _hbltu)
    omega
  have h_un21_eq :=
    div128Quot_v2_un21_toNat_untruncated u4 un3 b3' hdHi_ge hdLo_lt huHi_lt_vTop
      h_conj1 h_conj2
  simp only [] at h_un21_eq
  rw [h_un21_eq]
  exact h_alg

/-- **qHat * val256(b_shifted) > val256(a_shifted) under v2 borrow** —
    the shifted-domain version of `qHat_gt_q_true`. This statement is
    DIRECTLY derivable from `c3_un_zero_of_qHat_mul_le`'s contrapositive,
    avoiding the truncation issue with `q_true` (the original-domain
    quotient).

    Key insight: `c3_un_zero_of_qHat_mul_le` operates on raw limbs
    (whatever they are). In our setting the inputs are SHIFTED limbs,
    so the conclusion `qHat * val256(SHIFTED b) > val256(SHIFTED a)` is
    immediate from `c3 ≠ 0`.

    Issue #1337 algorithm fix migration. Path 3 shifted-domain sub-lemma. -/
theorem qHat_mul_b_shifted_gt_a_shifted_under_runtime_v2 (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    qHat.toNat * val256 b0' b1' b2' b3' > val256 u0 u1 u2 u3 := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat
  -- Step 1: hborrow_v2 → c3 ≠ 0 via u_top_lt_c3.
  rw [isAddbackBorrowN4CallEvm_v2_def] at hborrow_v2
  have h_u4_lt_c3 := EvmWord.u_top_lt_c3_of_addback_borrow_call_v2
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hborrow_v2
  simp only [] at h_u4_lt_c3
  -- Step 2: contrapositive of `c3_un_zero_of_qHat_mul_le` — c3 ≠ 0 ⟹
  --   qHat * val256(b_shifted) > val256(a_shifted).
  by_contra hle
  push Not at hle
  -- hle : qHat.toNat * val256 b0' b1' b2' b3' ≤ val256 u0 u1 u2 u3.
  have h_c3_zero := c3_un_zero_of_qHat_mul_le hle
  -- h_c3_zero : (mulsubN4 ...).2.2.2.2 = 0 (as Word).
  -- h_u4_lt_c3 : u4.toNat < (mulsubN4 ...).2.2.2.2.toNat.
  -- Combine: u4.toNat < 0, contradiction.
  -- Bridge h_c3_zero (Word equality) to a Nat equality on the same expression.
  have h_zero : (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat = 0 := by
    rw [h_c3_zero]; rfl
  -- Convert h_u4_lt_c3 (unfolded form) to use the local lets via `change`
  -- (definitional equality through zeta-reduction of qHat, b0', etc.).
  change u4.toNat < (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
    at h_u4_lt_c3
  omega

/-- **qHat > val256(a_shifted) / val256(b_shifted) under v2 borrow** —
    direct corollary of `qHat_mul_b_shifted_gt_a_shifted_under_runtime_v2`.

    Converts the multiplicative form `qHat * val256(b') > val256(a')` to
    the divisor form `qHat > val256(a') / val256(b')` via Nat division.
    Useful for the shifted-domain carry partition.

    Issue #1337 algorithm fix migration. -/
theorem qHat_gt_q_true_shifted_under_runtime_v2 (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    qHat.toNat > val256 u0 u1 u2 u3 / val256 b0' b1' b2' b3' := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat
  have h_mul := qHat_mul_b_shifted_gt_a_shifted_under_runtime_v2 a b hb3nz hborrow_v2
  simp only [] at h_mul
  -- h_mul : qHat.toNat * val256 b0' b1' b2' b3' > val256 u0 u1 u2 u3.
  -- Need val256 b' > 0 to use Nat.div_lt_iff.
  have h_b3'_ge : b3'.toNat ≥ 2^63 := b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2)
    hb3nz (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1)
  have h_v_pos : val256 b0' b1' b2' b3' > 0 := by
    show b0'.toNat + b1'.toNat * 2^64 + b2'.toNat * 2^128 + b3'.toNat * 2^192 > 0
    have : b3'.toNat * 2^192 > 0 := by positivity
    omega
  exact (Nat.div_lt_iff_lt_mul h_v_pos).mpr h_mul

/-- **qHat lower bound shifted-domain (ALONE)** — extracted from
    `qHat_in_range_under_runtime_v2` for direct use with the proven
    `qHat_gt_q_true_shifted_under_runtime_v2`. Just the lower-bound half.

    Issue #1337 algorithm fix migration. -/
theorem qHat_lower_shifted_under_runtime_v2 (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    val256 u0 u1 u2 u3 / val256 b0' b1' b2' b3' + 1 ≤ qHat.toNat := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat
  have h := qHat_gt_q_true_shifted_under_runtime_v2 a b hb3nz hborrow_v2
  simp only [] at h
  -- Convert h's unfolded form to use local lets for omega.
  change qHat.toNat > val256 u0 u1 u2 u3 / val256 b0' b1' b2' b3' at h
  omega

theorem n4CallAddbackBeqSemanticHolds_def {a b : EvmWord} :
    n4CallAddbackBeqSemanticHolds a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     let q_out : Word :=
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095
     q_out.toNat =
       val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl

/-- **Call+addback BEQ n=4 div getLimbN bridge.** Under the runtime conditions
    + `n4CallAddbackBeqSemanticHolds`, the post-addback corrected quotient
    `q_out` equals `(EvmWord.div a b).getLimbN 0`, and the upper three
    quotient limbs are zero.

    Simpler than the call-skip bridge: hsem directly gives the tight equality
    `q_out.toNat = val256(a)/val256(b)`, so we don't need to combine with T3.
    From that, `(EvmWord.div a b).toNat = q_out.toNat` via `BitVec.toNat_udiv`,
    and `q_out : Word` bounds pin the limbs.

    **VACUITY note (2026-04-27)**: per
    `n4CallAddbackBeqSemanticHolds_counterexample` (below), the `hsem`
    hypothesis is FALSE on a class of runtime-reachable inputs — the
    algorithm overshoots q_true by ~2^32 in those cases. So this bridge
    cannot be applied to derive correctness on the full input space;
    callers must restrict to inputs where `hsem` is independently
    discharged (currently impossible without algorithm fix). -/
theorem n4_call_addback_beq_div_mod_getLimbN (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_out : Word :=
      if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
      else qHat + signExtend12 4095
    (EvmWord.div a b).getLimbN 0 = q_out ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms carry q_out
  rw [n4CallAddbackBeqSemanticHolds_def] at hsem
  change q_out.toNat = val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) at hsem
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [ha_val, hb_val] at hsem
  -- hsem : q_out.toNat = a.toNat / b.toNat
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div
    rw [if_neg hbnz]
    exact BitVec.toNat_udiv
  set q_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => q_out | 1 => 0 | 2 => 0 | 3 => 0 with hq_target
  have hq_target_toNat : q_target.toNat = q_out.toNat := by
    simp [q_target, EvmWord.fromLimbs_toNat]
  have hq_eq_div : q_target = EvmWord.div a b :=
    BitVec.eq_of_toNat_eq (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_3

/-- **EVM-stack-level DIV spec on the n=4 call+addback BEQ sub-path.**

    Mirror of `evm_div_n4_call_skip_stack_spec` for the addback BEQ branch.
    Consumes runtime conditions, shift-nonzero, alignment, validity, and
    the semantic-correctness fact `n4CallAddbackBeqSemanticHolds`. Output
    shape is `divN4CallSkipStackPost` (same as call-skip — both paths
    produce identical stack layouts on success). -/
theorem evm_div_n4_call_addback_beq_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin 340 base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  have h_pre := evm_div_n4_full_call_addback_beq_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_addback_beq_div_mod_getLimbN a b hbnz hsem
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullDivN4CallAddbackBeqPost_unfold, denormDivPost_unfold] at hq
  apply div_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) = _
      from by rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
                  hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

end EvmAsm.Evm64
