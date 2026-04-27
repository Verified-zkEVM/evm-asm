-- file-size-exception: tracked by #66 / #61 (call-addback BEQ Word-level wrappers + closure are still being filled in; further sub-split deferred until the chain stabilizes).
/-
  EvmAsm.Evm64.DivMod.SpecCallAddbackBeq

  Call+addback BEQ semantic predicates and stack specs (n=4, shift ≠ 0).
  Split from `SpecCall.lean` to ease the file-size guardrail.

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
  - Word-level Euclideans (mulsub, addback) and val256 bounds.
  - Word-level wrappers (post1_val_eq_amod_pow_s_of_single_addback,
    abPrime_val_eq_amod_pow_s_of_double_addback).
  - Adapter / parent + final stack specs.
-/

import EvmAsm.Evm64.DivMod.SpecCall
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

/-- **Formal counterexample to `n4CallAddbackBeqSemanticHolds`** (2026-04-27).

    Concrete (a, b) satisfying all runtime preconditions of
    `evm_div_n4_full_call_addback_beq_stack_pre_spec` but for which the
    predicate is FALSE — algorithm overshoots true quotient by 2^32-2.

    Witness:
    - `a = (2^63 + 2^33) * 2^192` (a3 = 2^63 + 2^33, lower limbs zero)
    - `b = 2^192 + (2^33 - 1) * 2^128` (b3 = 1, b2 = 2^33 - 1, lower zero)
    - q_true = `val256(a) / val256(b) = 2^63 + 2^32 - 2`
    - qHat = `div128Quot(...) = 2^63 + 2^33 - 3`
    - Algorithm's q_out = qHat - 1 = 2^63 + 2^33 - 4 ≠ q_true.

    See `memory/project_n4callbeq_addback_overshoot_2pow32.md` for the
    full analysis. The proof is by `decide` after unfolding the
    predicate — Lean evaluates the Prop directly on the concrete
    Word inputs.

    **Precise bug class**: the algorithm is correct iff `q1' = q_true_1`
    (high digit exact), which holds iff Knuth's D3 correction loop
    finishes within 1 iteration. The bug fires precisely on inputs
    where Knuth's D3 needs the 2nd correction iteration — initial
    `q̂ = q_true_1 + 2` AND both 1st and 2nd D3 checks fire. Our
    1-correction `div128Quot` only does the 1st. In our counterexample,
    `q̂ = 2^31 + 2`, after 1 correction `q1' = 2^31 + 1`, but
    `q_true_1 = 2^31` (Knuth's full loop would do 2 corrections).

    **Implication**: this theorem proves that
    `n4CallAddbackBeqSemanticHolds_of_*` (any closure from runtime
    conditions) cannot exist FOR V1 — the v1 predicate is genuinely false
    on runtime-reachable inputs.

    **STATUS (2026-04-27):** the algorithm IS fixed via `div128Quot_v2`
    (Lean) and `divK_div128_v2` (RISC-V, PR #1389 merged). The v2
    predicate `n4CallAddbackBeqSemanticHolds_v2` HOLDS on this same
    counterexample input (see `n4CallAddbackBeqSemanticHolds_v2_holds_on_counterexample`
    below). After full v2 migration (path 3 closure: PR #1393), the v2
    user-facing theorem will subsume this; this v1 counterexample becomes
    a now-vacuous reminder of why the migration was needed and can be
    deleted. -/
theorem n4CallAddbackBeqSemanticHolds_counterexample :
    ¬ (n4CallAddbackBeqSemanticHolds
        (EvmWord.fromLimbs (fun i => match i with
          | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33)))
        (EvmWord.fromLimbs (fun i => match i with
          | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1))) := by
  unfold n4CallAddbackBeqSemanticHolds
  decide

/-- **Fix verification**: `div128Quot_v2` (the FIXED version with 2 D3
    iterations, in `LoopDefs/Iter.lean`) produces the CORRECT quotient
    on the counterexample input where the original buggy `div128Quot`
    fails. Kernel-checked via `decide`.

    This proves the migration target works (qHat overshoot drops from
    2^32-1 to just 1, within Knuth-B bound). The remaining work is to
    update the actual RISC-V program at `Program.lean:divK_div128` to
    add the corresponding 2nd D3 correction (~6 instructions after the
    existing one at lines 80-87), then migrate use-sites from
    `div128Quot` to `div128Quot_v2`.

    On the counterexample input, `div128Quot_v2 = q_true + 1 =
    9223372041149743103`, which is within Knuth-B bound (≤ q_true + 2).
    The outer addback BEQ branch's single-addback path then corrects
    by 1, giving the correct final `q_out = q_true`. -/
theorem div128Quot_v2_fixes_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
    -- q_true = 9223372041149743102 (val256(a) / val256(b))
    -- div128Quot_v2 produces q_true + 1 = 9223372041149743103
    -- which is within Knuth-B bound (≤ q_true + 2), so outer addback BEQ
    -- single-addback path corrects to q_true.
    (div128Quot_v2 u4 u3 b3').toNat = 9223372041149743103 := by
  decide

/-- **Bug confirmation**: `div128Quot` (the current/buggy version)
    produces the WRONG quotient on the counterexample input. The
    discrepancy is `2^32 - 2`. Pairs with `div128Quot_v2_fixes_counterexample`
    to demonstrate the fix is necessary. -/
theorem div128Quot_buggy_on_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
    -- Buggy version produces 9223372045444710397 (overshoots true quotient
    -- 9223372041149743102 by 2^32 - 1 = 4294967295).
    (div128Quot u4 u3 b3').toNat = 9223372045444710397 := by
  decide

/-- **v2 version of `n4CallAddbackBeqSemanticHolds`**, using `div128Quot_v2`
    (the fixed Knuth D 2-correction algorithm) instead of `div128Quot`
    (the buggy 1-correction version).

    Mirror of `n4CallAddbackBeqSemanticHolds` for the v2 algorithm.
    Used by downstream stack specs once they migrate from `div128Quot`
    to `div128Quot_v2`. The associated closure proofs
    (`n4CallAddbackBeqSemanticHolds_v2_of_*`) should be provable since
    the v2 algorithm correctly handles the Knuth D 2-correction case
    that breaks the original predicate (see
    `n4CallAddbackBeqSemanticHolds_counterexample`).

    Issue #1337's algorithm fix migration. Tracked alongside
    `div128_v2_spec` (PR #1392). -/
def n4CallAddbackBeqSemanticHolds_v2 (a b : EvmWord) : Prop :=
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
  let qHat := div128Quot_v2 u4 u3 b3'  -- v2: 2 D3 correction iterations.
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let q_out : Word :=
    if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
    else qHat + signExtend12 4095
  q_out.toNat =
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- The v2 predicate holds on the (a, b) input that broke the v1 predicate.
    Demonstrates the v2 fix works on the counterexample.

    With `div128Quot_v2` returning `q_true + 1`, the post-addback `q_out`
    correctly equals `q_true`. -/
theorem n4CallAddbackBeqSemanticHolds_v2_holds_on_counterexample :
    n4CallAddbackBeqSemanticHolds_v2
      (EvmWord.fromLimbs (fun i => match i with
        | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33)))
      (EvmWord.fromLimbs (fun i => match i with
        | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)) := by
  unfold n4CallAddbackBeqSemanticHolds_v2
  decide

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

/-- **Phase 1b 2nd D3 Euclidean invariant** for `div128Quot_v2`.

    The new substantive sub-lemma for v2: after the 2nd D3 correction
    iteration (gated by `rhat' >> 32 = 0`), the Euclidean invariant
    `q1'' * dHi + rhat'' = uHi` is preserved.

    Mirrors `div128Quot_phase1b_post` (KnuthTheoremB.lean:880) but for
    the 2nd correction iteration. The proof structure:
    - Guard taken (rhat' >> 32 ≠ 0): q1'' = q1', rhat'' = rhat',
      invariant carries through unchanged from `div128Quot_phase1b_post`.
    - Guard fall-through (rhat' >> 32 = 0):
      * Check fires (rhatUn1' < qDlo2): q1'' = q1' - 1, rhat'' = rhat' + dHi.
        Same algebra as 1st D3 correction (use `div128Quot_phase1b_correction_eucl`).
      * Check doesn't fire: q1'' = q1', rhat'' = rhat'.

    This sub-lemma plus the corresponding tightness `rhat'' < dHi` (under
    additional preconditions) lets us mirror v1's qHat_vTop_le proof
    without the no_wrap hypotheses (since the 2nd correction handles
    the truncation case that breaks v1).

    Issue #1337 algorithm fix migration. -/
theorem div128Quot_v2_phase1b_2nd_post
    (uHi dHi q1' rhat' dLo div_un1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (h_post_1st : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat) :
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    q1''.toNat * dHi.toNat + rhat''.toNat = uHi.toNat := by
  intro q1'' rhat''
  by_cases h_guard : rhat' >>> (32 : BitVec 6).toNat = 0
  · -- Guard fall-through: case-split on the BLTU check.
    by_cases h_check : BitVec.ult ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1)
                                    (q1' * dLo)
    · -- Check fires: q1'' = q1' - 1, rhat'' = rhat' + dHi.
      have h_q1'' : q1'' = q1' + signExtend12 4095 := by
        show div128Quot_phase2b_q0' q1' rhat' dLo div_un1 = _
        unfold div128Quot_phase2b_q0'
        rw [if_pos h_guard, if_pos h_check]
      have h_rhat'' : rhat'' = rhat' + dHi := by
        show (if rhat' >>> (32 : BitVec 6).toNat = 0 then _ else rhat') = _
        rw [if_pos h_guard, if_pos h_check]
      rw [h_q1'', h_rhat'']
      have h_q1'_pos : q1'.toNat ≥ 1 :=
        div128Quot_phase1b_check_implies_q1c_pos q1' dLo
          ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1) h_check
      -- Derive `rhat' < 2 * dHi` inline from h_guard + hdHi_ge.
      have h_rhat'_lt : rhat'.toNat < 2 * dHi.toNat := by
        have h_rhat'_lt_pow32 : rhat'.toNat < 2^32 := by
          have h := congrArg BitVec.toNat h_guard
          simp [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
                Nat.shiftRight_eq_div_pow] at h
          have h_word : rhat'.toNat < 2^64 := rhat'.isLt
          omega
        omega
      exact div128Quot_phase1b_correction_eucl uHi dHi q1' rhat'
        hdHi_lt h_post_1st h_q1'_pos h_rhat'_lt
    · -- Check doesn't fire: q1'' = q1', rhat'' = rhat'.
      have h_q1'' : q1'' = q1' := by
        show div128Quot_phase2b_q0' q1' rhat' dLo div_un1 = _
        unfold div128Quot_phase2b_q0'
        rw [if_pos h_guard, if_neg h_check]
      have h_rhat'' : rhat'' = rhat' := by
        show (if rhat' >>> (32 : BitVec 6).toNat = 0 then _ else rhat') = _
        rw [if_pos h_guard, if_neg h_check]
      rw [h_q1'', h_rhat''];  exact h_post_1st
  · -- Guard taken (rhat' >> 32 ≠ 0): q1'' = q1', rhat'' = rhat'.
    have h_q1'' : q1'' = q1' := by
      show div128Quot_phase2b_q0' q1' rhat' dLo div_un1 = _
      unfold div128Quot_phase2b_q0'
      rw [if_neg h_guard]
    have h_rhat'' : rhat'' = rhat' := by
      show (if rhat' >>> (32 : BitVec 6).toNat = 0 then _ else rhat') = _
      rw [if_neg h_guard]
    rw [h_q1'', h_rhat'']; exact h_post_1st

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
    simp [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
          Nat.shiftRight_eq_div_pow] at h
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
      simp [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
            Nat.shiftRight_eq_div_pow] at h
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

/-- **Numerical sanity check** for `div128Quot_v2_toNat_eq_strict` on the
    counterexample input. Verifies the halfword combine formula holds.
    Kernel-checked via `decide`. -/
theorem div128Quot_v2_toNat_eq_strict_test_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
    -- Recompute q1'', q0' to verify the halfword combine.
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
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
    (div128Quot_v2 u4 u3 b3').toNat = q1''.toNat * 2^32 + q0'.toNat := by
  decide

/-- **DISCOVERY (numerical, kernel-checked)**: the conjectured v2
    no-wrap bound `q1''.toNat * dLo.toNat ≤ (rhat''.toNat % 2^32) * 2^32
    + div_un1.toNat` is **FALSE** in general — fails on the counterexample
    input. See `div128Quot_v2_phase1_no_wrap_lo_FALSE_counterexample` below
    for the kernel-checked refutation.

    **Why**: under v2, when both D3 corrections fire, rhat'' = rhat' + dHi
    can land on/just past `2^32`. Then `rhat'' % 2^32` drops to 0 (or
    near zero), making the RHS small while LHS = q1'' * dLo remains large.

    This means the v2 algorithm fix does NOT eliminate the no-wrap
    hypotheses needed for the val256-level Knuth-B bound. Both v1 and v2
    require these hypotheses to be passed in (or discharged via other
    invariants from the Knuth Algorithm D analysis).

    **Implication**: `div128Quot_v2_qHat_vTop_le` should take no_wrap
    hypotheses (mirroring v1 exactly), not derive them automatically. -/
theorem div128Quot_v2_phase1_no_wrap_lo_FALSE_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
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
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    -- The no-wrap bound FAILS: LHS = 2^63 - 2^31 ≫ RHS = 0.
    ¬ (q1''.toNat * dLo.toNat ≤ (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat) := by
  decide

/-- **Untruncated phase-1 no-wrap invariant HOLDS on the same counterexample.**

    The truncated `(rhat''.toNat % 2^32) * 2^32` is too small here because
    `rhat'' = 2^32` truncates to 0. Without the truncation,
    `rhat''.toNat * 2^32 = 2^64` is large enough to dominate
    `q1''.toNat * dLo.toNat = 2^63 - 2^31`.

    This kernel-checked proof is the supporting evidence for **alternative
    path 3**: use the untruncated form `q1''.toNat * dLo.toNat ≤
    rhat''.toNat * 2^32 + div_un1.toNat` (with an additional upper-bound
    conjunct) as the discharge target. See
    `div128Quot_v2_no_wrap_under_call_addback_beq_untruncated`.

    The mathematical un21 = `(rhat''.toNat * 2^32 + div_un1.toNat) -
    q1''.toNat * dLo.toNat` then matches the algorithm's Word `un21.toNat`
    when in [0, 2^64) (since `cu_rhat_un1.toNat = rhat''.toNat * 2^32 +
    div_un1.toNat mod 2^64`). On this counterexample, math un21 = 2^63 +
    2^31 ∈ [0, 2^64), so they coincide.

    Issue #1337 algorithm fix migration. -/
theorem div128Quot_v2_phase1_no_wrap_lo_untruncated_HOLDS_on_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
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
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    -- The untruncated bound HOLDS: LHS = 2^63 - 2^31 ≤ 2^64 = RHS.
    q1''.toNat * dLo.toNat ≤ rhat''.toNat * 2^32 + div_un1.toNat := by
  decide

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

/-- Pure-Nat helper for the untruncated bridge: under the two-bound
    invariant `B ≤ A_trunc + k * 2^64` and `A_trunc + k * 2^64 - B < 2^64`,
    plus `A_trunc < 2^64` and `B < 2^64`, `(A_trunc + 2^64 - B) % 2^64 =
    A_trunc + k * 2^64 - B`. The bound forces `k ∈ {0, 1}`. -/
private theorem un21_toNat_untruncated_arith (A_trunc B k : ℕ)
    (h_A_trunc_lt : A_trunc < 2^64)
    (hB_lt : B < 2^64)
    (hBA' : B ≤ A_trunc + k * 2^64)
    (hAB' : A_trunc + k * 2^64 - B < 2^64) :
    (A_trunc + 2^64 - B) % 2^64 = A_trunc + k * 2^64 - B := by
  have hk_lt_2 : k < 2 := by
    by_contra hk_ge_2
    have hk_ge_2' : k ≥ 2 := Nat.not_lt.mp hk_ge_2
    have h1 : k * 2^64 ≥ 2 * 2^64 := Nat.mul_le_mul_right _ hk_ge_2'
    omega
  obtain hk0 | hk1 : k = 0 ∨ k = 1 := by omega
  · rw [hk0]
    have h_split : A_trunc + 2^64 - B = (A_trunc - B) + 2^64 := by omega
    rw [h_split, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : A_trunc - B < 2^64)]
    omega
  · rw [hk1]
    rw [Nat.mod_eq_of_lt (by omega : A_trunc + 2^64 - B < 2^64)]
    omega

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

/-- **Numerical sanity check** for `div128Quot_v2_qHat_vTop_le` on the
    counterexample input. Verifies the multiplication bound is at least
    consistent with the v2 algorithm. Kernel-checked via `decide`. -/
theorem div128Quot_v2_qHat_vTop_le_test_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
    -- div128Quot_v2 u4 u3 b3' = q_true + 1 = 9223372041149743103
    -- Times b3' (= 2^63 + (2^33 - 1) * 2^31 ≈ 2^63 + 2^63 - 2^31) should
    -- be ≤ u4 * 2^64 + u3 (= the dividend's high half).
    (div128Quot_v2 u4 u3 b3').toNat * b3'.toNat ≤ u4.toNat * 2^64 + u3.toNat := by
  decide

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

/-- **Untruncated runtime discharge** — alternative path 3 stub.

    **Note (2026-04-27):** the truncated counterpart of this discharge
    (with `(rhat''.toNat % 2^32) * 2^32` instead of `rhat''.toNat * 2^32`)
    was previously stubbed but is provably FALSE — see
    `div128Quot_v2_phase1_no_wrap_lo_FALSE_counterexample`. The
    architectural pivot to the untruncated form (this stub) was made in
    commits 1f9fcddd–5a14680b. Path 3 closes the closure proof via the
    untruncated chain.

    Uses the **untruncated** form of the phase-1 invariant — `rhat''.toNat
    * 2^32 + div_un1.toNat` — plus an additional upper-bound conjunct
    `A_un - B < 2^64` needed by `div128Quot_v2_un21_toNat_untruncated`.

    On the counterexample (a3=2^63+2^33, a2=a1=a0=0, b3=1, b2=2^33-1,
    b1=b0=0):
    - A_un = 2^32 * 2^32 + 0 = 2^64.
    - B = 2^31 * (2^32-1) = 2^63 - 2^31.
    - A_un - B = 2^63 + 2^31 < 2^64. ✓
    - B ≤ A_un. ✓
    See `div128Quot_v2_phase1_no_wrap_lo_untruncated_HOLDS_on_counterexample`.

    **This stub is the runtime discharge for the untruncated form** —
    expected TRUE (in contrast to the truncated form which is FALSE).
    Closing it requires a deeper analysis of how the runtime preconditions
    hbltu/hcarry2_nz/hborrow constrain rhat'' and q1''. The argument
    flows through the algorithm's invariants (Phase 1b 2nd D3 bound) +
    the addback's correctness witness (carry signaling).

    Issue #1337 algorithm fix migration. Alternative path 3. -/
theorem div128Quot_v2_no_wrap_under_call_addback_beq_untruncated (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hbltu : isCallTrialN4Evm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (_hborrow : isAddbackBorrowN4CallEvm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
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
    -- Untruncated phase-1 invariant (TWO conjuncts replacing the truncated one):
    q1''.toNat * dLo.toNat ≤ rhat''.toNat * 2^32 + div_un1.toNat ∧
    rhat''.toNat * 2^32 + div_un1.toNat - q1''.toNat * dLo.toNat < 2^64 ∧
    -- Phase-2 invariant (already untruncated in original, unchanged):
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat ∧
    q0'.toNat < 2^32 := by
  sorry  -- Discharge from runtime preconditions. The UNTRUNCATED phase-1
         -- invariants are TRUE (in contrast to the truncated FALSE one).
         --
         -- **KEY ALGEBRAIC INSIGHT (commit a8c6aee1+):** un21_math is
         -- exactly the remainder of `(uHi * 2^32 + div_un1) / vTop`.
         -- Let x := uHi * 2^32 + div_un1. From Phase 1b Euclidean
         -- (q1'' * dHi + rhat'' = uHi), we have:
         --    rhat'' * 2^32 + div_un1 - q1'' * dLo
         --  = uHi * 2^32 + div_un1 - q1'' * vTop  (where vTop = dHi * 2^32 + dLo)
         --  = x - q1'' * vTop
         -- Conjunct 1 (q1'' * vTop ≤ x) is equivalent to q1'' ≤ x / vTop.
         -- Knuth-A (post-2-correction) gives q1'' ≥ x / vTop.
         -- Combine: q1'' = x / vTop, hence un21_math = x mod vTop < vTop < 2^64.
         -- So conjunct 2 follows from conjunct 1 + Knuth-A.
         --
         -- **CONCRETE proof plan:**
         --  1. Conjunct 1 (untruncated lower): the substantive Knuth-D
         --     2-correction invariant. After 2 corrections in v2, q1''
         --     should satisfy q1'' * vTop ≤ uHi * 2^32 + div_un1 (the
         --     rationale for the 2nd correction). Discharge from the
         --     algorithm's structure + Phase 1b 2nd D3 trigger condition.
         --  2. Conjunct 2 (untruncated upper): follows from 1 + Knuth-A
         --     (q1'' ≥ floor(x/vTop)).
         --  3. Conjunct 3 (phase-2 untruncated): mirror argument for
         --     Phase 2 (q0' computation on un21). Symmetric to 1.
         --  4. Conjunct 4 (q0' < 2^32): standard halfword bound.
         --
         -- **CONNECTION TO v1'S OPEN PROBLEM (Div128KnuthLower.lean:615):**
         -- `knuth_compose_weak_lower_nat` requires a "Phase 1 tight"
         -- hypothesis `q1' * vTop + un21 = uHi * 2^32 + uLo_hi` with
         -- `un21 < vTop`. That hypothesis is exactly conjunct 1 + 2 of
         -- this stub (per the algebraic identity un21_math = x - q1'' * vTop).
         -- v1's comment: "tight Phase 1 hypothesis is currently unproven
         -- (requires Knuth Theorem C Word-level)". So conjunct 2 = the
         -- tight Phase 1 statement, equivalent to the v1 open problem.
         -- Closing it for v2 (where 2 corrections give better bounds)
         -- may be tractable via the 2nd D3 correction's trigger condition.

/-- **qHat range under runtime preconditions (sub-lemma).** Under
    runtime preconds (`hbltu, hcarry2_nz, hborrow`), the v2 algorithm's
    qHat is in `{q_true + 1, q_true + 2}` (equivalently, `q_true + 1 ≤
    qHat ≤ q_true + 2`).

    This decomposes the carry partition: combined with the partition's
    "carry encodes overshoot" claim, it pins qHat to a specific value.

    Proof sketch:
    - Upper bound `qHat ≤ q_true + 2`: from path 3's
      `div128Quot_v2_le_val256_div_plus_two_untruncated` (PROVEN), once
      the `_no_wrap_under_call_addback_beq_untruncated` stub is closed.
    - Lower bound `qHat ≥ q_true + 1`: from runtime forcing
      qHat * b > a (BEQ branch reached, so at least one addback fired,
      meaning qHat overshoots by at least 1). Uses `hborrow` (mulsub
      borrow ≠ 0 ⟺ qHat * b > a as Nat).

    Issue #1337 algorithm fix migration. Path 3 sub-lemma. -/
theorem qHat_in_range_under_runtime_v2 (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hbltu : isCallTrialN4Evm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (_hborrow : isAddbackBorrowN4CallEvm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot_v2 u4 u3 b3'
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                  val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    q_true + 1 ≤ qHat.toNat ∧ qHat.toNat ≤ q_true + 2 := by
  sorry  -- Decomposition target:
         --   - Upper: invoke `div128Quot_v2_le_val256_div_plus_two_untruncated`
         --     after discharging the no_wrap_untruncated stub.
         --   - Lower: from `hborrow` (uTop borrows from u4-c3 means qHat*b > a),
         --     use contrapositive of `c3_un_zero_of_qHat_mul_le` — c3 ≠ 0 ⟹
         --     qHat * val256(b) > val256(a) ⟹ qHat > a/b = q_true.
         --     Combined with `EvmWord.u_top_lt_c3_of_addback_borrow_call`
         --     (which extracts c3 ≠ 0 from hborrow for V1's qHat), this would
         --     give qHat ≥ q_true + 1 — BUT v1's lemma uses `div128Quot`, not
         --     `div128Quot_v2`. **MIGRATION CAVEAT:** the v2 closure proof's
         --     `hborrow` is v1-style (`isAddbackBorrowN4CallEvm`), but inside
         --     the predicate v2 uses `div128Quot_v2`. We need either:
         --     (a) prove `isAddbackBorrowN4CallEvm a b ↔ isAddbackBorrowN4CallEvm_v2 a b`
         --         on runtime-reachable inputs, OR
         --     (b) define and use v2-specific borrow predicates throughout.
         --     This precondition mismatch is a deeper architectural concern
         --     for the full v2 migration.

/-- **Carry partition for the BEQ branch (sub-lemma, conjunctive form).**
    Under runtime preconditions (`hbltu, hcarry2_nz, hborrow`), the
    algorithm's `addbackN4_carry` precisely encodes the qHat overshoot:
    - carry = 0 ⟺ qHat = q_true + 2 (double-addback).
    - carry ≠ 0 ⟺ qHat = q_true + 1 (single-addback).

    Both directions are needed: for `qHat_eq_*_of_*_addback_v2`, we
    use the forward implication of each iff (carry condition → qHat
    overshoot value).

    Closing this requires Knuth-D's classical addback correctness:
    each addback adds `b` back to the partial remainder, so the number
    of addbacks fired equals `qHat - q_true` (precise overshoot).

    Issue #1337 algorithm fix migration. Alternative path 3 sub-lemma. -/
theorem addback_carry_partition_v2 (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hbltu : isCallTrialN4Evm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (_hborrow : isAddbackBorrowN4CallEvm a b) :
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
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                  val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    -- Both directions of the partition:
    (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' = 0 →
     qHat.toNat = q_true + 2) ∧
    (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0 →
     qHat.toNat = q_true + 1) := by
  sorry  -- Conjunctive partition via Knuth-D's classical addback correctness.
         --
         -- **PROOF PLAN — concrete dependencies:**
         -- For carry = 0 case (qHat = q_true + 2):
         --   Use `c3_eq_u4_plus_one_from_double_mulsub_addback_bounds`
         --   (line ~2240) which gives c3 = u4 + 1 from the double-addback
         --   identity `ab' + 2^256 = ms + 2 * (b * 2^s)`.
         --   Combined with `qHat = a/b + 2` (from `_le_val256_div_plus_two_untruncated`)
         --   and the carry semantics, derive qHat = q_true + 2.
         --
         -- For carry ≠ 0 case (qHat = q_true + 1):
         --   Use `c3_eq_u4_plus_one_from_mulsub_addback_bounds` (line ~2172)
         --   which gives c3 = u4 + 1 from the single-addback identity
         --   `post1_val + 2^256 = ms + b * 2^s`.
         --   Combined with `qHat ≤ a/b + 2` (Knuth-B v2 untruncated) and
         --   `qHat > q_true` (BEQ branch reached) → qHat ∈ {q_true + 1, q_true + 2};
         --   exclude qHat = q_true + 2 via the carry ≠ 0 hypothesis (which
         --   would require double-addback).
         --
         -- Both branches need:
         --   - Knuth-A (lower): qHat ≥ a/b. Trivially true.
         --   - Knuth-B v2 (upper): via `_le_val256_div_plus_two_untruncated`.
         --   - Mulsub ↔ qHat * b - a relation: existing helpers.
         --   - addbackN4 ↔ +b * 2^s relation: existing helpers.
         -- Closing this requires:
         --   - Knuth-A (lower bound): qHat ≥ q_true.
         --   - Knuth-B v2 untruncated chain: qHat ≤ q_true + 2.
         --   - Mulsub correctness: ms encodes (q_true * b - a) mod 2^256
         --     when qHat is overshooting.
         --   - Addback correctness: each addback adds b back, so 2
         --     addbacks recover the true remainder iff qHat overshot by 2.

/-- **Single-addback case for v2**: under v2's Knuth-B + runtime BEQ
    preconditions + carry ≠ 0 (= single-addback), `qHat = q_true + 1`.

    **Path 3 chain** (closure via the new untruncated lemmas):
    1. `div128Quot_v2_no_wrap_under_call_addback_beq_untruncated` (stub)
       — derive untruncated phase-1 + phase-2 invariants from runtime.
    2. `div128Quot_v2_le_val256_div_plus_two_untruncated` (proven)
       — qHat ≤ q_true + 2 (Knuth-B upper).
    3. `addback_carry_eq_zero_iff_qHat_overshoot_two_v2` (stub) +
       carry ≠ 0 → qHat ∈ {q_true, q_true + 1}.
    4. Runtime forces qHat ≥ q_true + 1 (BEQ branch reached).
    5. Combine 3+4: qHat = q_true + 1.

    Issue #1337 algorithm fix migration. -/
theorem qHat_eq_div_plus_one_of_single_addback_v2 (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hcarry_nz :
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
      let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
      addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (div128Quot_v2 u4 u3 b3').toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 1 := by
  -- Direct via the carry partition (conjunctive form, carry ≠ 0 case).
  have h_part := addback_carry_partition_v2 a b
    hb3nz hshift_nz hbltu hcarry2_nz hborrow
  exact h_part.2 hcarry_nz

/-- **Double-addback case for v2**: under v2's Knuth-B + runtime BEQ
    preconditions + carry = 0 (= double-addback), `qHat = q_true + 2`.

    Combined with the v2 Knuth-B bound `qHat ≤ q_true + 2`:
    - carry = 0 implies qHat ≥ q_true + 2 (otherwise single-addback would
      have produced carry ≠ 0).
    - Combined with Knuth-B upper bound, qHat = q_true + 2.

    This is the v2 mirror of `qHat_eq_div_plus_one_of_single_addback`
    but for the double-addback (carry = 0) branch. v1's analog couldn't
    exist because v1's qHat could overshoot by 2^32-2 (per
    `n4CallAddbackBeqSemanticHolds_counterexample`).

    **Migration TODO (post-path-3 closure):** the runtime hypotheses
    here use v1 predicates (`isAddbackBorrowN4CallEvm`,
    `isAddbackCarry2NzN4CallEvm`) but inside the predicate, v2's
    `div128Quot_v2` is used. For full architectural soundness, switch
    the v2 chain theorems' hypotheses to v2-style:
    - `isAddbackBorrowN4CallEvm_v2`
    - `isAddbackCarry2NzN4CallEvm_v2`
    These were added in commits 82d668e8..5f1e2001. The
    `u_top_lt_c3_of_addback_borrow_call_v2` lemma (cdcc8a95) is the
    bridge from `hborrow_v2` to the c3 ≠ 0 fact needed in the closure.

    Issue #1337 algorithm fix migration. -/
theorem qHat_eq_div_plus_two_of_double_addback_v2 (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hcarry_zero :
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
      let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
      addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' = 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (div128Quot_v2 u4 u3 b3').toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2 := by
  -- Direct via the carry partition (conjunctive form, carry = 0 case).
  have h_part := addback_carry_partition_v2 a b
    hb3nz hshift_nz hbltu hcarry2_nz hborrow
  exact h_part.1 hcarry_zero
         -- 2. carry = 0 ⟹ qHat ≥ q_true + 2 (the addback's correctness:
         --    if qHat were q_true or q_true + 1, the post-addback partial
         --    remainder would not have triggered double-addback).
         -- 3. Combine to get qHat = q_true + 2.

/-- **Carry partition for the BEQ branch**: under runtime preconditions
    `hcarry2_nz ∧ hborrow` (the double-addback indicators), and given the
    Knuth-B bound `qHat ≤ q_true + 2`, the algorithm's carry from the outer
    addback is 0 iff `qHat = q_true + 2`.

    Combined with the post-addback formula `q_out = qHat - 2` when carry = 0,
    this gives `q_out = q_true`. When carry ≠ 0, `q_out = qHat - 1` and
    `qHat = q_true + 1`, so still `q_out = q_true`.

    This is the Knuth-style D6 addback step's correctness for v2:
    - Single-addback (carry ≠ 0): qHat overshoots by exactly 1.
    - Double-addback (carry = 0): qHat overshoots by exactly 2.
    - In both cases, q_out = q_true after the addback correction.

    **Path 3 chain assembly (commits 61b41296, 20f2fe01, 3ab6cc57, 594ab2a1):**
    The closure now reduces (modulo 2 stubs) to:
    1. `addback_carry_partition_v2` (stub) — biconditional linking carry
       signal to qHat overshoot value.
    2. The `qHat_eq_div_plus_*_v2` lemmas, which directly invoke
       partition.{1,2}.

    The Knuth-B v2 chain `qHat ≤ q_true + 2` is fully assembled via
    `div128Quot_v2_le_val256_div_plus_two_untruncated` (PROVEN), but it
    requires the runtime discharge stub
    `div128Quot_v2_no_wrap_under_call_addback_beq_untruncated`
    (provably TRUE per untruncated counterexample test).

    Issue #1337 algorithm fix migration. -/
theorem n4CallAddbackBeq_q_out_eq_q_true_v2 (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    n4CallAddbackBeqSemanticHolds_v2 a b := by
  unfold n4CallAddbackBeqSemanticHolds_v2
  -- Peel the let-chain into local context (matching v1's intro pattern,
  -- e.g. `qHat_eq_div_plus_one_of_single_addback`).
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms carry
  -- Goal: let q_out := if carry = 0 then ... else ...; q_out.toNat = q_true_expr.
  -- Case-split on the locally-named `carry`.
  by_cases h_carry : carry = 0
  · -- carry = 0: double-addback case. q_out = qHat - 2.
    simp only [if_pos h_carry]
    have h_qHat' := qHat_eq_div_plus_two_of_double_addback_v2 a b
      hb3nz hshift_nz hbltu hcarry2_nz hborrow h_carry
    -- Abstract the division as q_true so omega sees a clean constant offset.
    set q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                  val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
                  with hq_true_def
    have h_qHat : qHat.toNat = q_true + 2 := h_qHat'
    have hqHat_ge_2 : qHat.toNat ≥ 2 := by linarith [h_qHat]
    rw [BitVec.toNat_add, BitVec.toNat_add, signExtend12_4095_toNat]
    have hq_lt : qHat.toNat < 2^64 := qHat.isLt
    have h_inner : (qHat.toNat + (2^64 - 1)) % 2^64 = qHat.toNat - 1 := by
      have : qHat.toNat + (2^64 - 1) = (qHat.toNat - 1) + 2^64 := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : qHat.toNat - 1 < 2^64)]
    rw [h_inner]
    have h_outer : (qHat.toNat - 1 + (2^64 - 1)) % 2^64 = qHat.toNat - 2 := by
      have : qHat.toNat - 1 + (2^64 - 1) = (qHat.toNat - 2) + 2^64 := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : qHat.toNat - 2 < 2^64)]
    rw [h_outer]
    omega
  · -- carry ≠ 0: single-addback case. q_out = qHat - 1.
    simp only [if_neg h_carry]
    have h_qHat' := qHat_eq_div_plus_one_of_single_addback_v2 a b
      hb3nz hshift_nz hbltu hcarry2_nz hborrow h_carry
    set q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                  val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
                  with hq_true_def
    have h_qHat : qHat.toNat = q_true + 1 := h_qHat'
    have hqHat_ge_1 : qHat.toNat ≥ 1 := by linarith [h_qHat]
    rw [BitVec.toNat_add, signExtend12_4095_toNat]
    have h_eq : qHat.toNat + (2^64 - 1) = (qHat.toNat - 1) + 2^64 := by omega
    rw [h_eq, Nat.add_mod_right]
    have hq_lt : qHat.toNat - 1 < 2^64 := by have := qHat.isLt; omega
    rw [Nat.mod_eq_of_lt hq_lt]
    omega

/-- **Closure of `n4CallAddbackBeqSemanticHolds_v2` from runtime conditions.**

    Direct alias for `n4CallAddbackBeq_q_out_eq_q_true_v2` — the user-facing
    form mirroring `n4CallSkipSemanticHolds_of_call_trial` for the
    call+addback BEQ branch.

    Issue #1337 algorithm fix migration. -/
theorem n4CallAddbackBeqSemanticHolds_v2_of_call_addback_beq (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    n4CallAddbackBeqSemanticHolds_v2 a b :=
  n4CallAddbackBeq_q_out_eq_q_true_v2 a b hb3nz hshift_nz hbltu hcarry2_nz hborrow

-- ============================================================================
-- Numerical sanity checks on the v2 stubs (counterexample + variants).
-- These do NOT prove the stubs but verify the statements are at least
-- consistent on concrete witnesses, including the input that breaks v1.
-- ============================================================================

/-- **Sanity check 1**: `div128Quot_v2_le_val256_div_plus_two`'s bound holds
    on the counterexample input (the same (a, b) where v1's `div128Quot`
    overshoots by 2^32-2). Kernel-checked via `decide`. -/
theorem div128Quot_v2_le_val256_div_plus_two_test_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    (div128Quot_v2 u4 un3 b3').toNat ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2 := by
  decide

/-- **Sanity check 2**: by contrast, the buggy v1 `div128Quot` VIOLATES
    the same bound on the same input (overshoots by 2^32-2 ≫ 2). This
    is the underlying motivation for the v2 fix. Kernel-checked via `decide`. -/
theorem div128Quot_v1_violates_knuth_B_on_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    ¬ ((div128Quot u4 un3 b3').toNat ≤
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2) := by
  decide

/-- **Sanity check 3**: `div128Quot_v2_le_val256_div_plus_two` bound holds
    on a "small" test input where both v1 and v2 should agree. Verifies
    the bound isn't trivially false on common cases. Kernel-checked via `decide`. -/
theorem div128Quot_v2_le_val256_div_plus_two_test_small :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 5 | 3 => BitVec.ofNat 64 (2^60))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^32 + 7))
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    (div128Quot_v2 u4 un3 b3').toNat ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2 := by
  decide

/-- **Sanity check 5**: `addback_carry_partition_v2`'s claim on the
    counterexample input. v2 returns `qHat = q_true + 1` on this input
    (per `n4CallAddbackBeqSemanticHolds_v2_holds_on_counterexample`), so
    the partition's claim is: `carry ≠ 0` (single-addback case).

    Kernel-checked validation that the partition's stated form is at
    least correct on the canonical counterexample. -/
theorem addback_carry_partition_v2_test_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
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
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0 := by
  decide

/-- **Sanity check 6**: on the v1 counterexample input, both v1 and v2
    borrow predicates fire (kernel-checked via `decide`).

    This is preliminary evidence that on this specific input, the v1
    and v2 borrow predicates agree. A full equivalence theorem would be
    needed to use v1's `hborrow` lemmas in the v2 closure proof — this
    test just suggests it's not refuted on the worst-known case. -/
theorem isAddbackBorrowN4Call_v1_v2_agree_on_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    isAddbackBorrowN4CallEvm a b ↔ isAddbackBorrowN4CallEvm_v2 a b := by
  unfold isAddbackBorrowN4CallEvm isAddbackBorrowN4CallEvm_v2
         isAddbackBorrowN4Call isAddbackBorrowN4Call_v2
  decide

/-- **Sanity check 4**: NOTE — `n4CallAddbackBeqSemanticHolds_v2` requires
    the input to actually be in the call+addback BEQ runtime regime (i.e.
    the runtime preconditions of the closure stub: `hbltu`, `hcarry2_nz`,
    `hborrow`). On arbitrary inputs the predicate doesn't hold — the closure
    only asserts conditional correctness. The counterexample
    (`...holds_on_counterexample` above) was specifically constructed to be
    in the BEQ regime, which is why it's the right witness. -/

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
    (hvalid : ValidMemRange sp 8)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  have h_pre := evm_div_n4_full_call_addback_beq_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz hvalid halign hbltu hcarry2_nz hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_addback_beq_div_mod_getLimbN a b hbnz hsem
  refine cpsTriple_weaken (fun _ hp => hp) ?_ h_pre
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

/-- **Sub-stub (single-addback): qHat.toNat = a/b + 1.** Under
    `n4CallAddbackBeqSemanticHolds` and the single-addback condition (i.e.
    first-addback carry ≠ 0, equivalent to `q_out = qHat - 1`), the trial
    quotient overestimates by exactly 1. Direct corollary of hsem (which
    pins q_out.toNat = a/b) plus q_out = qHat - 1 in this branch.

    Once filled, this sub-lemma + `mulsubN4_c3_le_one` give c3 ≤ 1 in the
    single-addback branch, which is the missing piece for the addback-BEQ
    MOD adapter's single-addback closure. -/
theorem qHat_eq_div_plus_one_of_single_addback (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
                 let antiShift :=
                   (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
                 let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
                 let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
                 let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
                 let b0' := (b.getLimbN 0) <<< shift
                 let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
                 let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
                 let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
                 let u0 := (a.getLimbN 0) <<< shift
                 let u4 := (a.getLimbN 3) >>> antiShift
                 let qHat := div128Quot u4 u3 b3'
                 let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
                 addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    (div128Quot u4 u3 b3').toNat = a.toNat / b.toNat + 1 := by
  intro shift antiShift b3' u3 u4
  rw [n4CallAddbackBeqSemanticHolds_def] at hsem
  -- Unfold the if in hsem using hcarry_nz.
  simp only [if_neg hcarry_nz] at hsem
  -- val256(a_limbs) = a.toNat, val256(b_limbs) = b.toNat.
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
  -- hsem : (qHat + signExtend12 4095).toNat = a.toNat / b.toNat
  -- Rewrite the LHS via BitVec.toNat_add + signExtend12_4095_toNat.
  rw [BitVec.toNat_add, signExtend12_4095_toNat] at hsem
  -- hsem : (qHat.toNat + (2^64 - 1)) % 2^64 = a.toNat / b.toNat
  set qHat := div128Quot u4 u3 b3' with hqHat_def
  have h_div_lt : a.toNat / b.toNat < 2^64 := by
    have := a.isLt; have := b.isLt
    -- Dividing by anything ≥ 1 keeps result < 2^256. But we need < 2^64.
    -- Use that hsem already pins (qHat + (-1)).toNat (which is < 2^64) = a/b.
    -- Since LHS < 2^64 (it's a Word toNat after addition), a/b < 2^64.
    have h_lhs_lt : ((qHat.toNat + (2^64 - 1)) % 2^64) < 2^64 := Nat.mod_lt _ (by decide)
    omega
  have hqHat_pos : qHat.toNat ≥ 1 := by
    -- From hborrow: c3 ≠ 0 (specifically u4 < c3 ≥ 1).
    -- Contrapositive of `c3_un_zero_of_qHat_mul_le`: c3 ≠ 0 → qHat * b > a.
    -- If qHat = 0, then 0 * b = 0 ≤ a, contradicting qHat * b > a.
    by_contra hqHat_zero
    push Not at hqHat_zero
    -- hqHat_zero : qHat.toNat < 1, i.e., qHat.toNat = 0.
    have hqHat_eq_zero : qHat.toNat = 0 := by omega
    -- Then qHat * b = 0 ≤ a, so c3 = 0 by `c3_un_zero_of_qHat_mul_le`.
    have h_mul_le : qHat.toNat *
        val256 ((b.getLimbN 0) <<< shift)
              (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> (64 - shift)))
              (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> (64 - shift)))
              (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> (64 - shift)))
        ≤ val256 ((a.getLimbN 0) <<< shift)
              (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> (64 - shift)))
              (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> (64 - shift)))
              (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> (64 - shift))) := by
      rw [hqHat_eq_zero, Nat.zero_mul]; exact Nat.zero_le _
    have h_c3_zero := c3_un_zero_of_qHat_mul_le h_mul_le
    -- But hborrow gives u4 < c3, hence c3 ≥ 1 ≠ 0.
    rw [isAddbackBorrowN4CallEvm_def] at hborrow
    have h_u4_lt_c3 := EvmWord.u_top_lt_c3_of_addback_borrow_call
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        hborrow
    -- shift in `_call` form uses the un-modded clzResult; reconcile via rfl/match.
    -- The c3 in h_c3_zero matches the c3 in h_u4_lt_c3 (same shift mod 64).
    simp only [] at h_u4_lt_c3
    -- Goal: False. From h_c3_zero (c3 = 0) and h_u4_lt_c3 (u4 < c3.toNat),
    -- we have u4 < 0, contradiction.
    have h_c3_toNat_zero : (mulsubN4 qHat
        ((b.getLimbN 0) <<< shift)
        (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> (64 - shift)))
        (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> (64 - shift)))
        (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> (64 - shift)))
        ((a.getLimbN 0) <<< shift)
        (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> (64 - shift)))
        (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> (64 - shift)))
        (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> (64 - shift)))).2.2.2.2.toNat = 0 := by
      rw [h_c3_zero]; rfl
    -- Bridge: convert h_u4_lt_c3's Word form to match h_c3_toNat_zero's Nat form.
    -- Use `antiShift_toNat_mod_eq` to rewrite `(signExtend12 0 - clz).toNat % 64`
    -- to `64 - clz.toNat`. Then `(64 - clz.toNat) = (64 - shift)` via
    -- `shift = clz.toNat % 64 = clz.toNat` when clz.toNat ≤ 63.
    have h_clz_le : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
      clzResult_fst_toNat_le _
    have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
      rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
      · exfalso; apply hshift_nz
        exact BitVec.eq_of_toNat_eq (by simp [h0])
      · exact h0
    have h_anti_eq : (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
        = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
      antiShift_toNat_mod_eq h_clz_pos h_clz_le
    have h_shift_eq : shift = (clzResult (b.getLimbN 3)).1.toNat := by
      show (clzResult (b.getLimbN 3)).1.toNat % 64 = (clzResult (b.getLimbN 3)).1.toNat
      omega
    -- Now h_u4_lt_c3 has antiShift in Word form, but h_anti_eq + h_shift_eq give
    -- it equals our local `64 - shift`. After rewriting, the mulsubN4 invocations
    -- in h_u4_lt_c3 and h_c3_toNat_zero have identical arguments, contradiction.
    rw [h_anti_eq] at h_u4_lt_c3
    rw [show (clzResult (b.getLimbN 3)).1.toNat % 64 = (clzResult (b.getLimbN 3)).1.toNat
        from by omega] at h_u4_lt_c3
    -- Unfold qHat/u4/u3/b3'/shift/antiShift in h_c3_toNat_zero to match h_u4_lt_c3's
    -- fully-inlined form, then omega closes via c3 = 0 ∧ u4.toNat < c3.toNat.
    have h_anti_unfold : antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat := h_anti_eq
    rw [hqHat_def,
        show u4 = a.getLimbN 3 >>> antiShift from rfl,
        show u3 = a.getLimbN 3 <<< shift ||| a.getLimbN 2 >>> antiShift from rfl,
        show b3' = b.getLimbN 3 <<< shift ||| b.getLimbN 2 >>> antiShift from rfl,
        h_shift_eq, h_anti_unfold] at h_c3_toNat_zero
    omega
  -- (qHat.toNat + 2^64 - 1) % 2^64 = qHat.toNat - 1 when qHat ≥ 1.
  have h_qHat_lt : qHat.toNat < 2^64 := qHat.isLt
  have : (qHat.toNat + (2^64 - 1)) % 2^64 = qHat.toNat - 1 := by
    rw [show qHat.toNat + (2^64 - 1) = (qHat.toNat - 1) + 2^64 from by omega]
    rw [Nat.add_mod_right]
    apply Nat.mod_eq_of_lt; omega
  rw [this] at hsem
  -- hsem : qHat.toNat - 1 = a.toNat / b.toNat
  omega

/-- **Pure-Nat algebraic identity: post1_low4 + (u4 + 1)*2^256 = a%b*2^s + c3*2^256.**

    Combines the mulsub Euclidean, addback Euclidean, val256 normalization
    identities, and qHat = a/b + 1 into a single Nat equation. Avoids Nat
    subtraction by rearranging.

    From this identity + bound `post1_low4 < 2^256` + `c3 < 2^256` + the
    range of `a%b * 2^s < 2^256`, omega can derive c3 = u4 + 1 in single-
    addback. (Note: the lemma exposes the algebra; the surrounding proof
    must establish u4_lt_c3 from hborrow to pin c3 ≥ u4 + 1.) -/
theorem val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    (post1_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) = ms_val + (a_val / b_val + 1) * (b_val * 2^s))
    (h_addback : post1_val + 2^256 = ms_val + b_val * 2^s)
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s) :
    post1_val + (u4 + 1) * 2^256 = a_val % b_val * 2^s + c3 * 2^256 := by
  have h_dam_mul : a_val / b_val * b_val + a_val % b_val = a_val := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod a_val b_val
  -- Replace `a_val / b_val * b_val * 2^s` with `a_val * 2^s - a_val % b_val * 2^s`
  -- via h_dam_mul.
  have h_div_mul_pow : a_val / b_val * b_val * 2^s + a_val % b_val * 2^s = a_val * 2^s := by
    rw [← Nat.add_mul]; rw [h_dam_mul]
  have h_expand : (a_val / b_val + 1) * (b_val * 2^s) =
      a_val / b_val * b_val * 2^s + b_val * 2^s := by ring
  -- h_mulsub_simp: c3 * 2^256 + a_val % b_val * 2^s = ms_val + b_val * 2^s + u4 * 2^256.
  have h_mulsub_simp : c3 * 2^256 + a_val % b_val * 2^s =
      ms_val + b_val * 2^s + u4 * 2^256 := by
    -- Use h_mulsub + h_expand + h_div_mul_pow + h_u4_le.
    have h1 : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) =
              ms_val + (a_val / b_val * b_val * 2^s + b_val * 2^s) := by
      rw [← h_expand]; exact h_mulsub
    omega
  -- Combine with h_addback.
  omega

/-- **Pure-Nat: c3 ≤ u4 + 1 from the closed identity + bounds.**

    Direct corollary: from `post1_val + (u4 + 1)*2^256 = a%b*2^s + c3*2^256`
    plus `post1_val < 2^256` (val256 bound) and `a%b*2^s < 2^256` (a%b < b
    and b * 2^s ≤ 2^256), it follows that `c3 ≤ u4 + 1` — otherwise
    post1_val would exceed 2^256. -/
theorem c3_le_u4_plus_one_from_identity
    (post1_val a_val b_val s u4 c3 : Nat)
    (h_id : post1_val + (u4 + 1) * 2^256 = a_val % b_val * 2^s + c3 * 2^256)
    (h_post1_lt : post1_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256) :
    c3 ≤ u4 + 1 := by
  -- Suppose c3 ≥ u4 + 2. Then RHS ≥ (u4 + 2)*2^256 = (u4 + 1)*2^256 + 2^256.
  -- LHS = post1_val + (u4 + 1)*2^256 < 2^256 + (u4 + 1)*2^256.
  -- a%b*2^s ≥ 0 and a%b*2^s < 2^256, so RHS could be in
  -- [(u4 + 2)*2^256, (u4 + 2)*2^256 + 2^256). LHS bound contradicts.
  by_contra h_gt
  push Not at h_gt
  have h_c3_ge : c3 ≥ u4 + 2 := h_gt
  have h_c3_mul : c3 * 2^256 ≥ (u4 + 2) * 2^256 := Nat.mul_le_mul_right _ h_c3_ge
  have h_split : (u4 + 2) * 2^256 = (u4 + 1) * 2^256 + 2^256 := by ring
  omega

/-- **Pure-Nat: c3 = u4 + 1 from mulsub Euclidean + addback Euclidean + bounds.**

    Combined sub-stub: takes the val256-level Euclidean equations, normalization
    bounds, and `u4 < c3`, and outputs c3 = u4 + 1 directly. This is the
    pure-Nat composition of the algebraic identity, the c3 ≤ u4 + 1 bound,
    and the u4 < c3 hypothesis.

    Once the Word-level wrapper at `c3_n_eq_u4_plus_one_of_single_addback`
    is plumbed up, it just calls this. -/
theorem c3_eq_u4_plus_one_from_mulsub_addback_bounds
    (post1_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) = ms_val + (a_val / b_val + 1) * (b_val * 2^s))
    (h_addback : post1_val + 2^256 = ms_val + b_val * 2^s)
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s)
    (h_post1_lt : post1_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256)
    (h_u4_lt_c3 : u4 < c3) :
    c3 = u4 + 1 := by
  have h_id := val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    post1_val ms_val a_val b_val s u4 c3 h_mulsub h_addback h_u4_le
  have h_le := c3_le_u4_plus_one_from_identity
    post1_val a_val b_val s u4 c3 h_id h_post1_lt h_amod_pow_lt
  omega

/-- **B.3 (pure-Nat algebra for double-addback): closed identity.**

    Mirror of `val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4`
    for the **double-addback** branch. The double-addback path runs two
    `addbackN4` calls; the val256-level invariants are:
    - mulsub with qHat = a/b + 2.
    - First addback (carry₁ = 0): ab = ms + b * 2^s (no wrap).
    - Second addback (carry₂ = 1): ab' + 2^256 = ab + b * 2^s (wrap).

    Combined: `ab' + 2^256 = ms + 2 * (b * 2^s)`. Algebra below uses that
    combined form as `h_addback_combined`.

    **Algebraic surprise** (per #1338): the resulting identity is **identical**
    to single-addback's `c3 = u4 + 1` shape, despite qHat shifting from
    `a/b + 1` to `a/b + 2`. The +2's extra `b * 2^s` is absorbed by the
    second addback's `+ b * 2^s`.

    This pure-Nat lemma does NOT depend on Knuth-B (#1337). The Knuth bound
    is needed only to discharge the `(a/b + 2)` factor in `h_mulsub` (i.e.,
    Phase B.1 `qHat_eq_div_plus_two_of_double_addback`). -/
theorem val256_abPrime_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    (abPrime_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) =
                ms_val + (a_val / b_val + 2) * (b_val * 2^s))
    (h_addback_combined : abPrime_val + 2^256 = ms_val + 2 * (b_val * 2^s))
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s) :
    abPrime_val + (u4 + 1) * 2^256 = a_val % b_val * 2^s + c3 * 2^256 := by
  have h_dam_mul : a_val / b_val * b_val + a_val % b_val = a_val := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod a_val b_val
  have h_div_mul_pow : a_val / b_val * b_val * 2^s + a_val % b_val * 2^s = a_val * 2^s := by
    rw [← Nat.add_mul]; rw [h_dam_mul]
  have h_expand : (a_val / b_val + 2) * (b_val * 2^s) =
      a_val / b_val * b_val * 2^s + 2 * (b_val * 2^s) := by ring
  -- h_mulsub_simp: c3 * 2^256 + a%b * 2^s = ms_val + 2 * (b * 2^s) + u4 * 2^256.
  have h_mulsub_simp : c3 * 2^256 + a_val % b_val * 2^s =
      ms_val + 2 * (b_val * 2^s) + u4 * 2^256 := by
    have h1 : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) =
              ms_val + (a_val / b_val * b_val * 2^s + 2 * (b_val * 2^s)) := by
      rw [← h_expand]; exact h_mulsub
    omega
  -- Combine with h_addback_combined.
  omega

/-- **B.3: c3 = u4 + 1 from double-addback Euclidean + bounds** (CLOSED, pure-Nat).

    Direct mirror of `c3_eq_u4_plus_one_from_mulsub_addback_bounds` for the
    double-addback path. The closed identity from
    `val256_abPrime_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4` has
    the same shape as single-addback's; combined with
    `c3_le_u4_plus_one_from_identity` (already closed, generic) and
    `u4 < c3`, omega gives c3 = u4 + 1.

    Pure Nat. Independent of Knuth-B (#1337). -/
theorem c3_eq_u4_plus_one_from_double_mulsub_addback_bounds
    (abPrime_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) =
                ms_val + (a_val / b_val + 2) * (b_val * 2^s))
    (h_addback_combined : abPrime_val + 2^256 = ms_val + 2 * (b_val * 2^s))
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s)
    (h_abPrime_lt : abPrime_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256)
    (h_u4_lt_c3 : u4 < c3) :
    c3 = u4 + 1 := by
  have h_id := val256_abPrime_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    abPrime_val ms_val a_val b_val s u4 c3 h_mulsub h_addback_combined h_u4_le
  have h_le := c3_le_u4_plus_one_from_identity
    abPrime_val a_val b_val s u4 c3 h_id h_abPrime_lt h_amod_pow_lt
  omega

/-- **B.3: pure-Nat double-addback wrapper** (CLOSED, pure-Nat).

    Mirror of `post1_val_eq_amod_pow_s_pure_nat`. From the double-addback
    Euclidean equations + standard bounds, gives `abPrime_val = a%b * 2^s`.
    Composes:
    - `c3_eq_u4_plus_one_from_double_mulsub_addback_bounds` (above).
    - The val256-identity instantiated with c3 = u4 + 1.

    Independent of Knuth-B (#1337). The Knuth bound is needed only to
    DERIVE `h_mulsub` (with the `(a/b + 2)` factor), not for the algebra. -/
theorem abPrime_val_eq_amod_pow_s_pure_nat
    (abPrime_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) =
                ms_val + (a_val / b_val + 2) * (b_val * 2^s))
    (h_addback_combined : abPrime_val + 2^256 = ms_val + 2 * (b_val * 2^s))
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s)
    (h_abPrime_lt : abPrime_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256)
    (h_u4_lt_c3 : u4 < c3) :
    abPrime_val = a_val % b_val * 2^s := by
  have h_c3_eq := c3_eq_u4_plus_one_from_double_mulsub_addback_bounds
    abPrime_val ms_val a_val b_val s u4 c3
    h_mulsub h_addback_combined h_u4_le h_abPrime_lt h_amod_pow_lt h_u4_lt_c3
  have h_id := val256_abPrime_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    abPrime_val ms_val a_val b_val s u4 c3 h_mulsub h_addback_combined h_u4_le
  rw [h_c3_eq] at h_id
  omega

/-- **Sub-stub: addbackN4_carry returns 0 or 1.** Pure structural fact about
    `addbackN4_carry` — the output is `aco3 = ac1_3 ||| ac2_3` where each
    is 0 or 1, so `aco3 ∈ {0, 1}`. -/
theorem addbackN4_carry_le_one (un0 un1 un2 un3 v0 v1 v2 v3 : Word) :
    (addbackN4_carry un0 un1 un2 un3 v0 v1 v2 v3).toNat ≤ 1 := by
  unfold addbackN4_carry
  simp only []
  split_ifs <;> decide

/-- **Irreducible bundle: the call+addback BEQ algorithm's first-addback carry.**

    Bundles the full let-chain (shift, antiShift, b0'..b3', u0..u4, qHat, ms) into
    an opaque `Word` value. Used by callers that need to talk about the carry
    without paying the let-chain elaboration cost.

    The body uses the same `% 64` form as `n4CallAddbackBeqSemanticHolds_def`,
    so consumers get a consistent shape. Use `algCallAddbackBeqCarry_unfold`
    to expose the let-chain when needed in proofs. -/
@[irreducible]
def algCallAddbackBeqCarry (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'

/-- **Irreducible bundle: the call+addback BEQ algorithm's mulsub borrow c3.**

    Parallel to `algCallAddbackBeqCarry`. Encapsulates the deep let-chain
    needed to talk about the c3 = mulsub borrow at normalized limbs as a
    single opaque Word value, sidestepping let-chain elaboration cost. -/
@[irreducible]
def algCallAddbackBeqMsC3 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  ms.2.2.2.2

/-- **Irreducible bundle: the call+addback BEQ algorithm's u4 (overflow limb).** -/
@[irreducible]
def algCallAddbackBeqU4 (a b : EvmWord) : Word :=
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  (a.getLimbN 3) >>> antiShift

/-- Unfolding lemma for `algCallAddbackBeqCarry`. -/
theorem algCallAddbackBeqCarry_unfold {a b : EvmWord} :
    algCallAddbackBeqCarry a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3') := by
  show algCallAddbackBeqCarry a b = _
  unfold algCallAddbackBeqCarry
  rfl

/-- **Irreducible bundle: val256 of post1 limbs at normalized inputs.**

    Captures the val256 of the 4 low outputs of `addbackN4 ms.1 ms.2.1
    ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'` (i.e., the first-addback result
    at carry-input 0). When the first-addback carry is 1 (single-addback
    branch), this Nat value is exactly `val256(a)%val256(b) * 2^s` per
    `post1_val_eq_amod_pow_s_pure_nat`.

    Encapsulates the deep let-chain so consumers can talk about the
    addback post1 val256 as a single opaque Nat, sidestepping the
    elaboration-cost penalty observed in the parent adapter. -/
@[irreducible]
def algCallAddbackBeqPost1Val (a b : EvmWord) : Nat :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let post1 := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1

/-- Unfolding lemma for `algCallAddbackBeqPost1Val`. -/
theorem algCallAddbackBeqPost1Val_unfold {a b : EvmWord} :
    algCallAddbackBeqPost1Val a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let post1 := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
     val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1) := by
  show algCallAddbackBeqPost1Val a b = _
  unfold algCallAddbackBeqPost1Val
  rfl

/-- **Irreducible bundles: per-limb post1 outputs at normalized inputs.**

    4 individual Word-valued bundles capturing the low 4 outputs of
    `addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'` — same
    expression as `algCallAddbackBeqPost1Val`'s underlying val256. Used
    to keep the goal manageable when reasoning per-limb (avoids huge
    inline `mulsubN4 ...` expressions). -/
@[irreducible]
def algCallAddbackBeqPost1Limb0 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').1

@[irreducible]
def algCallAddbackBeqPost1Limb1 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.1

@[irreducible]
def algCallAddbackBeqPost1Limb2 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.1

@[irreducible]
def algCallAddbackBeqPost1Limb3 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.2.1

/-- **Packaging: `algCallAddbackBeqPost1Val = val256 of irreducible limbs`** (CLOSED).

    Bridges the val256-level `algCallAddbackBeqPost1Val` to the per-limb
    irreducible bundles. By definition both unfold to the same thing —
    proof is rfl after unfolding both sides. Useful when applying
    `denorm_4limb_eq_mod_of_val256_eq_amod_pow_s` with the irreducible
    Limb0..Limb3 as X1..X4: the goal stays small. -/
theorem algCallAddbackBeqPost1Val_eq_val256_limbs (a b : EvmWord) :
    algCallAddbackBeqPost1Val a b =
    val256 (algCallAddbackBeqPost1Limb0 a b)
           (algCallAddbackBeqPost1Limb1 a b)
           (algCallAddbackBeqPost1Limb2 a b)
           (algCallAddbackBeqPost1Limb3 a b) := by
  unfold algCallAddbackBeqPost1Val
    algCallAddbackBeqPost1Limb0 algCallAddbackBeqPost1Limb1
    algCallAddbackBeqPost1Limb2 algCallAddbackBeqPost1Limb3
  rfl

/-- **Irreducible bundles: per-limb un{i}Out (the if-then-else outputs).**

    These are the parent adapter's per-limb output values: `un{i}Out :=
    if carry = 0 then ab'.{i_low} else ab.{i_low}`. Wrapping them as
    irreducible defs keeps the parent's goal manageable. -/
@[irreducible]
def algCallAddbackBeqUn0Out (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  if carry = 0 then ab'.1 else ab.1

@[irreducible]
def algCallAddbackBeqUn1Out (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  if carry = 0 then ab'.2.1 else ab.2.1

@[irreducible]
def algCallAddbackBeqUn2Out (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  if carry = 0 then ab'.2.2.1 else ab.2.2.1

@[irreducible]
def algCallAddbackBeqUn3Out (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1

/-- Unfolding lemmas for un{i}Out irreducibles (used by the parent to fold). -/
theorem algCallAddbackBeqUn0Out_unfold {a b : EvmWord} :
    algCallAddbackBeqUn0Out a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     if carry = 0 then ab'.1 else ab.1) := by
  show algCallAddbackBeqUn0Out a b = _; unfold algCallAddbackBeqUn0Out; rfl

theorem algCallAddbackBeqUn1Out_unfold {a b : EvmWord} :
    algCallAddbackBeqUn1Out a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     if carry = 0 then ab'.2.1 else ab.2.1) := by
  show algCallAddbackBeqUn1Out a b = _; unfold algCallAddbackBeqUn1Out; rfl

theorem algCallAddbackBeqUn2Out_unfold {a b : EvmWord} :
    algCallAddbackBeqUn2Out a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     if carry = 0 then ab'.2.2.1 else ab.2.2.1) := by
  show algCallAddbackBeqUn2Out a b = _; unfold algCallAddbackBeqUn2Out; rfl

theorem algCallAddbackBeqUn3Out_unfold {a b : EvmWord} :
    algCallAddbackBeqUn3Out a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1) := by
  show algCallAddbackBeqUn3Out a b = _; unfold algCallAddbackBeqUn3Out; rfl

/-- **Bridge: `algCallAddbackBeqUn0Out = algCallAddbackBeqPost1Limb0` in single-addback** (CLOSED). -/
theorem algCallAddbackBeqUn0Out_eq_post1Limb0_of_single_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqUn0Out a b = algCallAddbackBeqPost1Limb0 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn0Out algCallAddbackBeqPost1Limb0
  simp only []
  rw [if_neg hcarry]
  -- Now LHS = ab.1, RHS = post1.1 (with input 0). Equal via low-4-indep.
  rfl

theorem algCallAddbackBeqUn1Out_eq_post1Limb1_of_single_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqUn1Out a b = algCallAddbackBeqPost1Limb1 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn1Out algCallAddbackBeqPost1Limb1
  simp only []
  rw [if_neg hcarry]
  rfl

theorem algCallAddbackBeqUn2Out_eq_post1Limb2_of_single_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqUn2Out a b = algCallAddbackBeqPost1Limb2 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn2Out algCallAddbackBeqPost1Limb2
  simp only []
  rw [if_neg hcarry]
  rfl

theorem algCallAddbackBeqUn3Out_eq_post1Limb3_of_single_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqUn3Out a b = algCallAddbackBeqPost1Limb3 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn3Out algCallAddbackBeqPost1Limb3
  simp only []
  rw [if_neg hcarry]
  rfl

/-- **Irreducible bundles: per-limb second-addback (ab') outputs.**

    Mirror of `algCallAddbackBeqPost1Limb{i}` for the **double-addback**
    branch (carry = 0): wraps the second `addbackN4` call's per-limb low
    outputs (ab'.{i_low}). Used to keep the double-addback parent goal
    manageable when reasoning per-limb.

    Issue #1338 (Phase B.4 mechanical infrastructure).  -/
@[irreducible]
def algCallAddbackBeqAbPrimeLimb0 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').1

@[irreducible]
def algCallAddbackBeqAbPrimeLimb1 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.1

@[irreducible]
def algCallAddbackBeqAbPrimeLimb2 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.1

@[irreducible]
def algCallAddbackBeqAbPrimeLimb3 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.2.1

/-- **Bridge: Un{i}Out = AbPrimeLimb{i} in double-addback** (Phase B.6, CLOSED).

    When the first addback's carry is zero, the algorithm runs a second
    addback. This bridge folds the parent's `un{i}Out` to the irreducible
    `AbPrimeLimb{i}` form. Issue #1338. -/
theorem algCallAddbackBeqUn0Out_eq_abPrimeLimb0_of_double_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqUn0Out a b = algCallAddbackBeqAbPrimeLimb0 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn0Out algCallAddbackBeqAbPrimeLimb0
  simp only []
  rw [if_pos hcarry]

theorem algCallAddbackBeqUn1Out_eq_abPrimeLimb1_of_double_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqUn1Out a b = algCallAddbackBeqAbPrimeLimb1 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn1Out algCallAddbackBeqAbPrimeLimb1
  simp only []
  rw [if_pos hcarry]

theorem algCallAddbackBeqUn2Out_eq_abPrimeLimb2_of_double_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqUn2Out a b = algCallAddbackBeqAbPrimeLimb2 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn2Out algCallAddbackBeqAbPrimeLimb2
  simp only []
  rw [if_pos hcarry]

theorem algCallAddbackBeqUn3Out_eq_abPrimeLimb3_of_double_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqUn3Out a b = algCallAddbackBeqAbPrimeLimb3 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn3Out algCallAddbackBeqAbPrimeLimb3
  simp only []
  rw [if_pos hcarry]

/-- **Irreducible bundle: val256 of ab' (second-addback) limbs at normalized inputs.**

    Captures the val256 of the 4 low outputs of the **second** addback
    `addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'`,
    which fires in the double-addback branch (carry = 0).

    Mirrors `algCallAddbackBeqPost1Val` for the double-addback path. The
    Word-level wrapper `algCallAddbackBeqAbPrimeVal_eq_amod_pow_s_of_double_addback`
    (Phase B.5, blocked on Knuth-B #1337) will tie this Nat to
    `val256(a) % val256(b) * 2^s` via the c3 = 1 derivation.

    Issue #1338 (Phase B.4 mechanical infrastructure). -/
@[irreducible]
def algCallAddbackBeqAbPrimeVal (a b : EvmWord) : Nat :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let abPrime := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  val256 abPrime.1 abPrime.2.1 abPrime.2.2.1 abPrime.2.2.2.1

/-- Unfolding lemma for `algCallAddbackBeqAbPrimeVal`. -/
theorem algCallAddbackBeqAbPrimeVal_unfold {a b : EvmWord} :
    algCallAddbackBeqAbPrimeVal a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     let abPrime := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
     val256 abPrime.1 abPrime.2.1 abPrime.2.2.1 abPrime.2.2.2.1) := by
  show algCallAddbackBeqAbPrimeVal a b = _
  unfold algCallAddbackBeqAbPrimeVal
  rfl

/-- **Packaging: `algCallAddbackBeqAbPrimeVal = val256 of irreducible AbPrimeLimb`** (CLOSED).

    Mirrors `algCallAddbackBeqPost1Val_eq_val256_limbs` for the double-
    addback path. By definition both unfold to the same val256 expression
    over the second-addback's low 4 outputs. Used when applying
    `denorm_4limb_eq_mod_of_val256_eq_amod_pow_s` with the irreducible
    AbPrimeLimb0..AbPrimeLimb3 limbs as X1..X4 (keeps the goal small). -/
theorem algCallAddbackBeqAbPrimeVal_eq_val256_limbs (a b : EvmWord) :
    algCallAddbackBeqAbPrimeVal a b =
    val256 (algCallAddbackBeqAbPrimeLimb0 a b)
           (algCallAddbackBeqAbPrimeLimb1 a b)
           (algCallAddbackBeqAbPrimeLimb2 a b)
           (algCallAddbackBeqAbPrimeLimb3 a b) := by
  unfold algCallAddbackBeqAbPrimeVal
    algCallAddbackBeqAbPrimeLimb0 algCallAddbackBeqAbPrimeLimb1
    algCallAddbackBeqAbPrimeLimb2 algCallAddbackBeqAbPrimeLimb3
  rfl

/-- **Bridge: `algCallAddbackBeqPost1Limb0` in parent-friendly `(64 - s)` form** (CLOSED). -/
theorem algCallAddbackBeqPost1Limb0_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqPost1Limb0 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').1) := by
  show algCallAddbackBeqPost1Limb0 a b = _
  unfold algCallAddbackBeqPost1Limb0
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridge: `algCallAddbackBeqPost1Limb1` in parent-friendly `(64 - s)` form** (CLOSED). -/
theorem algCallAddbackBeqPost1Limb1_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqPost1Limb1 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.1) := by
  show algCallAddbackBeqPost1Limb1 a b = _
  unfold algCallAddbackBeqPost1Limb1
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridge: `algCallAddbackBeqPost1Limb2` in parent-friendly `(64 - s)` form** (CLOSED). -/
theorem algCallAddbackBeqPost1Limb2_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqPost1Limb2 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.1) := by
  show algCallAddbackBeqPost1Limb2 a b = _
  unfold algCallAddbackBeqPost1Limb2
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridge: `algCallAddbackBeqPost1Limb3` in parent-friendly `(64 - s)` form** (CLOSED). -/
theorem algCallAddbackBeqPost1Limb3_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqPost1Limb3 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.2.1) := by
  show algCallAddbackBeqPost1Limb3 a b = _
  unfold algCallAddbackBeqPost1Limb3
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridges: `algCallAddbackBeqAbPrimeLimb{i}` in parent-friendly `(64 - s)`
    form** (Phase B.4 mechanical, CLOSED).

    Mirror of `algCallAddbackBeqPost1Limb{i}_eq_parent_64ms_form` for the
    double-addback's second-addback per-limb output. Same `simp_only`
    proof pattern: rewrite the antiShift to `64 - s` and the `s % 64`
    to `s`, both under `hshift_nz`.

    Issue #1338. -/
theorem algCallAddbackBeqAbPrimeLimb0_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqAbPrimeLimb0 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').1) := by
  show algCallAddbackBeqAbPrimeLimb0 a b = _
  unfold algCallAddbackBeqAbPrimeLimb0
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

theorem algCallAddbackBeqAbPrimeLimb1_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqAbPrimeLimb1 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.1) := by
  show algCallAddbackBeqAbPrimeLimb1 a b = _
  unfold algCallAddbackBeqAbPrimeLimb1
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

theorem algCallAddbackBeqAbPrimeLimb2_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqAbPrimeLimb2 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.1) := by
  show algCallAddbackBeqAbPrimeLimb2 a b = _
  unfold algCallAddbackBeqAbPrimeLimb2
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

theorem algCallAddbackBeqAbPrimeLimb3_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqAbPrimeLimb3 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.2.1) := by
  show algCallAddbackBeqAbPrimeLimb3 a b = _
  unfold algCallAddbackBeqAbPrimeLimb3
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridge: `algCallAddbackBeqPost1Val` in parent-friendly `(64 - s)` form** (CLOSED).

    Parallel to `algCallAddbackBeqCarry_eq_parent_64ms_form`. Equates the
    irreducible def's antiShift-form body with the parent's local
    `64 - s` form, so the parent can rewrite its local val256 of the
    addback post1 limbs to `algCallAddbackBeqPost1Val a b`. -/
theorem algCallAddbackBeqPost1Val_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqPost1Val a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let post1 := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
     val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1) := by
  rw [algCallAddbackBeqPost1Val_unfold]
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridge: `algCallAddbackBeqCarry` in parent-friendly `(64 - s)` form** (CLOSED).

    The irreducible def's body uses antiShift form `(signExtend12 0 -
    clz).toNat % 64`. The parent adapter's local `set` lines use the
    Nat-subtraction form `64 - s` (matching what the runtime emits via
    bit-shift instructions). This bridge equates the two forms under
    `hshift_nz`, so the parent can use `algCallAddbackBeqCarry a b ≠ 0`
    directly from its local `carry_word ≠ 0` hypothesis. -/
theorem algCallAddbackBeqCarry_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqCarry a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3') := by
  rw [algCallAddbackBeqCarry_unfold]
  -- Convert antiShift form to (64 - s) form via hanti_toNat_mod.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Irreducible bundle: val256 of ms low 4 outputs at normalized inputs.**

    Captures `val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1` where `ms = mulsubN4
    qHat b0' b1' b2' b3' u0 u1 u2 u3` at the algorithm's normalized limbs.
    Used as `ms_val` in `post1_val_eq_amod_pow_s_pure_nat` and the addback
    Euclidean (h_addback) and mulsub Euclidean (h_mulsub) preconditions. -/
@[irreducible]
def algCallAddbackBeqMsLowVal (a b : EvmWord) : Nat :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1

/-- Unfolding lemma for `algCallAddbackBeqMsLowVal`. -/
theorem algCallAddbackBeqMsLowVal_unfold {a b : EvmWord} :
    algCallAddbackBeqMsLowVal a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1) := by
  show algCallAddbackBeqMsLowVal a b = _
  unfold algCallAddbackBeqMsLowVal
  rfl

/-- **Bridge: `algCallAddbackBeqMsLowVal` in parent-friendly `(64 - s)` form** (CLOSED).

    Parallel to the carry/post1Val bridges. Equates the irreducible def's
    antiShift-form body with the parent's local `64 - s` form for the
    val256 of mulsub low 4 outputs. -/
theorem algCallAddbackBeqMsLowVal_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqMsLowVal a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1) := by
  rw [algCallAddbackBeqMsLowVal_unfold]
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bound: `algCallAddbackBeqPost1Val a b < 2^256`** (CLOSED).

    Trivial: the addback's low 4 outputs are 4 `Word`s, so their `val256` is
    bounded by `2^256` regardless of inputs. Useful as the `h_post1_lt`
    precondition of `post1_val_eq_amod_pow_s_pure_nat` when closing the
    `algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback` wrapper. -/
theorem algCallAddbackBeqPost1Val_lt_pow256 (a b : EvmWord) :
    algCallAddbackBeqPost1Val a b < 2 ^ 256 := by
  rw [algCallAddbackBeqPost1Val_unfold]
  simp only []
  exact EvmWord.val256_bound _ _ _ _

/-- **AbPrimeVal val256 bound** (Phase B.4 mechanical, CLOSED).

    Mirror of `algCallAddbackBeqPost1Val_lt_pow256` for the
    double-addback's second-addback val256. Used as the
    `h_abPrime_lt` precondition of `abPrime_val_eq_amod_pow_s_pure_nat`
    (B.3) when closing B.5.

    Issue #1338. -/
theorem algCallAddbackBeqAbPrimeVal_lt_pow256 (a b : EvmWord) :
    algCallAddbackBeqAbPrimeVal a b < 2 ^ 256 := by
  rw [algCallAddbackBeqAbPrimeVal_unfold]
  simp only []
  exact EvmWord.val256_bound _ _ _ _

/-- **Bound: `algCallAddbackBeqU4 * 2^256 ≤ val256(a) * 2^s`** (CLOSED).

    Uses `u4 = a3 >>> antiShift = a3 / 2^(64-s)` so `u4 * 2^(64-s) ≤ a3`,
    then multiplies by `2^(192+s)` and uses `val256(a) ≥ a3 * 2^192` to
    yield `u4 * 2^256 ≤ val256(a) * 2^s`.

    Useful as the `h_u4_le` precondition of `post1_val_eq_amod_pow_s_pure_nat`
    when closing the `algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback`
    wrapper. -/
theorem algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    (algCallAddbackBeqU4 a b).toNat * 2 ^ 256 ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
  -- Unfold the irreducible u4 to expose `(a.getLimbN 3) >>> antiShift`.
  rw [show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl]
  -- Setup: clz bounds and antiShift conversion.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  -- u4 toNat = a3 / 2^(64-s).
  have h_u4_toNat : ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64)).toNat =
      (a.getLimbN 3).toNat / 2 ^ ((signExtend12 (0 : BitVec 12) -
        (clzResult (b.getLimbN 3)).1).toNat % 64) := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  -- val256(a) ≥ a3 * 2^192.
  have h_a3_val_ge :
      (a.getLimbN 3).toNat * 2 ^ 192 ≤
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := by
    unfold val256; nlinarith [(a.getLimbN 0).isLt, (a.getLimbN 1).isLt, (a.getLimbN 2).isLt]
  -- u4 * 2^(64-s) ≤ a3 via Nat.div_mul_le_self.
  rw [h_u4_toNat, h_anti_eq]
  set s := (clzResult (b.getLimbN 3)).1.toNat
  have h_u4_mul : (a.getLimbN 3).toNat / 2 ^ (64 - s) * 2 ^ (64 - s)
      ≤ (a.getLimbN 3).toNat :=
    Nat.div_mul_le_self _ _
  -- Split 2^256 = 2^(64-s) * (2^192 * 2^s).
  rw [h_s_eq]
  have h_pow_split : (2 : Nat) ^ 256 = 2 ^ (64 - s) * (2 ^ 192 * 2 ^ s) := by
    rw [show (2 : Nat) ^ 192 * 2 ^ s = 2 ^ (192 + s) from by rw [pow_add],
        show (2 : Nat) ^ (64 - s) * 2 ^ (192 + s) = 2 ^ ((64 - s) + (192 + s)) from
          (pow_add 2 (64-s) (192+s)).symm,
        show (64 - s) + (192 + s) = 256 from by omega]
  rw [h_pow_split]
  calc (a.getLimbN 3).toNat / 2 ^ (64 - s) * (2 ^ (64 - s) * (2 ^ 192 * 2 ^ s))
      = ((a.getLimbN 3).toNat / 2 ^ (64 - s) * 2 ^ (64 - s)) * (2 ^ 192 * 2 ^ s) := by ring
    _ ≤ (a.getLimbN 3).toNat * (2 ^ 192 * 2 ^ s) :=
        Nat.mul_le_mul_right _ h_u4_mul
    _ = (a.getLimbN 3).toNat * 2 ^ 192 * 2 ^ s := by ring
    _ ≤ val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) * 2 ^ s :=
        Nat.mul_le_mul_right _ h_a3_val_ge

/-- **Addback Euclidean (carry = 1) for the call+addback BEQ algorithm** (CLOSED).

    In the single-addback branch (`algCallAddbackBeqCarry a b ≠ 0`),
    the val256 of the post1 limbs satisfies:

      `algCallAddbackBeqPost1Val a b + 2^256 =
         algCallAddbackBeqMsLowVal a b + val256(b_limbs) * 2^s`

    where s = clz % 64. Combines `addbackN4_val256_eq` (carry-form) with
    `addbackN4_carry_le_one` to pin carry.toNat = 1, plus `val256_normalize`
    to fold the normalized b into `val256(b) * 2^s`.

    Useful as the `h_addback` precondition of
    `post1_val_eq_amod_pow_s_pure_nat` when closing the wrapper. -/
theorem algCallAddbackBeq_addback_euclidean_carry_one
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqPost1Val a b + 2 ^ 256 =
      algCallAddbackBeqMsLowVal a b +
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
  -- Setup: clz bounds.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- Unfold both irreducibles.
  rw [algCallAddbackBeqPost1Val_unfold, algCallAddbackBeqMsLowVal_unfold]
  simp only []
  -- Define ms in let-chain form.
  set shift := (clzResult (b.getLimbN 3)).1.toNat % 64 with hshift_def
  set antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 with hanti_def
  set b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set u4 := (a.getLimbN 3) >>> antiShift
  set qHat := div128Quot u4 u3 b3'
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- Addback Euclidean at val256 level.
  have h_addback_eq := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  simp only [] at h_addback_eq
  -- carry.toNat = 1: from hcarry_nz (≠ 0) + addbackN4_carry_le_one (≤ 1).
  have h_carry_le := addbackN4_carry_le_one ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  rw [algCallAddbackBeqCarry_unfold] at hcarry_nz
  simp only [] at hcarry_nz
  have h_carry_eq_one :
      (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat = 1 := by
    have h_pos : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat ≠ 0 := by
      intro h_zero
      apply hcarry_nz
      apply BitVec.eq_of_toNat_eq
      rw [h_zero]; rfl
    omega
  rw [h_carry_eq_one] at h_addback_eq
  -- val256(b_norm) = val256(b) * 2^s.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ shift := by
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- Combine.
  rw [h_norm_b] at h_addback_eq
  omega

/-- **Variant attempt**: prove carry_zero Euclidean WITHOUT the `simp
    [Nat.zero_mul, Nat.add_zero]` pre-pass. Maybe leaving `0 * 2^256`
    in the equation lets omega's certificate match the carry_one
    pattern (which has a `+ 1 * 2^256` term). -/
theorem algCallAddbackBeq_addback_euclidean_carry_zero_v2
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqPost1Val a b + 0 * 2 ^ 256 =
      algCallAddbackBeqMsLowVal a b +
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz; exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  rw [algCallAddbackBeqPost1Val_unfold, algCallAddbackBeqMsLowVal_unfold]
  simp only []
  set shift := (clzResult (b.getLimbN 3)).1.toNat % 64 with hshift_def
  set antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 with hanti_def
  set b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set u4 := (a.getLimbN 3) >>> antiShift
  set qHat := div128Quot u4 u3 b3'
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  have h_addback_eq := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  simp only [] at h_addback_eq
  rw [algCallAddbackBeqCarry_unfold] at hcarry_zero
  simp only [] at hcarry_zero
  have h_carry_eq_zero :
      (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat = 0 := by
    rw [hcarry_zero]; rfl
  rw [h_carry_eq_zero] at h_addback_eq
  -- DELIBERATELY skip `simp [Nat.zero_mul, Nat.add_zero]`. Goal LHS now has
  -- `+ 0 * 2^256` to match the carry_one pattern's `+ 1 * 2^256`.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ shift := by
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  rw [h_norm_b] at h_addback_eq
  omega

/-- **MsLowVal + val256(b_norm) * 2^s no-overflow** (CLOSED, derived via v2).

    `algCallAddbackBeqMsLowVal a b + val256(b_limbs) * 2^s < 2^256`

    when `algCallAddbackBeqCarry a b = 0` (double-addback's first
    addback has no overflow). This is the `h_no_overflow` precondition
    of `qHat_ge_two_abstract` for B.1a's call-addback-side closure.

    Derives via:
    - `algCallAddbackBeq_addback_euclidean_carry_zero_v2`: Post1Val + 0*2^256
      = MsLowVal + val256(b_limbs) * 2^s.
    - `algCallAddbackBeqPost1Val_lt_pow256`: Post1Val < 2^256.
    - `linarith` to combine (avoiding `omega`'s deterministic-timeout
      issue when chained through `algCallAddbackBeq_addback_euclidean_carry_zero_v2`). -/
theorem algCallAddbackBeqMsLowVal_plus_b_norm_lt_pow256
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqMsLowVal a b +
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) < 2 ^ 256 := by
  have h_eq := algCallAddbackBeq_addback_euclidean_carry_zero_v2 a b hshift_nz hcarry_zero
  have h_lt := algCallAddbackBeqPost1Val_lt_pow256 a b
  linarith

/-- **Mulsub Euclidean — raw form (no qHat substitution)** (CLOSED).

    The val256-level mulsub identity at the algorithm's normalized inputs,
    expressed directly in terms of the irreducibles `algCallAddbackBeqMsC3`
    and `algCallAddbackBeqMsLowVal` AND the algorithm's actual qHat
    (no substitution with `a/b + 1` or `a/b + 2`):

      `(MsC3 a b).toNat * 2^256 + val256(a) * 2^s
         = MsLowVal a b + qHat.toNat * (val256(b) * 2^s)
                        + (algCallAddbackBeqU4 a b).toNat * 2^256`

    Notation: `qHat := div128Quot u4 u3 b3'` (the algorithm's actual
    qHat in the let-chain).

    This is the **`h_mulsub` precondition for `qHat_ge_two_abstract`**
    in B.1a. Independent of B.1 (no qHat = a/b + 2 substitution),
    so usable in B.1a's proof. -/
theorem algCallAddbackBeq_mulsub_eucl_irreducible_form
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let qHat := div128Quot u4 u3 b3'
    (algCallAddbackBeqMsC3 a b).toNat * 2 ^ 256 +
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) =
    algCallAddbackBeqMsLowVal a b +
      qHat.toNat *
        (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) +
      (algCallAddbackBeqU4 a b).toNat * 2 ^ 256 := by
  intro shift antiShift b3' u3 u4 qHat
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz; exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  rw [show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl,
      show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl,
      algCallAddbackBeqMsLowVal_unfold]
  simp only []
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- Mulsub Euclidean.
  have h_mulsub_eq := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub_eq
  -- val256(b_norm) = val256(b) * 2^s.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ shift := by
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- val256(u_norm low4) + u4 * 2^256 = val256(a) * 2^s.
  have h_norm_u : val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ shift := by
    show val256 ((a.getLimbN 0) <<< shift)
                (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift))
                (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift))
                (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)) +
            ((a.getLimbN 3) >>> antiShift).toNat * 2 ^ 256 = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize_general h_clz_pos h_clz_lt_64
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  rw [h_norm_b] at h_mulsub_eq
  linarith

/-- **Bound: `algCallAddbackBeqU4 < algCallAddbackBeqMsC3`** (CLOSED).

    Wraps `EvmWord.u_top_lt_c3_of_addback_borrow_call` in the irreducible-
    bundle form, taking just `hborrow : isAddbackBorrowN4CallEvm a b`.
    Useful as the `h_u4_lt_c3` precondition of
    `post1_val_eq_amod_pow_s_pure_nat` when closing the wrapper. -/
theorem algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat
    (a b : EvmWord) (hborrow : isAddbackBorrowN4CallEvm a b) :
    (algCallAddbackBeqU4 a b).toNat < (algCallAddbackBeqMsC3 a b).toNat := by
  rw [show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl,
      show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl]
  rw [isAddbackBorrowN4CallEvm_def] at hborrow
  exact EvmWord.u_top_lt_c3_of_addback_borrow_call
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hborrow

/-- **Abstract Nat-level sub-lemma for B.1a**: under mulsub Euclidean +
    first-addback no-overflow + c3 ≥ 1, `qHat ≥ 2`.

    Pure Nat algebra. Used to factor B.1a's proof, avoiding the kernel
    deep-recursion that arises when `rfl`-bridging through deeply-nested
    `mulsubN4` let-chains.

    Hypotheses encode:
    - h_mulsub: `c3 · 2^256 + u_norm = ms + qHat · b_norm` (mulsubN4_val256_eq).
    - h_no_overflow: `ms + b_norm < 2^256` (first-addback Euclidean with carry₁ = 0
      directly gives this — `val256(ab) = ms + b_norm` and `val256(ab) < 2^256`).
    - h_c3_pos: `c3 ≥ 1` (from hborrow's u4 < c3).

    **Key simplification** (vs. earlier 6-arg version): folding the addback
    Euclidean + val256 bound into a single `h_no_overflow` parameter eliminates
    the explicit `ab` parameter, so callers don't need to supply the deep
    `addbackN4 (mulsubN4 ...) ...` expression — sidesteps the kernel
    deep-recursion at instantiation.

    Issue #1338 Phase B.1a. -/
theorem qHat_ge_two_abstract
    (qHat ms u_norm b_norm c3 : Nat)
    (h_mulsub : c3 * 2^256 + u_norm = ms + qHat * b_norm)
    (h_no_overflow : ms + b_norm < 2^256)
    (h_c3_pos : c3 ≥ 1) :
    qHat ≥ 2 := by
  by_contra h_lt
  push Not at h_lt
  have h_case : qHat = 0 ∨ qHat = 1 := by omega
  rcases h_case with h_qHat_zero | h_qHat_one
  · rw [h_qHat_zero] at h_mulsub
    simp only [Nat.zero_mul, Nat.add_zero] at h_mulsub
    omega
  · rw [h_qHat_one] at h_mulsub
    simp only [Nat.one_mul] at h_mulsub
    omega

/-- **B.1a (sub-lemma, sorry — pending bridges):** `qHat ≥ 2` under
    double-addback hypotheses.

    Moved here (from before line 2244) to use the
    `algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat` wrapper
    directly instead of the inline `EvmWord.u_top_lt_c3_of_addback_borrow_call`
    + antiShift dance. Eliminates the previous forward-reference issue.

    **Proof outline** (still pending closure due to set/rfl bridges):
    - by_contra h_lt: qHat.toNat < 2.
    - From hborrow + wrapper: u4 < c3 (Word level via irreducibles).
    - interval_cases qHat.toNat:
      - qHat = 0: c3_un_zero_of_qHat_mul_le gives c3 = 0. Contradiction
        with c3 > u4 ≥ 0.
      - qHat = 1: mulsub gives val256(u_norm) + c3*2^256 = val256(ms) +
        val256(b_norm). hcarry_zero with first-addback Euclidean gives
        val256(ms) + val256(b_norm) < 2^256. Combined with c3 ≥ 1:
        val256(u_norm) + 2^256 < 2^256 = contradiction.

    **Pending technicalities** for next iteration:
    - Bridge `(algCallAddbackBeqU4 a b).toNat = u4.toNat` via the
      irreducible's unfold (1-line `show`/`rfl`).
    - Handle `interval_cases qHat.toNat` substitution (use case
      hypothesis directly instead of `rfl`).
    - `set ms := ...` to align `c3_un_zero_of_qHat_mul_le`'s output.

    Estimated remaining: ~80 LOC. Issue #1338 Phase B.1a. -/
theorem qHat_ge_two_of_double_addback (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    (div128Quot u4 u3 b3').toNat ≥ 2 := by
  -- **4th attempt with `algCallAddbackBeqMsLowVal` / `algCallAddbackBeqMsC3`
  -- irreducibles still hits kernel deep-recursion (101 sec build)**.
  -- Per pirapira PR review (#1339 line 3543): "Use irreducible definitions".
  --
  -- The existing irreducibles work as opaque Nats at the abstract-lemma
  -- application level. The kernel-recursion happens at proof-CHECKING time:
  -- when verifying the `apply` step, Lean reduces the proof obligations
  -- (e.g., the `addbackN4 (mulsubN4 ...) ...` inside `h_addback`'s proof),
  -- which still triggers the deep let-chain reduction.
  --
  -- **Recommended path forward** (next iteration): add a NEW irreducible
  -- `algCallAddbackBeqAbLowValDouble a b : Nat` for the val256 of the
  -- first-addback's low 4 outputs in the double-addback path. Then
  -- `h_no_overflow` becomes:
  --   `algCallAddbackBeqMsLowVal a b + val256(b_norm)
  --     = algCallAddbackBeqAbLowValDouble a b   (carry = 0 case)
  --     ∧ algCallAddbackBeqAbLowValDouble a b < 2^256` (val256 bound)
  --   ⟹ `algCallAddbackBeqMsLowVal a b + val256(b_norm) < 2^256`.
  -- Both are statements about irreducibles only, no deep let-chain in proof.
  --
  intro shift antiShift b3' u3 u4
  -- Apply qHat_ge_two_abstract with irreducibles + closed preconditions.
  -- Note: u_norm = val256(a) * 2^s - u4 * 2^256 (Nat sub via h_u4_le).
  apply qHat_ge_two_abstract
    (div128Quot u4 u3 b3').toNat
    (algCallAddbackBeqMsLowVal a b)
    (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) -
      (algCallAddbackBeqU4 a b).toNat * 2 ^ 256)
    (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64))
    (algCallAddbackBeqMsC3 a b).toNat
  · -- h_mulsub: c3 * 2^256 + u_norm = ms + qHat * b_norm.
    have h_eucl := algCallAddbackBeq_mulsub_eucl_irreducible_form a b hshift_nz
    simp only [] at h_eucl
    have h_u4_le := algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s a b hshift_nz
    -- Bridge the let-fvars `u4 u3 b3'` (in the goal) to the explicit forms
    -- in h_eucl. Both are defeq via zeta but omega can't see lets.
    have h_qHat_eq : (div128Quot u4 u3 b3').toNat =
        (div128Quot ((a.getLimbN 3) >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
           ((a.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
           ((b.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat
                % 64)))).toNat := rfl
    rw [h_qHat_eq]
    -- Substitute val256(a)*2^s = u_norm + u4*2^256 (Nat sub bridge via h_u4_le).
    have h_a_eq :
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
            2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) =
        (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) -
          (algCallAddbackBeqU4 a b).toNat * 2 ^ 256) +
          (algCallAddbackBeqU4 a b).toNat * 2 ^ 256 := by omega
    rw [h_a_eq] at h_eucl
    omega
  · -- h_no_overflow: ms + b_norm < 2^256.
    exact algCallAddbackBeqMsLowVal_plus_b_norm_lt_pow256 a b hshift_nz hcarry_zero
  · -- h_c3_pos: c3 ≥ 1, from u4 < c3 (hborrow).
    have h := algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat a b hborrow
    have := (algCallAddbackBeqU4 a b).isLt; omega

/-- **B.1 (#1338, NOT Knuth-B blocked):** qHat.toNat = a/b + 2
    in double-addback case.

    Mirror of `qHat_eq_div_plus_one_of_single_addback` for the
    double-addback branch (`algCallAddbackBeqCarry a b = 0`).

    **REFINED ANALYSIS (2026-04-26):** This lemma does NOT actually need
    Knuth-B (#1337). The lower bound qHat ≥ a/b + 2 is **derivable
    directly** from hborrow + hcarry_zero via mulsub algebra:

    1. From hborrow: u4 < c3 (so c3 - u4 ≥ 1).
    2. From mulsub Euclidean (instantiated):
       val256(ms) + qHat * b * 2^s = a * 2^s + (c3 - u4) * 2^256.
    3. carry₁ = 0 means val256(ms) + b * 2^s < 2^256 (no overflow in
       first addback). Substituting (2):
       a * 2^s + (c3 - u4) * 2^256 - (qHat - 1) * b * 2^s < 2^256.
    4. With c3 - u4 ≥ 1: (qHat - 1) * b * 2^s > a * 2^s, hence
       (qHat - 1) * b > a, hence qHat - 1 > a/b, hence qHat ≥ a/b + 2.

    **Proof structure**: composes B.1a (qHat ≥ 2, CLOSED above) with
    Word arithmetic on hsem (this proof, ~50 LOC, fully closed).

    Issue #1338 Phase B.1. -/
theorem qHat_eq_div_plus_two_of_double_addback (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    (div128Quot u4 u3 b3').toNat = a.toNat / b.toNat + 2 := by
  intro shift antiShift b3' u3 u4
  -- B.1a (algorithm-side): qHat ≥ 2.
  have hqHat_ge_two : (div128Quot u4 u3 b3').toNat ≥ 2 :=
    qHat_ge_two_of_double_addback a b hshift_nz hborrow hcarry2_nz hcarry_zero
  -- Bridge hcarry_zero to the parent's let-chain form via algCallAddbackBeqCarry_unfold.
  rw [algCallAddbackBeqCarry_unfold] at hcarry_zero
  -- Unfold hsem with the carry-equals-0 case.
  rw [n4CallAddbackBeqSemanticHolds_def] at hsem
  simp only [if_pos hcarry_zero] at hsem
  -- val256(a_limbs) = a.toNat, val256(b_limbs) = b.toNat.
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
  -- hsem: (qHat + signExtend12 4095 + signExtend12 4095).toNat = a/b.
  set qHat := div128Quot u4 u3 b3' with hqHat_def
  rw [BitVec.toNat_add, BitVec.toNat_add, signExtend12_4095_toNat] at hsem
  have h_inner_eq : (qHat.toNat + (2^64 - 1)) % 2^64 = qHat.toNat - 1 := by
    have h_qHat_lt : qHat.toNat < 2^64 := qHat.isLt
    rw [show qHat.toNat + (2^64 - 1) = (qHat.toNat - 1) + 2^64 from by omega]
    rw [Nat.add_mod_right]
    apply Nat.mod_eq_of_lt; omega
  rw [h_inner_eq] at hsem
  have h_outer_eq : ((qHat.toNat - 1) + (2^64 - 1)) % 2^64 = qHat.toNat - 2 := by
    rw [show (qHat.toNat - 1) + (2^64 - 1) = (qHat.toNat - 2) + 2^64 from by omega]
    rw [Nat.add_mod_right]
    apply Nat.mod_eq_of_lt
    have := qHat.isLt; omega
  rw [h_outer_eq] at hsem
  omega

/-- **B.5 building block STUB: combined two-addback Euclidean** (#1338).

    Mirror of `algCallAddbackBeq_addback_euclidean_carry_one` for the
    **double-addback** path. Combines:
    - First addback (carry₁ = 0): val256(ab) = val256(ms) + val256(b_norm).
    - Second addback (carry₂ = 1, from `isAddbackCarry2NzN4CallEvm`):
      val256(ab') + 2^256 = val256(ab) + val256(b_norm).

    Combined: `AbPrimeVal + 2^256 = MsLowVal + 2 · (val256(b_limbs) · 2^s)`.

    **Proof sketch** (~120 LOC, mirrors single-addback's structure):
    - Setup clz bounds.
    - Unfold AbPrimeVal and MsLowVal.
    - Apply `addbackN4_val256_eq` to first addback; use `addbackN4_top_eq`
      to get the 5th-limb input for second addback.
    - Apply `addbackN4_val256_eq` to second addback (low4 of first addback's
      output + b_norm).
    - Use carry₁ = 0 (hcarry_zero) and carry₂ = 1 (from hcarry2_nz +
      `addbackN4_carry_le_one`).
    - Combine: val256(ab') + 2^256 = val256(ms) + 2 · val256(b_norm).
    - Apply `val256_normalize` for b_norm.

    Independent of Knuth-B (#1337). The complexity is mostly notational
    (let-chains aligning across two addback applications). -/
theorem algCallAddbackBeq_addback_combined_euclidean_carry2
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqAbPrimeVal a b + 2 ^ 256 =
      algCallAddbackBeqMsLowVal a b +
        2 * (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) := by
  -- Setup clz bounds.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz; exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- Unfold both irreducibles.
  rw [algCallAddbackBeqAbPrimeVal_unfold, algCallAddbackBeqMsLowVal_unfold]
  simp only []
  -- Define local let-chain.
  set shift := (clzResult (b.getLimbN 3)).1.toNat % 64 with hshift_def
  set antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 with hanti_def
  set b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set u4 := (a.getLimbN 3) >>> antiShift
  set qHat := div128Quot u4 u3 b3'
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  set c3 := ms.2.2.2.2
  set u4_new := u4 - c3
  set ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3' with hab_eq
  set abPrime := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
                  with habPrime_eq
  -- First addback Euclidean.
  have h_ab_eq := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  simp only [] at h_ab_eq
  -- carry₁ = 0 from hcarry_zero.
  rw [algCallAddbackBeqCarry_unfold] at hcarry_zero
  simp only [] at hcarry_zero
  have h_carry1_zero :
      (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat = 0 := by
    rw [hcarry_zero]; rfl
  rw [h_carry1_zero] at h_ab_eq
  -- Second addback Euclidean.
  have h_abPrime_eq := addbackN4_val256_eq ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2
                                            b0' b1' b2' b3'
  simp only [] at h_abPrime_eq
  -- carry₂ = 1 from hcarry2_nz applied to carry₁ = 0.
  rw [isAddbackCarry2NzN4CallEvm_def] at hcarry2_nz
  unfold isAddbackCarry2NzN4CallAb isAddbackCarry2NzN4Call isAddbackCarry2Nz at hcarry2_nz
  simp only [] at hcarry2_nz
  have h_carry2_nz_local := hcarry2_nz hcarry_zero
  have h_carry2_le := addbackN4_carry_le_one ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0' b1' b2' b3'
  have h_carry2_one :
      (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0' b1' b2' b3').toNat = 1 := by
    have h_pos : (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
                                    b0' b1' b2' b3').toNat ≠ 0 := by
      intro h_zero
      apply h_carry2_nz_local
      apply BitVec.eq_of_toNat_eq
      rw [h_zero]; rfl
    omega
  rw [h_carry2_one] at h_abPrime_eq
  -- val256(b_norm) = val256(b_limbs) * 2^shift.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ shift := by
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- Bridge the goal's inline addbackN4 forms via rfl (mirror of mulsub Euclidean).
  have h_ab_low : val256
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3').1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3').2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3').2.2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3').2.2.2.1
      = val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 := rfl
  have h_abPrime_low : val256
      (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').1
      (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.1
      (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.1
      (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.2.1
      = val256 abPrime.1 abPrime.2.1 abPrime.2.2.1 abPrime.2.2.2.1 := rfl
  rw [h_ab_low] at h_ab_eq
  rw [h_abPrime_low] at h_abPrime_eq
  rw [h_norm_b] at h_ab_eq h_abPrime_eq
  -- Goal uses val256(b.getLimbN 0)... * 2^shift directly; hypotheses now match.
  omega

/-- **Mulsub Euclidean for the call+addback BEQ algorithm** (CLOSED).

    The val256-level mulsub Euclidean identity at normalized inputs,
    composed with `qHat = a/b + 1` (single-addback) and the normalization
    identities for `u_norm` and `b_norm`. In the irreducible-bundle form:

      (algCallAddbackBeqMsC3 a b).toNat * 2^256 +
        (val256(a_limbs) * 2^s - (algCallAddbackBeqU4 a b).toNat * 2^256) =
      algCallAddbackBeqMsLowVal a b +
        (val256(a_limbs) / val256(b_limbs) + 1) * (val256(b_limbs) * 2^s)

    Useful as the `h_mulsub` precondition of
    `post1_val_eq_amod_pow_s_pure_nat` when closing the wrapper. -/
theorem algCallAddbackBeq_mulsub_euclidean
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    (algCallAddbackBeqMsC3 a b).toNat * 2 ^ 256 +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) -
        (algCallAddbackBeqU4 a b).toNat * 2 ^ 256) =
    algCallAddbackBeqMsLowVal a b +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 1) *
      (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) := by
  -- Setup: clz bounds.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- Bridge val256(a_limbs) = a.toNat and similar for b.
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
  -- qHat = a/b + 1 from the closed sub-stub.
  rw [algCallAddbackBeqCarry_unfold] at hcarry_nz
  have h_qHat_eq : (div128Quot ((a.getLimbN 3) >>>
      ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
      (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
        ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64)))
      (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
        ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64)))).toNat =
      a.toNat / b.toNat + 1 :=
    qHat_eq_div_plus_one_of_single_addback a b hshift_nz hborrow hsem hcarry_nz
  -- Unfold the irreducibles.
  rw [show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl,
      show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl,
      algCallAddbackBeqMsLowVal_unfold]
  simp only []
  -- Set up the let-chain.
  set shift := (clzResult (b.getLimbN 3)).1.toNat % 64 with hshift_def
  set antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 with hanti_def
  set b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift) with hb3_eq
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift) with hu3_eq
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set u4 := (a.getLimbN 3) >>> antiShift with hu4_eq
  set qHat := div128Quot u4 u3 b3' with hqHat_eq
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- Mulsub Euclidean at val256 level.
  have h_mulsub_eq := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub_eq
  -- val256(b_norm) = val256(b) * 2^s.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ shift := by
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- val256(u_norm low4) + u4 * 2^256 = val256(a) * 2^s.
  have h_norm_u : val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ shift := by
    show val256 ((a.getLimbN 0) <<< shift)
                (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift))
                (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift))
                (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)) +
            ((a.getLimbN 3) >>> antiShift).toNat * 2 ^ 256 = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize_general h_clz_pos h_clz_lt_64
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  -- Express h_qHat_eq in terms of the let-chain qHat.
  have h_qHat : qHat.toNat = a.toNat / b.toNat + 1 := h_qHat_eq
  -- Combine. Substitute into h_mulsub_eq using h_norm_b, h_qHat, h_norm_u.
  rw [h_norm_b] at h_mulsub_eq
  rw [h_qHat] at h_mulsub_eq
  rw [ha_val, hb_val]
  have h_u_eq : val256 u0 u1 u2 u3 = a.toNat * 2 ^ shift - u4.toNat * 2 ^ 256 := by
    have h := h_norm_u; rw [ha_val] at h; omega
  rw [h_u_eq] at h_mulsub_eq
  rw [hb_val] at h_mulsub_eq
  -- Bridge the goal's inline `mulsubN4 ...` forms to `ms.{...}` via rfl.
  have h_ms_top : (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
      = ms.2.2.2.2.toNat := rfl
  have h_ms_low : val256
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.1
      = val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := rfl
  rw [h_ms_top, h_ms_low]
  omega

/-- **Bound: `a%b * 2^s < 2^256` in the call+addback BEQ shape** (CLOSED).

    Wraps `EvmWord.val256_mod_mul_pow_lt_pow256_of_b3_bound` taking
    `b3 ≠ 0` (rather than `b ≠ 0`) and giving the `% 64`-shifted exponent
    form used by the algorithm scaffold. Useful as the `h_amod_pow_lt`
    precondition of `post1_val_eq_amod_pow_s_pure_nat` when closing
    `algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback`. -/
theorem algCallAddbackBeq_amod_pow_s_lt_pow256
    (a b : EvmWord) (hb3nz : b.getLimbN 3 ≠ 0) :
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) < 2 ^ 256 := by
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hvb_pos : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    EvmWord.val256_pos_of_or_ne_zero hbnz
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  rw [h_s_eq]
  exact EvmWord.val256_mod_mul_pow_lt_pow256_of_b3_bound
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (by omega) hvb_pos hb3_bound

/-- **B.5 building block STUB: mulsub Euclidean for double-addback** (#1338).

    Mirror of `algCallAddbackBeq_mulsub_euclidean` for the double-addback path.
    The val256-level mulsub identity at normalized inputs, with the qHat factor
    being `val256(a)/val256(b) + 2` (per B.1 `qHat_eq_div_plus_two_of_double_addback`):

      c3_n · 2^256 + (val256(a)·2^s − u4·2^256) =
        algCallAddbackBeqMsLowVal a b + (val256(a)/val256(b) + 2) · (val256(b)·2^s)

    **Proof sketch** (~155 LOC, mirrors single-addback's structure):
    - Setup clz bounds (same as single-addback).
    - Bridge val256(a_limbs) = a.toNat, val256(b_limbs) = b.toNat.
    - Apply `mulsubN4_val256_eq` for the val256-level identity.
    - Substitute qHat via B.1 (`qHat_eq_div_plus_two_of_double_addback`).
    - val256_normalize for u_norm and b_norm.

    **Dependencies**: B.1 (CLOSED, `qHat_eq_div_plus_two_of_double_addback`).
    Mirror of single-addback's `algCallAddbackBeq_mulsub_euclidean`.
    Issue #1338 Phase B.5. -/
theorem algCallAddbackBeq_mulsub_euclidean_double
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    (algCallAddbackBeqMsC3 a b).toNat * 2 ^ 256 +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) -
        (algCallAddbackBeqU4 a b).toNat * 2 ^ 256) =
    algCallAddbackBeqMsLowVal a b +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2) *
      (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) := by
  -- Setup: clz bounds.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- Bridge val256(a_limbs) = a.toNat and similar for b.
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
  -- qHat = a/b + 2 from B.1 (closed mod B.1a).
  have h_qHat_eq : (div128Quot ((a.getLimbN 3) >>>
      ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
      (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
        ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64)))
      (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
        ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64)))).toNat =
      a.toNat / b.toNat + 2 :=
    qHat_eq_div_plus_two_of_double_addback a b hshift_nz hborrow hcarry2_nz
      hsem hcarry_zero
  -- Unfold the irreducibles.
  rw [show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl,
      show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl,
      algCallAddbackBeqMsLowVal_unfold]
  simp only []
  -- Set up the let-chain.
  set shift := (clzResult (b.getLimbN 3)).1.toNat % 64 with hshift_def
  set antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 with hanti_def
  set b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift) with hb3_eq
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift) with hu3_eq
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set u4 := (a.getLimbN 3) >>> antiShift with hu4_eq
  set qHat := div128Quot u4 u3 b3' with hqHat_eq
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- Mulsub Euclidean at val256 level.
  have h_mulsub_eq := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub_eq
  -- val256(b_norm) = val256(b) * 2^s.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ shift := by
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- val256(u_norm low4) + u4 * 2^256 = val256(a) * 2^s.
  have h_norm_u : val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ shift := by
    show val256 ((a.getLimbN 0) <<< shift)
                (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift))
                (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift))
                (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)) +
            ((a.getLimbN 3) >>> antiShift).toNat * 2 ^ 256 = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize_general h_clz_pos h_clz_lt_64
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  -- Express h_qHat_eq in terms of the let-chain qHat.
  have h_qHat : qHat.toNat = a.toNat / b.toNat + 2 := h_qHat_eq
  -- Combine. Substitute into h_mulsub_eq using h_norm_b, h_qHat, h_norm_u.
  rw [h_norm_b] at h_mulsub_eq
  rw [h_qHat] at h_mulsub_eq
  rw [ha_val, hb_val]
  have h_u_eq : val256 u0 u1 u2 u3 = a.toNat * 2 ^ shift - u4.toNat * 2 ^ 256 := by
    have h := h_norm_u; rw [ha_val] at h; omega
  rw [h_u_eq] at h_mulsub_eq
  rw [hb_val] at h_mulsub_eq
  -- Bridge the goal's inline `mulsubN4 ...` forms to `ms.{...}` via rfl.
  have h_ms_top : (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
      = ms.2.2.2.2.toNat := rfl
  have h_ms_low : val256
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.1
      = val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := rfl
  rw [h_ms_top, h_ms_low]
  omega

/-- **Sub-stub: c3_n = u4 + 1 in single-addback** (CLOSED).

    The key algebraic identity for the call-addback BEQ MOD adapter, mirroring
    `u_top_eq_c3_n_of_overestimate` (call-skip case where c3_n = u4).

    Under hsem + hcarry_nz (single-addback) + hborrow (giving u4 < c3_n):
    - From `qHat_eq_div_plus_one_of_single_addback`: qHat = val256(a)/val256(b) + 1.
    - Mulsub Euclidean: c3_n*2^256 = val256(ms_n) + qHat*val256(b_norm) - val256(u_norm).
    - val256(u_norm) = val256(a)*2^s - u4*2^256, val256(b_norm) = val256(b)*2^s.
    - Algebra: c3_n*2^256 = val256(ms_n) + (val256(b) - val256(a)%val256(b))*2^s + u4*2^256.

    The bound `0 ≤ val256(post1_low4) < 2^256` (from val256 being a 4-limb val)
    combined with the addback Euclidean (carry = 1) forces c3_n - 1 - u4 = 0,
    i.e., c3_n = u4 + 1.

    Combined with hborrow's c3_n ≥ u4 + 1, this pins c3_n exactly.

    **Caveat for callers**: this sub-stub uses `% 64` form for shift/antiShift
    (matching `n4CallAddbackBeqSemanticHolds_def`). Direct application from a
    parent context that uses `set s := clz.1.toNat` (no `% 64`) hits a
    200k-heartbeat elaboration timeout. Callers should align their let-chain
    binding form to use `% 64`, or inline the proof body. -/
theorem c3_n_eq_u4_plus_one_of_single_addback (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
                 let antiShift :=
                   (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
                 let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
                 let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
                 let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
                 let b0' := (b.getLimbN 0) <<< shift
                 let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
                 let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
                 let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
                 let u0 := (a.getLimbN 0) <<< shift
                 let u4 := (a.getLimbN 3) >>> antiShift
                 let qHat := div128Quot u4 u3 b3'
                 let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
                 addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let qHat := div128Quot u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    ms.2.2.2.2.toNat = u4.toNat + 1 := by
  intro shift antiShift b3' b2' b1' b0' u3 u2 u1 u0 u4 qHat ms
  -- Concrete proof: apply the closed pure-Nat sub-stub
  -- `c3_eq_u4_plus_one_from_mulsub_addback_bounds` after deriving its 6
  -- preconditions:
  -- - h_mulsub: from `mulsubN4_val256_eq` at normalized limbs +
  --   `qHat_eq_div_plus_one_of_single_addback` (hsem is in scope).
  -- - h_addback: from `addbackN4_val256_eq` at normalized limbs (carry = 1
  --   from hcarry_nz).
  -- - h_u4_le: u4*2^256 ≤ val256(a)*2^s. Follows from u4 = a3 >>> antiShift
  --   (top-s bits of a3) plus val256(a) ≥ a3 * 2^192.
  -- - h_post1_lt: val256(post1_low4) < 2^256 (always, val256 of 4 limbs).
  -- - h_amod_pow_lt: val256(a) % val256(b) * 2^s < 2^256. Follows from
  --   val256(a) % val256(b) < val256(b) ≤ 2^256 / 2^s ⟹ a%b * 2^s < 2^256.
  --   This is the val256_mod_mul_pow bound, available as
  --   `val256_mod_mul_pow_lt_pow256_of_b3_bound`.
  -- - h_u4_lt_c3: directly from hborrow via `u_top_lt_c3_of_addback_borrow_call`.
  -- TODO: each precondition is a small focused derivation (~5-15 lines).
  -- Save folded forms for sub-stub applications, before unfolding.
  have hsem_orig := hsem
  have hborrow_orig := hborrow
  -- Step 1: h_u4_lt_c3 from hborrow.
  rw [isAddbackBorrowN4CallEvm_def] at hborrow
  have h_u4_lt_c3 := EvmWord.u_top_lt_c3_of_addback_borrow_call
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hborrow
  -- Step 2: h_post1_lt — val256(post1_low4) < 2^256 (val256 of any 4-limb is bounded).
  let post1 := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  have h_post1_lt : val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1 < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  -- Step 3: h_amod_pow_lt — val256(a) % val256(b) * 2^s < 2^256.
  have h_clz_le : (clzResult (b.getLimbN 3)).1.toNat ≤ 64 := by
    have := clzResult_fst_toNat_le (b.getLimbN 3); omega
  have hbnz_or : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hvb_pos : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    EvmWord.val256_pos_of_or_ne_zero hbnz_or
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  have h_amod_pow_lt :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ (clzResult (b.getLimbN 3)).1.toNat < 2 ^ 256 :=
    EvmWord.val256_mod_mul_pow_lt_pow256_of_b3_bound
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      h_clz_le hvb_pos hb3_bound
  -- Step 4: h_u4_le — u4 * 2^256 ≤ val256(a) * 2^s.
  -- u4 = a3 >>> antiShift = a3 / 2^(64-s), so u4 * 2^(64-s) ≤ a3.
  -- val256(a) ≥ a3 * 2^192. Hence u4 * 2^256 = u4 * 2^(64-s) * 2^(192+s)
  --   ≤ a3 * 2^(192+s) ≤ val256(a) * 2^s.
  have h_a3_val_ge :
      (a.getLimbN 3).toNat * 2^192 ≤
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := by
    unfold val256; nlinarith [(a.getLimbN 0).isLt, (a.getLimbN 1).isLt, (a.getLimbN 2).isLt]
  have h_u4_toNat : u4.toNat =
      (a.getLimbN 3).toNat / 2 ^ ((signExtend12 (0 : BitVec 12) -
        (clzResult (b.getLimbN 3)).1).toNat % 64) := by
    show ((a.getLimbN 3) >>> antiShift).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  -- antiShift = 64 - s, derived via antiShift_toNat_mod_eq (needs 1 ≤ s ≤ 63).
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have h_u4_le : u4.toNat * 2^256 ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    rw [h_s_eq]
    -- u4 * 2^antiShift ≤ a3 (Nat.div_mul_le_self).
    have h_u4_mul : u4.toNat * 2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat)
        ≤ (a.getLimbN 3).toNat := by
      rw [h_u4_toNat, h_anti_eq]
      exact Nat.div_mul_le_self _ _
    -- Multiply both sides by 2^(192 + s) and use the val256 ≥ a3*2^192 bound.
    set s := (clzResult (b.getLimbN 3)).1.toNat
    have h_pow_split : (2 : Nat)^256 = 2^(64 - s) * (2^192 * 2^s) := by
      rw [show (2 : Nat)^192 * 2^s = 2^(192 + s) from by rw [pow_add],
          show (2 : Nat)^(64 - s) * 2^(192 + s) = 2^((64 - s) + (192 + s)) from
            (pow_add 2 (64-s) (192+s)).symm,
          show (64 - s) + (192 + s) = 256 from by omega]
    rw [h_pow_split]
    -- Goal: u4 * (2^(64-s) * (2^192 * 2^s)) ≤ val256(a) * 2^s.
    calc u4.toNat * (2 ^ (64 - s) * (2 ^ 192 * 2 ^ s))
        = (u4.toNat * 2 ^ (64 - s)) * (2 ^ 192 * 2 ^ s) := by ring
      _ ≤ (a.getLimbN 3).toNat * (2 ^ 192 * 2 ^ s) :=
          Nat.mul_le_mul_right _ h_u4_mul
      _ = (a.getLimbN 3).toNat * 2 ^ 192 * 2 ^ s := by ring
      _ ≤ val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) * 2 ^ s :=
          Nat.mul_le_mul_right _ h_a3_val_ge
  -- Step 5a: addback Euclidean (val256-level, with carry term) — direct application.
  have h_addback_eq := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  simp only [] at h_addback_eq
  -- Step 5b: carry.toNat = 1 from hcarry_nz + addbackN4_carry_le_one.
  have h_carry_le := addbackN4_carry_le_one ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  have h_carry_eq_one : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat = 1 := by
    -- carry is a Word that's ≠ 0 (hcarry_nz) and ≤ 1 (h_carry_le); so carry.toNat = 1.
    have h_pos : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat ≠ 0 := by
      intro h_zero
      apply hcarry_nz
      change addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' = (0 : Word)
      apply BitVec.eq_of_toNat_eq
      rw [h_zero]; rfl
    omega
  -- Step 5c: val256(b_norm) = val256(b) * 2^s via val256_normalize.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    -- Unfold b0'..b3' and antiShift to bring the `(64 - s)` form into scope.
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    have h_anti_unfold : antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat := h_anti_eq
    have h_shift_unfold : shift = (clzResult (b.getLimbN 3)).1.toNat := h_s_eq
    rw [h_anti_unfold, h_shift_unfold, h_s_eq]
    have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by
      have := h_clz_le_63; omega
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- Step 5d: combine h_addback_eq + h_carry_eq_one + h_norm_b → h_addback.
  have h_addback : val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1 + 2^256 =
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 +
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    show val256 (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').1
                (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.1
                (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.1
                (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.2.1 + 2^256 = _
    rw [← h_norm_b]
    have h := h_addback_eq
    rw [h_carry_eq_one] at h
    omega
  -- Step 6: h_qHat_eq — qHat.toNat = a/b + 1 from the closed sub-stub.
  have h_qHat_eq : qHat.toNat = a.toNat / b.toNat + 1 :=
    qHat_eq_div_plus_one_of_single_addback a b hshift_nz hborrow_orig hsem_orig hcarry_nz
  -- Step 7: h_mulsub_eq — mulsub Euclidean at val256 level.
  have h_mulsub_eq := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub_eq
  -- Step 8: h_norm_u — val256(u_norm_low4) + u4*2^256 = val256(a)*2^s.
  have h_norm_u : val256 u0 u1 u2 u3 + u4.toNat * 2^256 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    show val256 ((a.getLimbN 0) <<< shift)
                (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift))
                (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift))
                (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)) +
            ((a.getLimbN 3) >>> antiShift).toNat * 2^256 = _
    have h_anti_unfold : antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat := h_anti_eq
    have h_shift_unfold : shift = (clzResult (b.getLimbN 3)).1.toNat := h_s_eq
    rw [h_anti_unfold, h_shift_unfold, h_s_eq]
    have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by
      have := h_clz_le_63; omega
    exact EvmWord.val256_normalize_general h_clz_pos h_clz_lt_64
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  -- Step 9: combine h_mulsub_eq + h_norm_u + h_norm_b + h_qHat_eq → h_mulsub.
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
  -- Step 9: h_mulsub composition.
  -- h_norm_b'  : val256(b0'..b3') = b.toNat * 2^s.
  -- h_norm_u'  : val256(u0..u3) + u4*2^256 = a.toNat * 2^s.
  have h_norm_b' : val256 b0' b1' b2' b3' = b.toNat *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    rw [h_norm_b, hb_val]
  have h_norm_u' : val256 u0 u1 u2 u3 + u4.toNat * 2^256 = a.toNat *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    have h := h_norm_u
    rw [ha_val] at h
    exact h
  -- ms_eq: ms.2.2.2.2 = (inline mulsubN4 ...).2.2.2.2 (defeq via set ms).
  have h_ms_eq : ms.2.2.2.2 = (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2 := rfl
  have h_ms_lo_eq : (val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 :)
      = val256 (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).1
               (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.1
               (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.1
               (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.1 := rfl
  have h_mulsub : ms.2.2.2.2.toNat * 2^256 +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) - u4.toNat * 2^256) =
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 +
        (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 1) *
          (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
            2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) := by
    rw [ha_val, hb_val, h_ms_eq, h_ms_lo_eq]
    have h := h_mulsub_eq
    rw [h_qHat_eq, h_norm_b'] at h
    have h_u_val : val256 u0 u1 u2 u3 =
        a.toNat * 2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) - u4.toNat * 2^256 := by
      have h2 := h_norm_u'
      omega
    rw [h_u_val] at h
    omega
  -- Align h_amod_pow_lt's `2^s` form (no `% 64`) with the Nat lemma's expected form.
  have h_amod_pow_lt' :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) < 2 ^ 256 := by
    rw [h_s_eq]; exact h_amod_pow_lt
  -- Final composition: apply the closed Nat lemma with all 6 preconditions.
  show ms.2.2.2.2.toNat = u4.toNat + 1
  exact c3_eq_u4_plus_one_from_mulsub_addback_bounds
    (val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1)
    (val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1)
    (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3))
    (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    ((clzResult (b.getLimbN 3)).1.toNat % 64) u4.toNat ms.2.2.2.2.toNat
    h_mulsub h_addback h_u4_le h_post1_lt h_amod_pow_lt' h_u4_lt_c3

/-- **Wrapper: c3 = u4 + 1 in single-addback (irreducible-form).**

    Wraps `c3_n_eq_u4_plus_one_of_single_addback` to take its hypothesis
    in irreducible-bundle form (`algCallAddbackBeqCarry a b ≠ 0`), avoiding
    the deep let-chain elaboration cost at the call site. The conclusion
    is also stated in irreducible form for symmetry.

    Internally unfolds the irreducible defs and applies the closed sub-stub.
    Caller should provide hb3nz, hshift_nz, hborrow, hsem, and the
    irreducible-form hcarry_nz. -/
theorem algCallAddbackBeqMsC3_eq_u4_plus_one_of_single_addback
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    (algCallAddbackBeqMsC3 a b).toNat = (algCallAddbackBeqU4 a b).toNat + 1 := by
  -- Unfold the irreducible defs to get the let-chain forms.
  show _ = _
  rw [show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl,
      show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl]
  rw [algCallAddbackBeqCarry_unfold] at hcarry_nz
  exact c3_n_eq_u4_plus_one_of_single_addback a b hb3nz hshift_nz hborrow hsem hcarry_nz


/-- **Sub-stub: post1 = a%b * 2^s from c3 = u4 + 1 (pure Nat).**

    Given the closed Nat lemmas + `c3_n_eq_u4_plus_one_of_single_addback`'s
    output, this directly gives val256(post1_low4) = a%b * 2^s.

    Composition of:
    - `val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4` (closed).
    - `c3 = u4 + 1` (substituted in).

    Result: post1_val + 0*2^256 = a%b * 2^s + 0, i.e., post1_val = a%b * 2^s. -/
theorem post1_eq_mod_times_pow_s_of_c3_eq_u4_plus_one
    (post1_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) = ms_val + (a_val / b_val + 1) * (b_val * 2^s))
    (h_addback : post1_val + 2^256 = ms_val + b_val * 2^s)
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s)
    (h_c3_eq : c3 = u4 + 1) :
    post1_val = a_val % b_val * 2^s := by
  have h_id := val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    post1_val ms_val a_val b_val s u4 c3 h_mulsub h_addback h_u4_le
  -- h_id: post1_val + (u4 + 1) * 2^256 = a%b * 2^s + c3 * 2^256
  -- h_c3_eq: c3 = u4 + 1
  rw [h_c3_eq] at h_id
  omega

/-- **Pure-Nat: post1_val = a%b * 2^s from mulsub+addback Euclidean + bounds.**

    Packaged single-shot sub-stub for the call+addback BEQ MOD adapter's
    single-addback branch (PR #1253). Combines:
    - `c3_eq_u4_plus_one_from_mulsub_addback_bounds` (yields c3 = u4 + 1).
    - `post1_eq_mod_times_pow_s_of_c3_eq_u4_plus_one` (val256-level result).

    Avoids exposing the intermediate `c3 = u4 + 1` step at the call site.
    Once the Word-level bridge to the parent's let-chain is figured out, the
    parent can apply this directly to skip an entire chained `c3` derivation.

    The hypotheses are exactly the 6 preconditions for the c3-pinning lemma:
    `h_mulsub` already encodes `qHat = a/b + 1` via the `(a_val / b_val + 1)`
    factor on its RHS. -/
theorem post1_val_eq_amod_pow_s_pure_nat
    (post1_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) = ms_val + (a_val / b_val + 1) * (b_val * 2^s))
    (h_addback : post1_val + 2^256 = ms_val + b_val * 2^s)
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s)
    (h_post1_lt : post1_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256)
    (h_u4_lt_c3 : u4 < c3) :
    post1_val = a_val % b_val * 2^s := by
  have h_c3_eq := c3_eq_u4_plus_one_from_mulsub_addback_bounds
    post1_val ms_val a_val b_val s u4 c3
    h_mulsub h_addback h_u4_le h_post1_lt h_amod_pow_lt h_u4_lt_c3
  exact post1_eq_mod_times_pow_s_of_c3_eq_u4_plus_one
    post1_val ms_val a_val b_val s u4 c3 h_mulsub h_addback h_u4_le h_c3_eq

/-- **Wrapper: post1Val = a%b * 2^s in single-addback (irreducible-form)** (CLOSED).

    Given the algorithm's invariants in single-addback (carry ≠ 0), the val256
    of the first-addback post1 limbs at normalized inputs equals
    `val256(a) % val256(b) * 2^s` — i.e., the un-truncated form of the
    Knuth-style remainder.

    Stated in irreducible-bundle form (`algCallAddbackBeqPost1Val a b` =
    val256-of-post1; `algCallAddbackBeqCarry a b ≠ 0` = single-addback)
    so the call site doesn't pay the deep let-chain elaboration cost.

    Composes the 6 closed Word-level preconditions through
    `post1_val_eq_amod_pow_s_pure_nat`:
    - `algCallAddbackBeqPost1Val_lt_pow256`                    (h_post1_lt)
    - `algCallAddbackBeq_amod_pow_s_lt_pow256`                 (h_amod_pow_lt)
    - `algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat` (h_u4_lt_c3)
    - `algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s`     (h_u4_le)
    - `algCallAddbackBeq_addback_euclidean_carry_one`          (h_addback)
    - `algCallAddbackBeq_mulsub_euclidean`                     (h_mulsub) -/
theorem algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqPost1Val a b =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
  exact post1_val_eq_amod_pow_s_pure_nat
    (algCallAddbackBeqPost1Val a b)
    (algCallAddbackBeqMsLowVal a b)
    (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3))
    (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    ((clzResult (b.getLimbN 3)).1.toNat % 64)
    (algCallAddbackBeqU4 a b).toNat
    (algCallAddbackBeqMsC3 a b).toNat
    (algCallAddbackBeq_mulsub_euclidean a b hshift_nz hborrow hsem hcarry_nz)
    (algCallAddbackBeq_addback_euclidean_carry_one a b hshift_nz hcarry_nz)
    (algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s a b hshift_nz)
    (algCallAddbackBeqPost1Val_lt_pow256 a b)
    (algCallAddbackBeq_amod_pow_s_lt_pow256 a b hb3nz)
    (algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat a b hborrow)

/-- **Unified parent-form: post1Val = a%b * 2^s in single-addback** (CLOSED).

    Drop-in replacement for the parent adapter's single-addback branch:
    takes the parent's local `(64-s)`-form `addbackN4_carry … ≠ 0`
    hypothesis directly, and returns the val256 equation in the parent's
    `(64-s)`-form too. Internally chains the carry/post1Val bridges with
    the closed wrapper. -/
theorem parent_post1Val_eq_amod_pow_s_of_single_addback
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz :
      let s := (clzResult (b.getLimbN 3)).1.toNat % 64
      let b0' := (b.getLimbN 0) <<< s
      let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
      let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
      let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
      let u0 := (a.getLimbN 0) <<< s
      let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
      let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
      let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
      let u4 := (a.getLimbN 3) >>> (64 - s)
      let qHat := div128Quot u4 u3 b3'
      let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
      addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0) :
    let s := (clzResult (b.getLimbN 3)).1.toNat % 64
    let b0' := (b.getLimbN 0) <<< s
    let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
    let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
    let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
    let u0 := (a.getLimbN 0) <<< s
    let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
    let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
    let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
    let u4 := (a.getLimbN 3) >>> (64 - s)
    let qHat := div128Quot u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let post1 := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
    val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ s := by
  intro s b0' b1' b2' b3' u0 u1 u2 u3 u4 qHat ms post1
  -- Bridge hcarry_nz: parent's (64-s) carry → algCallAddbackBeqCarry a b ≠ 0.
  have h_carry_bridge := algCallAddbackBeqCarry_eq_parent_64ms_form a b hshift_nz
  simp only [] at h_carry_bridge
  have hcarry_irreducible : algCallAddbackBeqCarry a b ≠ 0 := by
    rw [h_carry_bridge]; exact hcarry_nz
  -- Apply the closed wrapper.
  have h_wrapper := algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback
    a b hb3nz hshift_nz hborrow hsem hcarry_irreducible
  -- Bridge the wrapper's irreducible-form post1Val to parent's (64-s)-form post1.
  have h_post1_bridge := algCallAddbackBeqPost1Val_eq_parent_64ms_form a b hshift_nz
  simp only [] at h_post1_bridge
  rw [h_post1_bridge] at h_wrapper
  exact h_wrapper

/-- **Sub-lemma: per-limb mod equations using irreducible Post1Limb bundles** (CLOSED).

    Drop-in for the parent adapter's single-addback branch: produces per-limb
    equations `(EvmWord.mod a b).getLimbN i = (Limb{i} >>> s) ||| (Limb{i+1} <<< (64-s))`
    using the irreducible `algCallAddbackBeqPost1Limb{0..3}` bundles, keeping
    the goal small.

    Composes:
      * `parent_post1Val_eq_amod_pow_s_of_single_addback` (val256 fact, parent shape)
      * `algCallAddbackBeqPost1Val_eq_val256_limbs` (val256 ↔ per-limb irreducibles)
      * `denorm_4limb_eq_mod_of_val256_eq_amod_pow_s` (val256 → per-limb evmWordIs) -/
theorem mod_n4_call_addback_beq_single_addback_post1_limbs_close
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    let s := (clzResult (b.getLimbN 3)).1.toNat % 64
    (EvmWord.mod a b).getLimbN 0 =
      ((algCallAddbackBeqPost1Limb0 a b) >>> s) |||
        ((algCallAddbackBeqPost1Limb1 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 1 =
      ((algCallAddbackBeqPost1Limb1 a b) >>> s) |||
        ((algCallAddbackBeqPost1Limb2 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 2 =
      ((algCallAddbackBeqPost1Limb2 a b) >>> s) |||
        ((algCallAddbackBeqPost1Limb3 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 3 =
      (algCallAddbackBeqPost1Limb3 a b) >>> s := by
  intro s
  -- Step 1: get the val256 fact.
  have h_wrapper := algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback
    a b hb3nz hshift_nz hborrow hsem hcarry_nz
  -- Step 2: rewrite val256 in terms of irreducible per-limb bundles.
  rw [algCallAddbackBeqPost1Val_eq_val256_limbs] at h_wrapper
  -- Step 3: derive bounds on s.
  have h_clz_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_s_pos : 0 < s := by show 0 < _; omega
  have h_s_lt_64 : s < 64 := by show _ < 64; omega
  -- Step 4: apply denorm_4limb to get per-limb equations.
  exact denorm_4limb_eq_mod_of_val256_eq_amod_pow_s
    (a := a) (b := b)
    (X1 := algCallAddbackBeqPost1Limb0 a b)
    (X2 := algCallAddbackBeqPost1Limb1 a b)
    (X3 := algCallAddbackBeqPost1Limb2 a b)
    (X4 := algCallAddbackBeqPost1Limb3 a b)
    h_s_pos h_s_lt_64 hb3nz h_wrapper

/-- **B.5: val256 of double-addback's second-addback equals
    `val256(a) % val256(b) * 2^s`** (CLOSED modulo 2 stubs).

    Mirrors `algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback`
    for the **double-addback** branch (carry = 0).

    **Proof structure** (matches single-addback's): direct application
    of `abPrime_val_eq_amod_pow_s_pure_nat` (B.3, CLOSED) with the 6
    closed Word-level preconditions:
    - `algCallAddbackBeqAbPrimeVal_lt_pow256`                      (h_abPrime_lt, CLOSED)
    - `algCallAddbackBeq_amod_pow_s_lt_pow256`                     (h_amod_pow_lt, CLOSED, reused)
    - `algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat`   (h_u4_lt_c3, CLOSED, reused)
    - `algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s`         (h_u4_le, CLOSED, reused)
    - `algCallAddbackBeq_addback_combined_euclidean_carry2`         (h_addback_combined, CLOSED)
    - `algCallAddbackBeq_mulsub_euclidean_double`                  (h_mulsub, CLOSED)

    Issue #1338 Phase B.5. -/
theorem algCallAddbackBeqAbPrimeVal_eq_amod_pow_s_of_double_addback
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqAbPrimeVal a b =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
  exact abPrime_val_eq_amod_pow_s_pure_nat
    (algCallAddbackBeqAbPrimeVal a b)
    (algCallAddbackBeqMsLowVal a b)
    (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3))
    (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    ((clzResult (b.getLimbN 3)).1.toNat % 64)
    (algCallAddbackBeqU4 a b).toNat
    (algCallAddbackBeqMsC3 a b).toNat
    (algCallAddbackBeq_mulsub_euclidean_double a b hshift_nz hborrow hcarry2_nz
      hsem hcarry_zero)
    (algCallAddbackBeq_addback_combined_euclidean_carry2 a b hshift_nz
      hcarry2_nz hcarry_zero)
    (algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s a b hshift_nz)
    (algCallAddbackBeqAbPrimeVal_lt_pow256 a b)
    (algCallAddbackBeq_amod_pow_s_lt_pow256 a b hb3nz)
    (algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat a b hborrow)

/-- **B.7: per-limb mod equations for double-addback** (CLOSED modulo B.5).

    Mirror of `mod_n4_call_addback_beq_single_addback_post1_limbs_close`
    for the double-addback branch (carry = 0). Composes:
      * `algCallAddbackBeqAbPrimeVal_eq_amod_pow_s_of_double_addback` (B.5, sorry)
      * `algCallAddbackBeqAbPrimeVal_eq_val256_limbs` (B.4, closed)
      * `denorm_4limb_eq_mod_of_val256_eq_amod_pow_s` (existing)

    The proof body is fully wired; closure depends only on B.5. -/
theorem mod_n4_call_addback_beq_double_addback_abPrime_limbs_close
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    let s := (clzResult (b.getLimbN 3)).1.toNat % 64
    (EvmWord.mod a b).getLimbN 0 =
      ((algCallAddbackBeqAbPrimeLimb0 a b) >>> s) |||
        ((algCallAddbackBeqAbPrimeLimb1 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 1 =
      ((algCallAddbackBeqAbPrimeLimb1 a b) >>> s) |||
        ((algCallAddbackBeqAbPrimeLimb2 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 2 =
      ((algCallAddbackBeqAbPrimeLimb2 a b) >>> s) |||
        ((algCallAddbackBeqAbPrimeLimb3 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 3 =
      (algCallAddbackBeqAbPrimeLimb3 a b) >>> s := by
  intro s
  have h_wrapper := algCallAddbackBeqAbPrimeVal_eq_amod_pow_s_of_double_addback
    a b hb3nz hshift_nz hcarry2_nz hborrow hsem hcarry_zero
  rw [algCallAddbackBeqAbPrimeVal_eq_val256_limbs] at h_wrapper
  have h_clz_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_s_pos : 0 < s := by show 0 < _; omega
  have h_s_lt_64 : s < 64 := by show _ < 64; omega
  exact denorm_4limb_eq_mod_of_val256_eq_amod_pow_s
    (a := a) (b := b)
    (X1 := algCallAddbackBeqAbPrimeLimb0 a b)
    (X2 := algCallAddbackBeqAbPrimeLimb1 a b)
    (X3 := algCallAddbackBeqAbPrimeLimb2 a b)
    (X4 := algCallAddbackBeqAbPrimeLimb3 a b)
    h_s_pos h_s_lt_64 hb3nz h_wrapper

/-- **Call+addback BEQ n=4 MOD denorm adapter** (single-addback CLOSED, double-addback SORRY).

    Stack-level adapter folding the 4 denormalized remainder slots at
    sp+32..sp+56 into `evmWordIs (sp+32) (EvmWord.mod a b)` for the
    call+addback BEQ path.

    Signature uses irreducible Un{i}Out bundles to keep the goal small
    (a previous version had a 246-line proof body wrestling with deep
    inline let-chains). The proof fans out via:
      - `algCallAddbackBeqUn{i}Out_eq_post1Limb{i}_of_single_addback`
        (folds Un{i}Out → Post1Limb{i} under hcarry ≠ 0).
      - `mod_n4_call_addback_beq_single_addback_post1_limbs_close`
        (per-limb mod equations in irreducible form).
      - `evmWordIs_sp32_limbs_eq.symm` (final fold).

    Both branches CLOSED. The double-addback branch (carry = 0) closes
    via B.5 (`mod_n4_call_addback_beq_double_addback_abPrime_limbs_close`),
    which uses the now-closed `algCallAddbackBeq_mulsub_euclidean_double`
    chain (#1338 B.1a → B.1 → B.5 → B.7 cascade). -/
theorem output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm
    (sp : Word) (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let un0Out := algCallAddbackBeqUn0Out a b
    let un1Out := algCallAddbackBeqUn1Out a b
    let un2Out := algCallAddbackBeqUn2Out a b
    let un3Out := algCallAddbackBeqUn3Out a b
    (((sp + 32) ↦ₘ ((un0Out >>> shift) ||| (un1Out <<< (64 - shift)))) **
     ((sp + 40) ↦ₘ ((un1Out >>> shift) ||| (un2Out <<< (64 - shift)))) **
     ((sp + 48) ↦ₘ ((un2Out >>> shift) ||| (un3Out <<< (64 - shift)))) **
     ((sp + 56) ↦ₘ (un3Out >>> shift))) =
    evmWordIs (sp + 32) (EvmWord.mod a b) := by
  intro shift un0Out un1Out un2Out un3Out
  by_cases hcarry : algCallAddbackBeqCarry a b = 0
  · -- Double-addback branch (carry = 0). Wired via B.5 (#1338, blocked on
    -- Knuth-B #1337) → B.7 → parent. Mirror of single-addback's structure.
    rw [show un0Out = algCallAddbackBeqAbPrimeLimb0 a b from
          algCallAddbackBeqUn0Out_eq_abPrimeLimb0_of_double_addback a b hcarry,
        show un1Out = algCallAddbackBeqAbPrimeLimb1 a b from
          algCallAddbackBeqUn1Out_eq_abPrimeLimb1_of_double_addback a b hcarry,
        show un2Out = algCallAddbackBeqAbPrimeLimb2 a b from
          algCallAddbackBeqUn2Out_eq_abPrimeLimb2_of_double_addback a b hcarry,
        show un3Out = algCallAddbackBeqAbPrimeLimb3 a b from
          algCallAddbackBeqUn3Out_eq_abPrimeLimb3_of_double_addback a b hcarry]
    have h_limbs := mod_n4_call_addback_beq_double_addback_abPrime_limbs_close
      a b hb3nz hshift_nz hcarry2_nz hborrow hsem hcarry
    simp only [] at h_limbs
    exact (evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
      h_limbs.1 h_limbs.2.1 h_limbs.2.2.1 h_limbs.2.2.2).symm
  · -- Single-addback branch: fold Un{i}Out → Post1Limb{i} via bridges.
    rw [show un0Out = algCallAddbackBeqPost1Limb0 a b from
          algCallAddbackBeqUn0Out_eq_post1Limb0_of_single_addback a b hcarry,
        show un1Out = algCallAddbackBeqPost1Limb1 a b from
          algCallAddbackBeqUn1Out_eq_post1Limb1_of_single_addback a b hcarry,
        show un2Out = algCallAddbackBeqPost1Limb2 a b from
          algCallAddbackBeqUn2Out_eq_post1Limb2_of_single_addback a b hcarry,
        show un3Out = algCallAddbackBeqPost1Limb3 a b from
          algCallAddbackBeqUn3Out_eq_post1Limb3_of_single_addback a b hcarry]
    have h_limbs := mod_n4_call_addback_beq_single_addback_post1_limbs_close
      a b hb3nz hshift_nz hborrow hsem hcarry
    simp only [] at h_limbs
    exact (evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
      h_limbs.1 h_limbs.2.1 h_limbs.2.2.1 h_limbs.2.2.2).symm

/-- **EVM-stack-level MOD spec on the n=4 call+addback BEQ sub-path.**

    Mirror of `evm_div_n4_call_addback_beq_stack_spec` for MOD. Composes
    the closed `output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm`
    adapter (above) with the runtime + memory bookkeeping from
    `evm_mod_n4_full_call_addback_beq_stack_pre_spec_bundled`. Mirrors
    the template from `evm_mod_n4_call_skip_stack_spec` (landed in #1207). -/
theorem evm_mod_n4_call_addback_beq_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  have h_pre := evm_mod_n4_full_call_addback_beq_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  have hshift_le_63 := clzResult_fst_toNat_le (b.getLimbN 3)
  have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    by_contra h
    push Not at h
    apply hshift_nz
    apply BitVec.eq_of_toNat_eq
    rw [show (0 : Word).toNat = 0 from rfl]; omega
  have hmod_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have h0se12 : signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1 =
      -((clzResult (b.getLimbN 3)).1) := by rw [signExtend12_0]; simp
  have hanti_toNat_mod :
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat := by
    rw [h0se12, BitVec.toNat_neg]
    have : ((clzResult (b.getLimbN 3)).1).toNat ≤ 2^64 := by
      have := ((clzResult (b.getLimbN 3)).1).isLt; omega
    omega
  have h_slot := output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm sp a b
    hb3nz hshift_nz hcarry2_nz hborrow hsem
  refine cpsTriple_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullModN4CallAddbackBeqPost_unfold, denormModPost_unfold] at hq
  -- Fold hq's inline un{i}Out forms to the irreducible Un{i}Out names
  -- (matching the parent adapter's new signature).
  simp only [← algCallAddbackBeqUn0Out_unfold, ← algCallAddbackBeqUn1Out_unfold,
             ← algCallAddbackBeqUn2Out_unfold, ← algCallAddbackBeqUn3Out_unfold] at hq
  apply mod_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.mod a b) = _ from h_slot.symm]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  simp only [hmod_eq, hanti_toNat_mod] at hq ⊢
  xperm_hyp hq

/-- **n=4 shift_nz DIV top-level dispatcher** — routes between
    call+skip (unconditional, hsem auto-discharged) and call+addback
    BEQ paths via the borrow-check disjunction.

    Mirror of `evm_div_n4_shift0_stack_spec` (Shift0Dispatcher.lean) but
    for the shift_nz path. Uses
    `isSkipBorrowN4CallEvm_or_isAddbackBorrowN4CallEvm` as the case-split
    and `evm_div_n4_call_skip_stack_spec_unconditional` (which
    auto-discharges `n4CallSkipSemanticHolds`) for the skip path.

    The addback-BEQ path still requires its own `hsem`
    (`n4CallAddbackBeqSemanticHolds`) and `hcarry2_nz` — these encode
    Knuth-B + addback correctness which haven't been closed yet
    (parked behind PR #1339's bridge stub). -/
theorem evm_div_n4_call_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz_addback :
      isAddbackBorrowN4CallEvm a b → isAddbackCarry2NzN4CallEvm a b)
    (hsem_addback :
      isAddbackBorrowN4CallEvm a b → n4CallAddbackBeqSemanticHolds a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  rcases isSkipBorrowN4CallEvm_or_isAddbackBorrowN4CallEvm a b with hskip | haddback
  · exact evm_div_n4_call_skip_stack_spec_unconditional sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_nz halign hbltu hskip
  · exact evm_div_n4_call_addback_beq_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_nz hvalid halign hbltu
      (hcarry2_nz_addback haddback) haddback (hsem_addback haddback)

/-- **n=4 shift_nz MOD top-level dispatcher** — mirror of
    `evm_div_n4_call_stack_spec` for MOD. Routes between
    call+skip (auto-discharged) and call+addback BEQ paths.

    Note: MOD's call-addback-beq spec doesn't take `hvalid` (unlike
    DIV's), so the MOD dispatcher's signature is one parameter shorter. -/
theorem evm_mod_n4_call_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz_addback :
      isAddbackBorrowN4CallEvm a b → isAddbackCarry2NzN4CallEvm a b)
    (hsem_addback :
      isAddbackBorrowN4CallEvm a b → n4CallAddbackBeqSemanticHolds a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  rcases isSkipBorrowN4CallEvm_or_isAddbackBorrowN4CallEvm a b with hskip | haddback
  · exact evm_mod_n4_call_skip_stack_spec_unconditional sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_nz halign hbltu hskip
  · exact evm_mod_n4_call_addback_beq_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_nz halign hbltu
      (hcarry2_nz_addback haddback) haddback (hsem_addback haddback)

/-- **n=4 top-level DIV stack spec — fully shift-agnostic** (CLOSED for
    skip path; addback hypotheses gated on `isAddbackBorrowN4CallEvm`).

    Top-level dispatcher that case-splits on whether `b3` is already
    normalized (shift = 0) vs. needs CLZ shift (shift ≠ 0):
    - `(clzResult b3).1 = 0` → routes to `evm_div_n4_shift0_stack_spec`
      (fully unconditional under runtime conditions).
    - `(clzResult b3).1 ≠ 0` → routes to `evm_div_n4_call_stack_spec`
      (shift_nz dispatcher; skip path unconditional, addback path
      requires its own hsem/hcarry2_nz under `isAddbackBorrowN4CallEvm`).

    The shift0 path is fully closed; only the shift_nz call-addback
    case retains the Knuth-B-gated hypotheses. -/
theorem evm_div_n4_call_stack_spec_full (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : (clzResult (b.getLimbN 3)).1 ≠ 0 → isCallTrialN4Evm a b)
    (hcarry2_nz_addback :
      (clzResult (b.getLimbN 3)).1 ≠ 0 →
      isAddbackBorrowN4CallEvm a b → isAddbackCarry2NzN4CallEvm a b)
    (hsem_addback :
      (clzResult (b.getLimbN 3)).1 ≠ 0 →
      isAddbackBorrowN4CallEvm a b → n4CallAddbackBeqSemanticHolds a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  by_cases hshift_z : (clzResult (b.getLimbN 3)).1 = 0
  · exact evm_div_n4_shift0_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_z halign
  · exact evm_div_n4_call_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_z hvalid halign (hbltu hshift_z)
      (hcarry2_nz_addback hshift_z) (hsem_addback hshift_z)

/-- **n=4 top-level MOD stack spec — fully shift-agnostic** (CLOSED for
    skip path; addback hypotheses gated). Mirror of
    `evm_div_n4_call_stack_spec_full` for MOD.

    Note: MOD's call-addback-beq spec doesn't take `hvalid`, so the
    MOD top-level dispatcher's signature is one parameter shorter. -/
theorem evm_mod_n4_call_stack_spec_full (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : (clzResult (b.getLimbN 3)).1 ≠ 0 → isCallTrialN4Evm a b)
    (hcarry2_nz_addback :
      (clzResult (b.getLimbN 3)).1 ≠ 0 →
      isAddbackBorrowN4CallEvm a b → isAddbackCarry2NzN4CallEvm a b)
    (hsem_addback :
      (clzResult (b.getLimbN 3)).1 ≠ 0 →
      isAddbackBorrowN4CallEvm a b → n4CallAddbackBeqSemanticHolds a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  by_cases hshift_z : (clzResult (b.getLimbN 3)).1 = 0
  · exact evm_mod_n4_shift0_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_z halign
  · exact evm_mod_n4_call_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_z halign (hbltu hshift_z)
      (hcarry2_nz_addback hshift_z) (hsem_addback hshift_z)


end EvmAsm.Evm64
