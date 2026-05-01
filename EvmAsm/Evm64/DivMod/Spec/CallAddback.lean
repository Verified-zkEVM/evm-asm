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
  - Word-level Euclideans (mulsub, addback) and val256 bounds.
  - Word-level wrappers (post1_val_eq_amod_pow_s_of_single_addback,
    abPrime_val_eq_amod_pow_s_of_double_addback).
  - Adapter / parent + final stack specs.
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

/-- **Pure-Nat helper for conj2 of `_no_wrap_under_call_addback_beq_untruncated`.**

    Given the Phase-1 Euclidean (`q1'' * dHi + rhat'' = uHi`) and
    Knuth-A v2 (`q1'' ≥ (uHi*2^32 + div_un1) / vTop`) at the Nat level,
    derives the untruncated phase-1 upper-bound conjunct:
    `rhat'' * 2^32 + div_un1 - q1'' * dLo < 2^64`.

    No Word reasoning — this is the algebraic combiner that the parent
    stub's conj2 case will invoke once Knuth-A is closed. -/
private theorem conj2_arith
    (uHi div_un1 q1pp rhat_pp dHi dLo : ℕ)
    (h_eucl : q1pp * dHi + rhat_pp = uHi)
    (h_dHi_lt : dHi < 2^32)
    (h_dLo_lt : dLo < 2^32)
    (h_dHi_ge : dHi ≥ 2^31)
    (h_knuthA : q1pp ≥ (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo)) :
    rhat_pp * 2^32 + div_un1 - q1pp * dLo < 2^64 := by
  have h_vTop_pos : 0 < dHi * 2^32 + dLo := by
    have h1 : dHi * 2^32 ≥ 2^31 * 2^32 := Nat.mul_le_mul_right _ h_dHi_ge
    have h_pow : (2 ^ 31 * 2 ^ 32 : ℕ) = 2 ^ 63 := by decide
    omega
  have h_vTop_lt_pow64 : dHi * 2^32 + dLo < 2^64 := by
    have h1 : dHi * 2^32 ≤ (2^32 - 1) * 2^32 :=
      Nat.mul_le_mul_right _ (by omega : dHi ≤ 2^32 - 1)
    have h_pow : ((2^32 - 1) * 2^32 + (2^32 - 1) : ℕ) = 2^64 - 1 := by decide
    omega
  rcases Nat.lt_or_ge (rhat_pp * 2^32 + div_un1) (q1pp * dLo) with h_neg | h_nonneg
  · have h_zero : rhat_pp * 2^32 + div_un1 - q1pp * dLo = 0 := by omega
    rw [h_zero]; decide
  · have h_q1pp_dHi_le : q1pp * dHi ≤ uHi := by linarith [h_eucl]
    have h_q1pp_dHi_2pow32_le : q1pp * dHi * 2^32 ≤ uHi * 2^32 :=
      Nat.mul_le_mul_right _ h_q1pp_dHi_le
    have h_rhat_2pow32 : rhat_pp * 2^32 = uHi * 2^32 - q1pp * dHi * 2^32 := by
      have h_rhat_eq : rhat_pp = uHi - q1pp * dHi := by omega
      rw [h_rhat_eq, Nat.sub_mul]
    have h_q1pp_vTop : q1pp * (dHi * 2^32 + dLo) = q1pp * dHi * 2^32 + q1pp * dLo := by
      ring
    have h_lhs_eq :
        rhat_pp * 2^32 + div_un1 - q1pp * dLo =
        uHi * 2^32 + div_un1 - q1pp * (dHi * 2^32 + dLo) := by omega
    rw [h_lhs_eq]
    have h_div_mul :
        (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo) * (dHi * 2^32 + dLo) ≤
        q1pp * (dHi * 2^32 + dLo) :=
      Nat.mul_le_mul_right _ h_knuthA
    have h_div_add_mod :
        uHi * 2^32 + div_un1 =
        (dHi * 2^32 + dLo) * ((uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo)) +
        (uHi * 2^32 + div_un1) % (dHi * 2^32 + dLo) :=
      (Nat.div_add_mod _ _).symm
    have h_mod_lt :
        (uHi * 2^32 + div_un1) % (dHi * 2^32 + dLo) < dHi * 2^32 + dLo :=
      Nat.mod_lt _ h_vTop_pos
    have h_div_mul' :
        (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo) * (dHi * 2^32 + dLo) =
        (dHi * 2^32 + dLo) * ((uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo)) :=
      Nat.mul_comm _ _
    omega

/-- **Strengthened version of `conj2_arith`** — same hypotheses, but
    bounds the untruncated subtraction by `vTop` instead of `2^64`.
    Same algebraic argument, just keeps the tighter bound.

    The conclusion `(rhat'' * 2^32 + div_un1) - q1'' * dLo < vTop` is
    what the un21 < vTop bridge needs (combined with `_un21_toNat_untruncated`
    to convert from the untruncated form to the Word un21.toNat). -/
private theorem un21_lt_vTop_arith
    (uHi div_un1 q1pp rhat_pp dHi dLo : ℕ)
    (h_eucl : q1pp * dHi + rhat_pp = uHi)
    (h_dHi_lt : dHi < 2^32)
    (h_dLo_lt : dLo < 2^32)
    (h_dHi_ge : dHi ≥ 2^31)
    (h_knuthA : q1pp ≥ (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo)) :
    rhat_pp * 2^32 + div_un1 - q1pp * dLo < dHi * 2^32 + dLo := by
  have h_vTop_pos : 0 < dHi * 2^32 + dLo := by
    have h1 : dHi * 2^32 ≥ 2^31 * 2^32 := Nat.mul_le_mul_right _ h_dHi_ge
    have h_pow : (2 ^ 31 * 2 ^ 32 : ℕ) = 2 ^ 63 := by decide
    omega
  rcases Nat.lt_or_ge (rhat_pp * 2^32 + div_un1) (q1pp * dLo) with h_neg | h_nonneg
  · have h_zero : rhat_pp * 2^32 + div_un1 - q1pp * dLo = 0 := by omega
    rw [h_zero]; exact h_vTop_pos
  · have h_q1pp_dHi_le : q1pp * dHi ≤ uHi := by linarith [h_eucl]
    have h_q1pp_dHi_2pow32_le : q1pp * dHi * 2^32 ≤ uHi * 2^32 :=
      Nat.mul_le_mul_right _ h_q1pp_dHi_le
    have h_rhat_2pow32 : rhat_pp * 2^32 = uHi * 2^32 - q1pp * dHi * 2^32 := by
      have h_rhat_eq : rhat_pp = uHi - q1pp * dHi := by omega
      rw [h_rhat_eq, Nat.sub_mul]
    have h_q1pp_vTop : q1pp * (dHi * 2^32 + dLo) = q1pp * dHi * 2^32 + q1pp * dLo := by
      ring
    have h_lhs_eq :
        rhat_pp * 2^32 + div_un1 - q1pp * dLo =
        uHi * 2^32 + div_un1 - q1pp * (dHi * 2^32 + dLo) := by omega
    rw [h_lhs_eq]
    have h_div_mul :
        (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo) * (dHi * 2^32 + dLo) ≤
        q1pp * (dHi * 2^32 + dLo) :=
      Nat.mul_le_mul_right _ h_knuthA
    have h_div_add_mod :
        uHi * 2^32 + div_un1 =
        (dHi * 2^32 + dLo) * ((uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo)) +
        (uHi * 2^32 + div_un1) % (dHi * 2^32 + dLo) :=
      (Nat.div_add_mod _ _).symm
    have h_mod_lt :
        (uHi * 2^32 + div_un1) % (dHi * 2^32 + dLo) < dHi * 2^32 + dLo :=
      Nat.mod_lt _ h_vTop_pos
    have h_div_mul' :
        (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo) * (dHi * 2^32 + dLo) =
        (dHi * 2^32 + dLo) * ((uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo)) :=
      Nat.mul_comm _ _
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

end EvmAsm.Evm64
