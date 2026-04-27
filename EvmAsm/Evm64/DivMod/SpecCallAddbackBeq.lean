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

    **Implication**: this theorem proves that
    `n4CallAddbackBeqSemanticHolds_of_*` (any closure from runtime
    conditions) cannot exist — the predicate is genuinely false on
    runtime-reachable inputs. The user-facing
    `evm_div_n4_full_call_addback_beq_stack_pre_spec` and its
    relatives have a vacuous semantic correctness bridge for this
    input class, until the algorithm is fixed (see
    `memory/project_knuth_d_one_correction_design.md`). -/
theorem n4CallAddbackBeqSemanticHolds_counterexample :
    ¬ (n4CallAddbackBeqSemanticHolds
        (EvmWord.fromLimbs (fun i => match i with
          | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33)))
        (EvmWord.fromLimbs (fun i => match i with
          | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1))) := by
  unfold n4CallAddbackBeqSemanticHolds
  decide

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
