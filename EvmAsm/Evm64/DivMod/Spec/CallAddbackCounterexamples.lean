/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackCounterexamples

  Numerical counterexample / fix-verification block for the
  call+addback-BEQ semantic predicate, plus the v2 mirror predicate
  `n4CallAddbackBeqSemanticHolds_v2` and its sanity check.

  These theorems are documentation-only: nothing in the rest of the
  proof corpus depends on them as Lean expressions (they are only
  cross-referenced from docstrings). Extracted from
  `EvmAsm/Evm64/DivMod/Spec/CallAddback.lean` (issue #1078) to chip
  away at that file's 1500-line cap exception. See evm-asm-ry8 (parent
  beads task) and evm-asm-b5i (this sub-slice).

  Contents:
  - `n4CallAddbackBeqSemanticHolds_counterexample` — v1 predicate is FALSE
    on a concrete runtime-reachable input (overshoot-by-2^32-2 case).
  - `div128Quot_v2_fixes_counterexample` — v2 algorithm produces the
    correct quotient on the same input.
  - `div128Quot_buggy_on_counterexample` — companion bug confirmation
    for the v1 algorithm.
  - `n4CallAddbackBeqSemanticHolds_v2` — v2 mirror predicate definition.
  - `n4CallAddbackBeqSemanticHolds_v2_holds_on_counterexample` — v2 mirror
    predicate holds on the v1-counterexample input.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddback

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

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

end EvmAsm.Evm64
