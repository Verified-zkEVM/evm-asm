/-
  EvmAsm.Evm64.DivMod.SpecCallV4

  v4 versions of the call-trial semantic predicates:
  - `n4CallSkipSemanticHolds_v4` (mirror of `n4CallSkipSemanticHolds` with
    `div128Quot_v4` in place of `div128Quot`)
  - `n4CallAddbackBeqSemanticHolds_v4` (mirror of
    `n4CallAddbackBeqSemanticHolds` with `div128Quot_v4`)

  The v4 predicates are downstream of `IterV4InvariantsPhase2` (zero
  sorries on PR #1409, currently in review). They are the entry point
  for the v4 stack-spec dispatcher work tracked under issue #1337
  → issue #61.

  Companion to `SpecCall.lean` (defines v1 versions) and
  `SpecCallAddbackBeq.lean` (defines v1 + v2 versions).
-/

import EvmAsm.Evm64.DivMod.SpecCall
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq
import EvmAsm.Evm64.DivMod.LoopDefs.IterV4
import EvmAsm.Evm64.DivMod.LoopDefs.IterV4InvariantsPhase2

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- **v4 version of `n4CallSkipSemanticHolds`**, using `div128Quot_v4`
    (full 2-correction Knuth D3 in BOTH phases).

    Mirror of `n4CallSkipSemanticHolds` for the v4 algorithm. Used by
    downstream stack specs once they migrate from `div128Quot`/`div128Quot_v2`
    to `div128Quot_v4`. The associated closure
    `n4CallSkipSemanticHolds_v4_of_call_trial` is provable since v4
    satisfies `qHat ≥ q_true` (Knuth-A lower bound; trivially under
    perfect Phase-1+2). -/
def n4CallSkipSemanticHolds_v4 (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
    (div128Quot_v4 u4 u3 b3').toNat

theorem n4CallSkipSemanticHolds_v4_def {a b : EvmWord} :
    n4CallSkipSemanticHolds_v4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
       (div128Quot_v4 u4 u3 b3').toNat) :=
  rfl

/-- **v4 version of `n4CallAddbackBeqSemanticHolds`**, using
    `div128Quot_v4` (full 2-correction Knuth D3 in BOTH phases).

    The v1 predicate `n4CallAddbackBeqSemanticHolds` is **provably FALSE**
    under runtime preconditions (see
    `n4CallAddbackBeqSemanticHolds_counterexample`) due to v1's
    1-correction Phase-1b allowing 2^32-scale qHat overshoots. The v2
    predicate fixes Phase-1b only; the v4 predicate fixes BOTH phases,
    eliminating the counterexample input class by construction.

    Mirror of `n4CallAddbackBeqSemanticHolds` for the v4 algorithm.
    Closure proof `n4CallAddbackBeqSemanticHolds_v4_of_call_addback_beq`
    is the next critical-path target (still in stub form). -/
def n4CallAddbackBeqSemanticHolds_v4 (a b : EvmWord) : Prop :=
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
  let qHat := div128Quot_v4 u4 u3 b3'  -- v4: 2 D3 correction iterations in BOTH phases.
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let q_out : Word :=
    if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
    else qHat + signExtend12 4095
  q_out.toNat =
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem n4CallAddbackBeqSemanticHolds_v4_def {a b : EvmWord} :
    n4CallAddbackBeqSemanticHolds_v4 a b =
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
     let qHat := div128Quot_v4 u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     let q_out : Word :=
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095
     q_out.toNat =
       val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl

/-- **`n4CallAddbackBeqSemanticHolds_v4` closure stub**: under the runtime
    call-addback-BEQ preconditions, the v4 predicate holds. To be proven
    via the val256-level Knuth chain plus the now-closed Phase-2 invariants
    (esp. `div128Quot_v4_phase2_no_wrap_lo` and `div128Quot_v4_phase2_perfect`).

    Stub for the next critical-path iteration. The proof structure
    (per `project_addback_beq_closure_plan_v2.md`):
    - Layer 1: Knuth-B (`qHat ≤ q_true + 2`) — likely closeable now via
      Phase-1 perfect (`div128Quot_v4_phase1_perfect`).
    - Layer 2: carry partition (carry=0 ⟺ qHat=q_true+2) — closeable via
      Phase-2 perfect.
    - Layer 3: q_out arithmetic (carry=0: q_out = qHat-2 = q_true;
      carry≠0: q_out = qHat-1 = q_true).

    This stub exposes the proof obligation so downstream stack specs
    can wire through. -/
theorem n4CallAddbackBeqSemanticHolds_v4_of_call_addback_beq (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hcall : isCallTrialN4Evm a b) :
    n4CallAddbackBeqSemanticHolds_v4 a b := by
  sorry  -- Closure of the v4 predicate. See docstring for proof plan.

end EvmAsm.Evm64
