/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryEntryBody

  Non-fixed full-loop boundary spec, composed down to the single remaining
  loop-entry bridge.

  This wires the concrete 256-iteration loop-body spec
  `exp_loop_from_looppost_full_body_general_spec_within` (the `hBody`
  continuation, instantiated at `n = 256`) into the generic boundary
  composition `exp_two_mul_full_loop_boundary_of_entry_body_general_spec_within`.
  Specialising the abstract precondition `P` to
  `expTwoMulIterLoopPost (256 : Word) ...` leaves only the loop-entry bridge
  `expTwoMulLoopEntryPost → expTwoMulIterLoopPost 256` as a hypothesis.  The
  result is the full prologue→loop→epilogue boundary triple for the non-fixed
  (`TwoMul`) path, reduced to that one assertion-level implication plus the
  final-iteration exit bridge `hExitUniv`.

  Bead evm-asm-w5mk.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBodyFromLoopPost

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Full non-fixed EXP loop boundary spec, reduced to the loop-entry bridge.

    Composes the proven 256-iteration loop-body spec
    (`exp_loop_from_looppost_full_body_general_spec_within`) with the generic
    boundary scaffold, taking the abstract body precondition `P` to be the
    concrete loop-back post `expTwoMulIterLoopPost (256 : Word) ...`.  The only
    remaining proof obligations are:

    - `hEntry`: the loop-entry bridge — the prologue's loop-entry post implies
      the 256-counter loop-back post (a pure assertion-level implication at the
      loop head `base + 28`, with no code executed);
    - `hExitUniv`: the final-iteration exit bridge from
      `expTwoMulIterExitPost 0 ...` into the generalized full-stack loop-exit
      pre-frame;
    - `hbase`: the code-base alignment invariant `base &&& 1 = 0`.

    The conclusion is the complete boundary triple from `expTwoMulBoundaryPre`
    (prologue entry state) to `expTwoMulLoopExitPost` (loop-exit post state),
    spanning `base .. base + 304`. -/
theorem exp_two_mul_full_loop_boundary_of_entry_general_spec_within
    (bit sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (iterCountFinal out0 out1 out2 out3 d0 d1 d2 d3 a0 a1 a2 a3 : Word)
    (baseWord exponentWord : EvmWord) (squarW rwW : EvmWord)
    (rest : List EvmWord) (exitCond : Prop) (base : Word)
    (hbase : base &&& 1 = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest hp →
        expTwoMulIterLoopPost (256 : Word) bit sp evmSp base a0 a1 a2 a3
          squarW rwW hp)
    (hExitUniv : ∀ (bit0 : Word) (squarW0 rwW0 : EvmWord) (ps : PartialState),
        expTwoMulIterExitPost 0 bit0 sp evmSp base a0 a1 a2 a3 squarW0 rwW0 ps →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
          out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond ps) :
    cpsTripleWithin expTwoMulFullLoopBoundaryBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountFinal out0 out1 out2 out3
        baseWord rest exitCond) :=
  exp_two_mul_full_loop_boundary_of_entry_body_general_spec_within
    sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountFinal
    out0 out1 out2 out3 d0 d1 d2 d3 baseWord exponentWord rest exitCond base
    hEntry
    (exp_loop_from_looppost_full_body_general_spec_within
      bit sp evmSp base a0 a1 a2 a3 squarW rwW hbase
      iterCountFinal tOld out0 out1 out2 out3 d0 d1 d2 d3
      baseWord rest exitCond hExitUniv)

/-- Closed-form bound variant of
    `exp_two_mul_full_loop_boundary_of_entry_general_spec_within`.

    Exposes the boundary triple with the literal step count
    `48401 = expTwoMulFullLoopBoundaryBound`, for downstream `progAt`-style
    consumers that match on a concrete numeral rather than the named bound. -/
theorem exp_two_mul_full_loop_boundary_of_entry_general_closed_bound_spec_within
    (bit sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (iterCountFinal out0 out1 out2 out3 d0 d1 d2 d3 a0 a1 a2 a3 : Word)
    (baseWord exponentWord : EvmWord) (squarW rwW : EvmWord)
    (rest : List EvmWord) (exitCond : Prop) (base : Word)
    (hbase : base &&& 1 = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest hp →
        expTwoMulIterLoopPost (256 : Word) bit sp evmSp base a0 a1 a2 a3
          squarW rwW hp)
    (hExitUniv : ∀ (bit0 : Word) (squarW0 rwW0 : EvmWord) (ps : PartialState),
        expTwoMulIterExitPost 0 bit0 sp evmSp base a0 a1 a2 a3 squarW0 rwW0 ps →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
          out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond ps) :
    cpsTripleWithin 48401 base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountFinal out0 out1 out2 out3
        baseWord rest exitCond) := by
  rw [← expTwoMulFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_full_loop_boundary_of_entry_general_spec_within
      bit sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountFinal
      out0 out1 out2 out3 d0 d1 d2 d3 a0 a1 a2 a3
      baseWord exponentWord squarW rwW rest exitCond base hbase hEntry hExitUniv

end EvmAsm.Evm64.Exp.Compose
