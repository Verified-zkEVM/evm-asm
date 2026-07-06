/-
  EvmAsm.Evm64.Exp.Compose.SavedBitPrologueBodyCompose

  Non-fixed prologue + entry-bridge + 256-iteration body, composed into a single
  spec from the boundary entry state `expTwoMulBoundaryPre` to the loop-exit
  full-stack pre-frame (plus the residual exponent/stack frame).

  Chain:
    prologue   (base .. base+28)   BoundaryPre        -> loopEntryPost
    bridge     (assertion-level)   loopEntryPost      -> iterPre ** residual
    body       (base+28 .. base+264) iterPre ** residual -> exit ** residual

  This is the `cpsTriple` glue (step 2) for landing the non-fixed EXP loop:
  prologue via `..._named_boundary_closed_bound`, the loop-entry bridge
  `expTwoMulLoopEntryPost_to_iterPre_frame`, and the loop-entry body spec
  `exp_loop_from_iterpre_full_body_general_spec_within`.

  Bead evm-asm-w5mk.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitEntryIterPreBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBodyInd

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Prologue + bridge + 256-iteration body composed (non-fixed / two-MUL).

    From the boundary entry state `expTwoMulBoundaryPre` (with the stack carrying
    the two scratch words `dWord`, `eWord` below the operands), running the
    prologue and the full 256-iteration square-and-multiply loop reaches the
    loop-exit full-stack pre-frame, with the live exponent word and deeper stack
    carried alongside as the residual frame.

    The caller supplies `hbase` (code-base alignment) and `hExitUniv` (the
    final-iteration exit bridge into the chosen exit payload). -/
theorem exp_two_mul_prologue_body_compose_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (base : Word) (hbase : base &&& 1 = 0)
    (iterCountFinal tExit out0 out1 out2 out3 d0 d1 d2 d3 : Word)
    (baseWordExit : EvmWord) (restExit : List EvmWord) (exitCond : Prop)
    (hExitUniv : ∀ (bit0 : Word) (squarW0 rwW0 : EvmWord) (ps : PartialState),
        expTwoMulIterExitPost 0 bit0 sp (evmSp + 64) base
          (baseWord.getLimbN 0) (baseWord.getLimbN 1)
          (baseWord.getLimbN 2) (baseWord.getLimbN 3)
          squarW0 rwW0 ps →
        expTwoMulLoopExitFullStackPreFrame sp (evmSp + 64) iterCountFinal tExit
          out0 out1 out2 out3 d0 d1 d2 d3 baseWordExit restExit exitCond ps) :
    cpsTripleWithin (7 + 256 * 189) base (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp + 64) iterCountFinal tExit
        out0 out1 out2 out3 d0 d1 d2 d3 baseWordExit restExit exitCond **
       expTwoMulEntryIterPreResidual evmSp exponentWord rest) := by
  -- Prologue: BoundaryPre -> loopEntryPost (base .. base+28).
  have hPro :=
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_closed_bound_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
      baseWord exponentWord (dWord :: eWord :: rest) base
  -- Weaken the prologue's post into (iterPre ** residual) via the entry bridge.
  have hPro' :
      cpsTripleWithin 7 base (base + 28)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
          baseWord exponentWord (dWord :: eWord :: rest))
        (expTwoMulIterPre (1 : Word) (256 : Word) v18 sp (evmSp + 64) vOld
            ((1 : EvmWord).getLimbN 0) ((1 : EvmWord).getLimbN 1)
            ((1 : EvmWord).getLimbN 2) ((1 : EvmWord).getLimbN 3)
            (dWord.getLimbN 0) (dWord.getLimbN 1) (dWord.getLimbN 2) (dWord.getLimbN 3)
            (eWord.getLimbN 0) (eWord.getLimbN 1) (eWord.getLimbN 2) (eWord.getLimbN 3)
            (baseWord.getLimbN 0) (baseWord.getLimbN 1)
            (baseWord.getLimbN 2) (baseWord.getLimbN 3) **
         expTwoMulEntryIterPreResidual evmSp exponentWord rest) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => expTwoMulLoopEntryPost_to_iterPre_frame hq) hPro
  -- Body: iterPre -> exit (base+28 .. base+264), framed by the residual.
  have hBody :=
    exp_loop_from_iterpre_full_body_general_spec_within
      (1 : Word) v18 sp (evmSp + 64) vOld
      ((1 : EvmWord).getLimbN 0) ((1 : EvmWord).getLimbN 1)
      ((1 : EvmWord).getLimbN 2) ((1 : EvmWord).getLimbN 3)
      (dWord.getLimbN 0) (dWord.getLimbN 1) (dWord.getLimbN 2) (dWord.getLimbN 3)
      (eWord.getLimbN 0) (eWord.getLimbN 1) (eWord.getLimbN 2) (eWord.getLimbN 3)
      (baseWord.getLimbN 0) (baseWord.getLimbN 1)
      (baseWord.getLimbN 2) (baseWord.getLimbN 3)
      base hbase iterCountFinal tExit out0 out1 out2 out3 d0 d1 d2 d3
      baseWordExit restExit exitCond hExitUniv
  have hBodyF :=
    cpsTripleWithin_frameR (expTwoMulEntryIterPreResidual evmSp exponentWord rest)
      expTwoMulEntryIterPreResidual_pcFree hBody
  exact cpsTripleWithin_seq_same_cr hPro' hBodyF

end EvmAsm.Evm64.Exp.Compose
