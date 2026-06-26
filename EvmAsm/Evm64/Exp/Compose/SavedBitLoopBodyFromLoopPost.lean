/-
  EvmAsm.Evm64.Exp.Compose.SavedBitLoopBodyFromLoopPost

  Concrete 256-iteration instantiation of the abstract loop-body induction
  `exp_loop_from_looppost_induction_general`.

  This wraps the abstract `n`-step induction at `n = 256`, producing a body
  spec at the named `expTwoMulFullLoopBodyBound` step count.  The resulting
  shape (start `expTwoMulIterLoopPost (256 : Word) ...`, exit
  `expTwoMulLoopExitFullStackPreFrame ...`, code/offsets
  `evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base` from `base + 28` to
  `base + 264`) is exactly the `hBody` continuation consumed by the non-fixed
  boundary composition `exp_two_mul_full_loop_boundary_of_entry_body_general_spec_within`,
  once the loop-entry bridge `expTwoMulLoopEntryPost → expTwoMulIterLoopPost 256`
  is available.

  Bead evm-asm-w5mk.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBodyInd

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- `(256 : Word) ≠ 0`. -/
private theorem word256_ne_zero : (256 : Word) ≠ 0 := by decide

/-- `(256 : Word).toNat = 256`. -/
private theorem word256_toNat : (256 : Word).toNat = 256 := by decide

/-- Concrete 256-iteration loop-body spec from `expTwoMulIterLoopPost`.

    Instantiates `exp_loop_from_looppost_induction_general` at `n = 256` and
    rewrites the `256 * 189` step count to the named
    `expTwoMulFullLoopBodyBound`.  This is the `hBody`-shaped continuation the
    non-fixed boundary composition expects: it runs the full 256-iteration
    square-and-multiply loop from the loop-back post-state of the (notional)
    zeroth iteration to the generalized full-stack loop-exit pre-frame.

    The caller still supplies:
    - `hbase`: the code-base alignment invariant `base &&& 1 = 0`;
    - `hExitUniv`: the final-iteration exit bridge
      (`expTwoMulIterExitPost 0 ... → expTwoMulLoopExitFullStackPreFrame ...`). -/
theorem exp_loop_from_looppost_full_body_general_spec_within
    (bit sp evmSp base a0 a1 a2 a3 : Word)
    (squarW rwW : EvmWord)
    (hbase : base &&& 1 = 0)
    (iterCountFinal tOld out0 out1 out2 out3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hExitUniv : ∀ (bit0 : Word) (squarW0 rwW0 : EvmWord) (ps : PartialState),
        expTwoMulIterExitPost 0 bit0 sp evmSp base a0 a1 a2 a3 squarW0 rwW0 ps →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
          out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond ps) :
    cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (256 : Word) bit sp evmSp base a0 a1 a2 a3
        squarW rwW)
      (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
        out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond) := by
  rw [show expTwoMulFullLoopBodyBound = 256 * 189 from
    expTwoMulIterationsBodyBound_eq 256]
  exact
    exp_loop_from_looppost_induction_general 256
      bit sp evmSp base a0 a1 a2 a3 squarW rwW
      (256 : Word) word256_ne_zero word256_toNat hbase
      iterCountFinal tOld out0 out1 out2 out3 d0 d1 d2 d3
      baseWord rest exitCond hExitUniv

end EvmAsm.Evm64.Exp.Compose
