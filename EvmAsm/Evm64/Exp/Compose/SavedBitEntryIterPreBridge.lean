/-
  EvmAsm.Evm64.Exp.Compose.SavedBitEntryIterPreBridge

  Non-fixed loop-entry bridge: the prologue's `expTwoMulLoopEntryPost` implies
  the first-iteration loop-entry precondition `expTwoMulIterPre` (counter 256),
  plus a residual frame holding the live exponent word and the deeper stack.

  This is the separation-logic reshuffle that connects the prologue to the
  256-iteration body spec `exp_loop_from_iterpre_full_body_general_spec_within`.
  It is the non-fixed analog of `expTwoMulLoopEntryPostFixed_to_firstIterPre`.

  Bead evm-asm-w5mk.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitLoopEntry
import EvmAsm.Evm64.Exp.Compose.SavedBitIterPostDefs

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Residual resources left over after `expTwoMulIterPre` consumes the
    accumulator, base word, and the two scratch words from the loop-entry post:
    the live exponent word (at `evmSp + 32`) and the deeper stack
    (`evmStackIs (evmSp + 128) rest`). -/
@[irreducible]
def expTwoMulEntryIterPreResidual
    (evmSp : Word) (exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  evmWordIs (evmSp + 32) exponentWord ** evmStackIs (evmSp + 128) rest

theorem expTwoMulEntryIterPreResidual_unfold
    {evmSp : Word} {exponentWord : EvmWord} {rest : List EvmWord} :
    expTwoMulEntryIterPreResidual evmSp exponentWord rest =
      (evmWordIs (evmSp + 32) exponentWord ** evmStackIs (evmSp + 128) rest) := by
  delta expTwoMulEntryIterPreResidual
  rfl

theorem expTwoMulEntryIterPreResidual_pcFree
    {evmSp : Word} {exponentWord : EvmWord} {rest : List EvmWord} :
    (expTwoMulEntryIterPreResidual evmSp exponentWord rest).pcFree := by
  rw [expTwoMulEntryIterPreResidual_unfold]
  exact pcFree_sepConj pcFree_evmWordIs pcFree_evmStackIs

instance pcFreeInst_expTwoMulEntryIterPreResidual
    (evmSp : Word) (exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree (expTwoMulEntryIterPreResidual evmSp exponentWord rest) :=
  ⟨expTwoMulEntryIterPreResidual_pcFree⟩

/-- Loop-entry → first-iteration-pre bridge (non-fixed / two-MUL path).

    The prologue's `expTwoMulLoopEntryPost` (with the stack carrying the two
    scratch words `dWord`, `eWord` below the operands) implies the
    first-iteration precondition `expTwoMulIterPre` at counter `256`, run from
    the advanced stack pointer `evmSp + 64`, with:
    - accumulator `e = 1` and `r0..r3 = limbs of 1` (the squaring scratch at `sp`);
    - base limbs `a0..a3 = baseWord` (the multiplier, popped below the new top);
    - scratch limbs `d0..d3 = dWord`, `e0..e3 = eWord`;
    plus the residual exponent word and deeper stack.

    This is a pure separation-logic reshuffle (no code executed); it is the
    bridge that wires the prologue into
    `exp_loop_from_iterpre_full_body_general_spec_within`. -/
theorem expTwoMulLoopEntryPost_to_iterPre_frame
    {sp evmSp vOld v18 : Word}
    {baseWord exponentWord dWord eWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expTwoMulLoopEntryPost sp evmSp vOld v18
      baseWord exponentWord (dWord :: eWord :: rest) ps) :
    (expTwoMulIterPre (1 : Word) (256 : Word) v18 sp (evmSp + 64) vOld
        ((1 : EvmWord).getLimbN 0) ((1 : EvmWord).getLimbN 1)
        ((1 : EvmWord).getLimbN 2) ((1 : EvmWord).getLimbN 3)
        (dWord.getLimbN 0) (dWord.getLimbN 1) (dWord.getLimbN 2) (dWord.getLimbN 3)
        (eWord.getLimbN 0) (eWord.getLimbN 1) (eWord.getLimbN 2) (eWord.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3) **
     expTwoMulEntryIterPreResidual evmSp exponentWord rest) ps := by
  rw [expTwoMulLoopEntryPost_unfold_rest2_offsets] at h
  rw [expTwoMulIterPre_unfold, expTwoMulIterBaseFrame_unfold,
    expTwoMulEntryIterPreResidual_unfold]
  unfold evmWordIs at h ⊢
  simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
    signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
    EvmAsm.Rv64.AddrNorm.word_add_zero, BitVec.add_assoc,
    show (64 : Word) + signExtend12 ((-64) : BitVec 12) = 0 from by decide,
    show (64 : Word) + signExtend12 ((-56) : BitVec 12) = 8 from by decide,
    show (64 : Word) + signExtend12 ((-48) : BitVec 12) = 16 from by decide,
    show (64 : Word) + signExtend12 ((-40) : BitVec 12) = 24 from by decide,
    show (32 : Word) + 8 = 40 from by decide,
    show (32 : Word) + 16 = 48 from by decide,
    show (32 : Word) + 24 = 56 from by decide,
    show (64 : Word) + 8 = 72 from by decide,
    show (64 : Word) + 16 = 80 from by decide,
    show (64 : Word) + 24 = 88 from by decide,
    show (64 : Word) + 32 = 96 from by decide,
    show (64 : Word) + 40 = 104 from by decide,
    show (64 : Word) + 48 = 112 from by decide,
    show (64 : Word) + 56 = 120 from by decide,
    show (96 : Word) + 8 = 104 from by decide,
    show (96 : Word) + 16 = 112 from by decide,
    show (96 : Word) + 24 = 120 from by decide] at h ⊢
  sep_perm h

end EvmAsm.Evm64.Exp.Compose
