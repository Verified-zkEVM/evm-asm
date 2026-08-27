/-
  EvmAsm.Evm64.Exp.Compose.SavedBitIterPostPcFree

  PC-free instances for the named two-MUL saved-bit EXP iteration
  pre/postcondition bundles.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitIterPosts

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

instance pcFreeInst_expTwoMulIterBaseFrame
    (evmSp a0 a1 a2 a3 : Word) :
    Assertion.PCFree (expTwoMulIterBaseFrame evmSp a0 a1 a2 a3) :=
  ⟨expTwoMulIterBaseFrame_pcFree⟩

instance pcFreeInst_expTwoMulIterSkipRest
    (bit sp evmSp base : Word) (w : EvmWord) :
    Assertion.PCFree (expTwoMulIterSkipRest bit sp evmSp base w) :=
  ⟨expTwoMulIterSkipRest_pcFree⟩

instance pcFreeInst_expTwoMulIterCondRest
    (sp evmSp base a0 a1 a2 a3 : Word) (rw : EvmWord) :
    Assertion.PCFree (expTwoMulIterCondRest sp evmSp base a0 a1 a2 a3 rw) :=
  ⟨expTwoMulIterCondRest_pcFree⟩

instance pcFreeInst_expTwoMulIterCondFrame (bit : Word) :
    Assertion.PCFree (expTwoMulIterCondFrame bit) :=
  ⟨expTwoMulIterCondFrame_pcFree⟩

instance pcFreeInst_expTwoMulIterCondPost
    (iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word) (rw : EvmWord)
    (exitCond : Prop) :
    Assertion.PCFree
      (expTwoMulIterCondPost iterCountNew bit sp evmSp base a0 a1 a2 a3 rw
        exitCond) :=
  ⟨expTwoMulIterCondPost_pcFree⟩

instance pcFreeInst_expTwoMulIterSkipPost
    (iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word) (w : EvmWord)
    (exitCond : Prop) :
    Assertion.PCFree
      (expTwoMulIterSkipPost iterCountNew bit sp evmSp base a0 a1 a2 a3 w
        exitCond) :=
  ⟨expTwoMulIterSkipPost_pcFree⟩

instance pcFreeInst_expTwoMulIterLoopPost
    (iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word) (w rw : EvmWord) :
    Assertion.PCFree
      (expTwoMulIterLoopPost iterCountNew bit sp evmSp base a0 a1 a2 a3 w rw) :=
  ⟨expTwoMulIterLoopPost_pcFree⟩

instance pcFreeInst_expTwoMulIterExitPost
    (iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word) (w rw : EvmWord) :
    Assertion.PCFree
      (expTwoMulIterExitPost iterCountNew bit sp evmSp base a0 a1 a2 a3 w rw) :=
  ⟨expTwoMulIterExitPost_pcFree⟩

instance pcFreeInst_expTwoMulIterPre
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word) :
    Assertion.PCFree
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3) :=
  ⟨expTwoMulIterPre_pcFree⟩

end EvmAsm.Evm64.Exp.Compose
