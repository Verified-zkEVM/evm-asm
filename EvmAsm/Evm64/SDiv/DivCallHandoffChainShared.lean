/- Shared declaration home for the SDIV dispatch handoff and return chain. -/

import EvmAsm.Evm64.EvmWordArith.Div
import EvmAsm.Evm64.SDiv.Compose.BzeroFrames
import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFix
import EvmAsm.Evm64.SDiv.Compose.Words
import EvmAsm.Evm64.SDiv.Compose.DispatchViews
import EvmAsm.Evm64.SDiv.Compose.BzeroPost
import EvmAsm.Evm64.SDiv.Compose.DispatchPrefix
import EvmAsm.Evm64.SDiv.Compose.DispatchReadyPost
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn

namespace EvmAsm.Evm64.SDiv.Compose

@[irreducible]
def saveRaDivCallCallableReturnPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  (.x18 ↦ᵣ vRa) **
  (resultSignFixPost (sp + 32) resultSign
    (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
    (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
   saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)

theorem saveRaDivCallCallableReturnPost_unfold
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallCallableReturnPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       (.x18 ↦ᵣ vRa) **
       (resultSignFixPost (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  delta saveRaDivCallCallableReturnPost
  rfl

theorem saveRaDivCallCallableReturnPost_pcFree
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    (saveRaDivCallCallableReturnPost vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).pcFree := by
  rw [saveRaDivCallCallableReturnPost_unfold]
  dsimp
  rw [resultSignFixPost_unfold, saveRaDivCallBzeroSavedRaRetFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_saveRaDivCallCallableReturnPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (saveRaDivCallCallableReturnPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) :=
  ⟨saveRaDivCallCallableReturnPost_pcFree⟩

@[irreducible]
def saveRaDivCallCallableReturnPostNoX9
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
  (resultSignFixPost (sp + 32) resultSign
    (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
    (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
   saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)

theorem saveRaDivCallCallableReturnPostNoX9_unfold
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallCallableReturnPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (resultSignFixPost (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) := by
  delta saveRaDivCallCallableReturnPostNoX9
  rfl

theorem saveRaDivCallCallableReturnPostNoX9_pcFree
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    (saveRaDivCallCallableReturnPostNoX9 vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).pcFree := by
  rw [saveRaDivCallCallableReturnPostNoX9_unfold]
  dsimp
  rw [resultSignFixPost_unfold, saveRaDivCallSavedRaRetFrameNoX9_unfold,
    EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

/-- Callable-return postcondition after SDIV result-sign fixup, with the
    produced result slot folded as a named sign-fixed quotient word. -/
@[irreducible]
def saveRaDivCallCallableReturnSignFixedWordPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let resultWord :=
    sdivSignFixedWord resultSign
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3)
  let mask := (0 : Word) - resultSign
  let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
  let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
  let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x18 ↦ᵣ vRa) **
  (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
    (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
    evmWordIs (sp + 32) resultWord) **
   saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)

theorem saveRaDivCallCallableReturnSignFixedWordPost_unfold
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallCallableReturnSignFixedWordPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let resultWord :=
         sdivSignFixedWord resultSign
           (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
           (quotientWord.getLimbN 2) (quotientWord.getLimbN 3)
       let mask := (0 : Word) - resultSign
       let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ vRa) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmWordIs (sp + 32) resultWord) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  delta saveRaDivCallCallableReturnSignFixedWordPost
  rfl

theorem saveRaDivCallCallableReturnSignFixedWordPost_pcFree
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    (saveRaDivCallCallableReturnSignFixedWordPost vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).pcFree := by
  rw [saveRaDivCallCallableReturnSignFixedWordPost_unfold]
  dsimp
  rw [saveRaDivCallBzeroSavedRaRetFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_saveRaDivCallCallableReturnSignFixedWordPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (saveRaDivCallCallableReturnSignFixedWordPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) :=
  ⟨saveRaDivCallCallableReturnSignFixedWordPost_pcFree⟩

/-- Exact-callable return postcondition view with the result slot folded as the
    named sign-fixed SDIV word. -/
theorem saveRaDivCallCallableReturnPost_evmWordIs
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    saveRaDivCallCallableReturnPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      saveRaDivCallCallableReturnSignFixedWordPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop := by
  rw [saveRaDivCallCallableReturnPost_unfold,
    saveRaDivCallCallableReturnSignFixedWordPost_unfold]
  dsimp only
  rw [resultSignFixPost_evmWordIs]

@[irreducible]
def saveRaDivCallCallableReturnSignFixedWordPostNoX9
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let resultWord :=
    sdivSignFixedWord resultSign
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3)
  let mask := (0 : Word) - resultSign
  let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
  let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
  let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
  (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
    (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
    evmWordIs (sp + 32) resultWord) **
   saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)

theorem saveRaDivCallCallableReturnSignFixedWordPostNoX9_unfold
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallCallableReturnSignFixedWordPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let resultWord :=
         sdivSignFixedWord resultSign
           (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
           (quotientWord.getLimbN 2) (quotientWord.getLimbN 3)
       let mask := (0 : Word) - resultSign
       let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmWordIs (sp + 32) resultWord) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) := by
  delta saveRaDivCallCallableReturnSignFixedWordPostNoX9
  rfl

theorem saveRaDivCallCallableReturnPostNoX9_evmWordIs
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    saveRaDivCallCallableReturnPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      saveRaDivCallCallableReturnSignFixedWordPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop := by
  rw [saveRaDivCallCallableReturnPostNoX9_unfold,
    saveRaDivCallCallableReturnSignFixedWordPostNoX9_unfold]
  dsimp only
  rw [resultSignFixPost_evmWordIs]

@[irreducible]
def saveRaDivCallResultSignFixPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  resultSignFixPost (sp + 32) resultSign
    (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
    (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
  saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord

theorem saveRaDivCallResultSignFixPost_unfold
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallResultSignFixPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       resultSignFixPost (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
       saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord) := by
  delta saveRaDivCallResultSignFixPost
  rfl

theorem saveRaDivCallResultSignFixPost_pcFree
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    (saveRaDivCallResultSignFixPost vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).pcFree := by
  rw [saveRaDivCallResultSignFixPost_unfold]
  dsimp
  rw [resultSignFixPost_unfold, saveRaDivCallBzeroResultSignFixFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_saveRaDivCallResultSignFixPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (saveRaDivCallResultSignFixPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) :=
  ⟨saveRaDivCallResultSignFixPost_pcFree⟩

@[irreducible]
def saveRaDivCallResultSignFixPostNoX9
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  resultSignFixPost (sp + 32) resultSign
    (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
    (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
  saveRaDivCallResultSignFixFrameNoX9 vRa sp base dividendAbsWord

theorem saveRaDivCallResultSignFixPostNoX9_unfold
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallResultSignFixPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       resultSignFixPost (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
       saveRaDivCallResultSignFixFrameNoX9 vRa sp base dividendAbsWord) := by
  delta saveRaDivCallResultSignFixPostNoX9
  rfl

theorem saveRaDivCallResultSignFixPostNoX9_pcFree
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    (saveRaDivCallResultSignFixPostNoX9 vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).pcFree := by
  rw [saveRaDivCallResultSignFixPostNoX9_unfold]
  dsimp
  rw [resultSignFixPost_unfold, saveRaDivCallResultSignFixFrameNoX9_unfold,
    EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

open EvmAsm.Rv64.Tactics

/-- v4 SDIV wrapper prefix followed by any b=0 unsigned-DIV callable proof,
    then through result-sign-fix over the produced quotient word. -/
theorem saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_of_callable_post_spec_in_sdivCodeV4
    {nSteps : Nat}
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (saveRaDivCallBzeroCallablePost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)) :
    EvmAsm.Rv64.cpsTripleWithin ((49 + nSteps) + 21)
      base ((base + resultSignFixOff) + 84) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       resultSignFixPost (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
       saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_then_exact_callable_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0
      base (base + resultSignFixOff) hCallable
  have hFramePc :
      (saveRaDivCallBzeroResultSignFixFrame
        vRa sp base divisorSign dividendAbsWord).pcFree := by
    rw [saveRaDivCallBzeroResultSignFixFrame_unfold,
      EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
      EvmAsm.Evm64.divScratchOwn_unfold]
    pcFree
  have hFix :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (saveRaDivCallBzeroResultSignFixFrame
        vRa sp base divisorSign dividendAbsWord)
      hFramePc
      (resultSignFix_regOwn_scratch_spec_in_sdivCodeV4
        (sp + 32) resultSign
        (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
        (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) base)
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h (hp : (saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) h) => by
      rw [saveRaDivCallBzeroCallablePost_resultSignFixPreOwnScratch_quotient] at hp
      exact hp)
    hPrefix hFix

/-- v4 SDIV wrapper prefix followed by any exact unsigned-DIV callable proof,
    then through result-sign-fix over the produced quotient word. -/
theorem saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_of_callable_post_noX9_spec_in_sdivCodeV4
    {nSteps : Nat}
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (saveRaDivCallCallablePostNoX9 vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)) :
    EvmAsm.Rv64.cpsTripleWithin ((49 + nSteps) + 21)
      base ((base + resultSignFixOff) + 84) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       resultSignFixPost (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
       saveRaDivCallResultSignFixFrameNoX9 vRa sp base dividendAbsWord) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_then_exact_callable_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0
      base (base + resultSignFixOff) hCallable
  have hFramePc :
      (saveRaDivCallResultSignFixFrameNoX9
        vRa sp base dividendAbsWord).pcFree := by
    rw [saveRaDivCallResultSignFixFrameNoX9_unfold,
      EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
      EvmAsm.Evm64.divScratchOwn_unfold]
    pcFree
  have hFix :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (saveRaDivCallResultSignFixFrameNoX9
        vRa sp base dividendAbsWord)
      hFramePc
      (resultSignFix_regOwn_scratch_spec_in_sdivCodeV4
        (sp + 32) resultSign
        (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
        (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) base)
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h (hp : (saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) h) => by
      rw [saveRaDivCallCallablePostNoX9_resultSignFixPreOwnScratch_quotient] at hp
      exact hp)
    hPrefix hFix

theorem divModStackDispatchPre_pcFree
    {sp : Word} {a b : EvmWord}
    {v1 v2 v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word} :
    (EvmAsm.Evm64.divModStackDispatchPre sp a b
      v1 v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0).pcFree := by
  rw [EvmAsm.Evm64.divModStackDispatchPre_unfold,
    EvmAsm.Evm64.divScratchValuesCall_unfold]
  pcFree

instance pcFreeInst_divModStackDispatchPre
    (sp : Word) (a b : EvmWord)
    (v1 v2 v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (EvmAsm.Evm64.divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) :=
  ⟨divModStackDispatchPre_pcFree⟩

theorem divStackDispatchPostNoX1_pcFree {sp : Word} {a b : EvmWord} :
    (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b).pcFree := by
  rw [EvmAsm.Evm64.divStackDispatchPostNoX1_unfold,
    EvmAsm.Evm64.divScratchOwnCall_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_divStackDispatchPostNoX1
    (sp : Word) (a b : EvmWord) :
    EvmAsm.Rv64.Assertion.PCFree (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b) :=
  ⟨divStackDispatchPostNoX1_pcFree⟩

abbrev sdivAbsSign (top : Word) : Word :=
  top >>> (63 : BitVec 6).toNat

abbrev sdivAbsMask (top : Word) : Word :=
  (0 : Word) - sdivAbsSign top

abbrev sdivAbsSum0 (limb0 top : Word) : Word :=
  (limb0 ^^^ sdivAbsMask top) + sdivAbsSign top

abbrev sdivAbsCarry0 (limb0 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum0 limb0 top) (sdivAbsSign top) then (1 : Word) else 0

abbrev sdivAbsSum1 (limb0 limb1 top : Word) : Word :=
  (limb1 ^^^ sdivAbsMask top) + sdivAbsCarry0 limb0 top

abbrev sdivAbsCarry1 (limb0 limb1 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum1 limb0 limb1 top) (sdivAbsCarry0 limb0 top) then
    (1 : Word)
  else
    0

abbrev sdivAbsSum2 (limb0 limb1 limb2 top : Word) : Word :=
  (limb2 ^^^ sdivAbsMask top) + sdivAbsCarry1 limb0 limb1 top

abbrev sdivAbsCarry2 (limb0 limb1 limb2 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum2 limb0 limb1 limb2 top)
      (sdivAbsCarry1 limb0 limb1 top) then
    (1 : Word)
  else
    0

abbrev sdivAbsSum3 (limb0 limb1 limb2 top : Word) : Word :=
  (top ^^^ sdivAbsMask top) + sdivAbsCarry2 limb0 limb1 limb2 top

abbrev sdivAbsCarry3 (limb0 limb1 limb2 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum3 limb0 limb1 limb2 top)
      (sdivAbsCarry2 limb0 limb1 limb2 top) then
    (1 : Word)
  else
    0

theorem sdivAbsDividendWord_eq_components
    (limb0 limb1 limb2 top : Word) :
    sdivAbsDividendWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => sdivAbsSum0 limb0 top
        | 1 => sdivAbsSum1 limb0 limb1 top
        | 2 => sdivAbsSum2 limb0 limb1 limb2 top
        | 3 => sdivAbsSum3 limb0 limb1 limb2 top := by
  rfl

theorem sdivAbsDivisorWord_eq_components
    (limb0 limb1 limb2 top : Word) :
    sdivAbsDivisorWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => sdivAbsSum0 limb0 top
        | 1 => sdivAbsSum1 limb0 limb1 top
        | 2 => sdivAbsSum2 limb0 limb1 limb2 top
        | 3 => sdivAbsSum3 limb0 limb1 limb2 top := by
  rfl

theorem sdivAbsDividendWord_getLimbN_0
    (limb0 limb1 limb2 top : Word) :
    (sdivAbsDividendWord limb0 limb1 limb2 top).getLimbN 0 =
      sdivAbsSum0 limb0 top := by
  rw [sdivAbsDividendWord_eq_components, EvmWord.getLimbN_lt _ 0 (by decide)]
  exact EvmWord.getLimb_fromLimbs

theorem sdivAbsDividendWord_getLimbN_1
    (limb0 limb1 limb2 top : Word) :
    (sdivAbsDividendWord limb0 limb1 limb2 top).getLimbN 1 =
      sdivAbsSum1 limb0 limb1 top := by
  rw [sdivAbsDividendWord_eq_components, EvmWord.getLimbN_lt _ 1 (by decide)]
  exact EvmWord.getLimb_fromLimbs

theorem sdivAbsDividendWord_getLimbN_2
    (limb0 limb1 limb2 top : Word) :
    (sdivAbsDividendWord limb0 limb1 limb2 top).getLimbN 2 =
      sdivAbsSum2 limb0 limb1 limb2 top := by
  rw [sdivAbsDividendWord_eq_components, EvmWord.getLimbN_lt _ 2 (by decide)]
  exact EvmWord.getLimb_fromLimbs

theorem sdivAbsDividendWord_getLimbN_3
    (limb0 limb1 limb2 top : Word) :
    (sdivAbsDividendWord limb0 limb1 limb2 top).getLimbN 3 =
      sdivAbsSum3 limb0 limb1 limb2 top := by
  rw [sdivAbsDividendWord_eq_components, EvmWord.getLimbN_lt _ 3 (by decide)]
  exact EvmWord.getLimb_fromLimbs

theorem sdivAbsDivisorWord_getLimbN_0
    (limb0 limb1 limb2 top : Word) :
    (sdivAbsDivisorWord limb0 limb1 limb2 top).getLimbN 0 =
      sdivAbsSum0 limb0 top := by
  rw [sdivAbsDivisorWord_eq_components, EvmWord.getLimbN_lt _ 0 (by decide)]
  exact EvmWord.getLimb_fromLimbs

theorem sdivAbsDivisorWord_getLimbN_1
    (limb0 limb1 limb2 top : Word) :
    (sdivAbsDivisorWord limb0 limb1 limb2 top).getLimbN 1 =
      sdivAbsSum1 limb0 limb1 top := by
  rw [sdivAbsDivisorWord_eq_components, EvmWord.getLimbN_lt _ 1 (by decide)]
  exact EvmWord.getLimb_fromLimbs

theorem sdivAbsDivisorWord_getLimbN_2
    (limb0 limb1 limb2 top : Word) :
    (sdivAbsDivisorWord limb0 limb1 limb2 top).getLimbN 2 =
      sdivAbsSum2 limb0 limb1 limb2 top := by
  rw [sdivAbsDivisorWord_eq_components, EvmWord.getLimbN_lt _ 2 (by decide)]
  exact EvmWord.getLimb_fromLimbs

theorem sdivAbsDivisorWord_getLimbN_3
    (limb0 limb1 limb2 top : Word) :
    (sdivAbsDivisorWord limb0 limb1 limb2 top).getLimbN 3 =
      sdivAbsSum3 limb0 limb1 limb2 top := by
  rw [sdivAbsDivisorWord_eq_components, EvmWord.getLimbN_lt _ 3 (by decide)]
  exact EvmWord.getLimb_fromLimbs

theorem sdivAbsDividendWord_evmWordIs_sp_components
    (sp limb0 limb1 limb2 top : Word) :
    evmWordIs sp (sdivAbsDividendWord limb0 limb1 limb2 top) =
      ((sp ↦ₘ sdivAbsSum0 limb0 top) **
       ((sp + 8) ↦ₘ sdivAbsSum1 limb0 limb1 top) **
       ((sp + 16) ↦ₘ sdivAbsSum2 limb0 limb1 limb2 top) **
       ((sp + 24) ↦ₘ sdivAbsSum3 limb0 limb1 limb2 top)) := by
  rw [sdivAbsDividendWord_eq_components]
  exact evmWordIs_sp_limbs_eq sp _ _ _ _ _
    EvmWord.getLimbN_fromLimbs_0
    EvmWord.getLimbN_fromLimbs_1
    EvmWord.getLimbN_fromLimbs_2
    EvmWord.getLimbN_fromLimbs_3

open EvmAsm.Rv64 in
theorem sdivAbsDividendWord_evmWordIs_sp_components_right
    (sp limb0 limb1 limb2 top : Word) (Q : Assertion) :
    ((sp ↦ₘ sdivAbsSum0 limb0 top) **
     ((sp + 8) ↦ₘ sdivAbsSum1 limb0 limb1 top) **
     ((sp + 16) ↦ₘ sdivAbsSum2 limb0 limb1 limb2 top) **
     ((sp + 24) ↦ₘ sdivAbsSum3 limb0 limb1 limb2 top) ** Q) =
      (evmWordIs sp (sdivAbsDividendWord limb0 limb1 limb2 top) ** Q) := by
  rw [sdivAbsDividendWord_evmWordIs_sp_components]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

open EvmAsm.Rv64 in
theorem sdivAbsDividendWord_evmWordIs_sp_components_sdivOffsets
    (sp limb0 limb1 limb2 top : Word) :
    evmWordIs sp (sdivAbsDividendWord limb0 limb1 limb2 top) =
      (((sp + signExtend12 (0 : BitVec 12)) ↦ₘ sdivAbsSum0 limb0 top) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ sdivAbsSum1 limb0 limb1 top) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ sdivAbsSum2 limb0 limb1 limb2 top) **
       ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         sdivAbsSum3 limb0 limb1 limb2 top)) := by
  rw [sdivAbsDividendWord_evmWordIs_sp_components]
  rw [show sp + signExtend12 (0 : BitVec 12) = sp by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) by decide]
    simp]
  rw [show sp + signExtend12 (8 : BitVec 12) = sp + 8 by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) by decide]]
  rw [show sp + signExtend12 (16 : BitVec 12) = sp + 16 by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) by decide]]
  rw [show sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff =
      sp + 24 by
    unfold EvmAsm.Evm64.evm_sdivDividendTopLimbOff
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) by decide]]

open EvmAsm.Rv64 in
theorem sdivAbsDividendWord_evmWordIs_sp_components_sdivOffsets_right
    (sp limb0 limb1 limb2 top : Word) (Q : Assertion) :
    (((sp + signExtend12 (0 : BitVec 12)) ↦ₘ sdivAbsSum0 limb0 top) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ sdivAbsSum1 limb0 limb1 top) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ sdivAbsSum2 limb0 limb1 limb2 top) **
     ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
       sdivAbsSum3 limb0 limb1 limb2 top) ** Q) =
      (evmWordIs sp (sdivAbsDividendWord limb0 limb1 limb2 top) ** Q) := by
  rw [sdivAbsDividendWord_evmWordIs_sp_components_sdivOffsets]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

theorem sdivAbsDivisorWord_evmWordIs_sp32_components
    (sp limb0 limb1 limb2 top : Word) :
    evmWordIs (sp + 32) (sdivAbsDivisorWord limb0 limb1 limb2 top) =
      (((sp + 32) ↦ₘ sdivAbsSum0 limb0 top) **
       ((sp + 40) ↦ₘ sdivAbsSum1 limb0 limb1 top) **
       ((sp + 48) ↦ₘ sdivAbsSum2 limb0 limb1 limb2 top) **
       ((sp + 56) ↦ₘ sdivAbsSum3 limb0 limb1 limb2 top)) := by
  rw [sdivAbsDivisorWord_eq_components]
  exact evmWordIs_sp32_limbs_eq sp _ _ _ _ _
    EvmWord.getLimbN_fromLimbs_0
    EvmWord.getLimbN_fromLimbs_1
    EvmWord.getLimbN_fromLimbs_2
    EvmWord.getLimbN_fromLimbs_3

open EvmAsm.Rv64 in
theorem sdivAbsDivisorWord_evmWordIs_sp32_components_right
    (sp limb0 limb1 limb2 top : Word) (Q : Assertion) :
    (((sp + 32) ↦ₘ sdivAbsSum0 limb0 top) **
     ((sp + 40) ↦ₘ sdivAbsSum1 limb0 limb1 top) **
     ((sp + 48) ↦ₘ sdivAbsSum2 limb0 limb1 limb2 top) **
     ((sp + 56) ↦ₘ sdivAbsSum3 limb0 limb1 limb2 top) ** Q) =
      (evmWordIs (sp + 32) (sdivAbsDivisorWord limb0 limb1 limb2 top) ** Q) := by
  rw [sdivAbsDivisorWord_evmWordIs_sp32_components]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

open EvmAsm.Rv64 in
theorem sdivAbsDivisorWord_evmWordIs_sp32_components_sdivOffsets
    (sp limb0 limb1 limb2 top : Word) :
    evmWordIs (sp + 32) (sdivAbsDivisorWord limb0 limb1 limb2 top) =
      (((sp + signExtend12 (32 : BitVec 12)) ↦ₘ sdivAbsSum0 limb0 top) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ sdivAbsSum1 limb0 limb1 top) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ sdivAbsSum2 limb0 limb1 limb2 top) **
       ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
         sdivAbsSum3 limb0 limb1 limb2 top)) := by
  rw [sdivAbsDivisorWord_evmWordIs_sp32_components]
  rw [show sp + signExtend12 (32 : BitVec 12) = sp + 32 by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) by decide]]
  rw [show sp + signExtend12 (40 : BitVec 12) = sp + 40 by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) by decide]]
  rw [show sp + signExtend12 (48 : BitVec 12) = sp + 48 by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) by decide]]
  rw [show sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff =
      sp + 56 by
    unfold EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
    rw [show signExtend12 (56 : BitVec 12) = (56 : Word) by decide]]

open EvmAsm.Rv64 in
theorem sdivAbsDivisorWord_evmWordIs_sp32_components_sdivOffsets_right
    (sp limb0 limb1 limb2 top : Word) (Q : Assertion) :
    (((sp + signExtend12 (32 : BitVec 12)) ↦ₘ sdivAbsSum0 limb0 top) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ sdivAbsSum1 limb0 limb1 top) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ sdivAbsSum2 limb0 limb1 limb2 top) **
     ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
       sdivAbsSum3 limb0 limb1 limb2 top) ** Q) =
      (evmWordIs (sp + 32) (sdivAbsDivisorWord limb0 limb1 limb2 top) ** Q) := by
  rw [sdivAbsDivisorWord_evmWordIs_sp32_components_sdivOffsets]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

abbrev saveRaDivCallSignFrame
    (vRa resultSign divisorSign : Word) : EvmAsm.Rv64.Assertion :=
  ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
    (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))

abbrev sdivDivCallResultSign (dividendTop divisorTop : Word) : Word :=
  sdivAbsSign dividendTop ^^^ sdivAbsSign divisorTop




/-- v4 named-post wrapper for the b=0 SDIV callable composition through
    result-sign-fix, before the saved-RA return. -/
theorem saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_named_post_of_callable_post_spec_in_sdivCodeV4
    {nSteps : Nat}
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (saveRaDivCallBzeroCallablePost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)) :
    EvmAsm.Rv64.cpsTripleWithin ((49 + nSteps) + 21)
      base ((base + resultSignFixOff) + 84) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallResultSignFixPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  rw [saveRaDivCallResultSignFixPost_unfold]
  exact
    saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_of_callable_post_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hCallable

/-- v4 named-post wrapper for the generic SDIV callable composition through
    result-sign-fix, before the saved-RA return. -/
theorem saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_named_post_of_callable_post_noX9_spec_in_sdivCodeV4
    {nSteps : Nat}
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (saveRaDivCallCallablePostNoX9 vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)) :
    EvmAsm.Rv64.cpsTripleWithin ((49 + nSteps) + 21)
      base ((base + resultSignFixOff) + 84) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallResultSignFixPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  rw [saveRaDivCallResultSignFixPostNoX9_unfold]
  exact
    saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_of_callable_post_noX9_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hCallable

open EvmAsm.Rv64.Tactics

/-- v4 SDIV wrapper prefix followed by any b=0 unsigned-DIV callable proof,
    result-sign-fix over the produced quotient word, and the saved-RA return. -/
theorem saveRa_signs_abs_signXor_then_divCall_then_return_of_callable_post_spec_in_sdivCodeV4
    {nSteps : Nat}
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (saveRaDivCallBzeroCallablePost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + nSteps) + 21) + 1)
      base (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (resultSignFixPost (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_named_post_of_callable_post_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hCallable
  rw [saveRaDivCallResultSignFixPost_unfold] at hPrefix
  have hRetFramePc :
      (resultSignFixPost (sp + 32) resultSign
        (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
        (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord).pcFree := by
    rw [resultSignFixPost_unfold, saveRaDivCallBzeroSavedRaRetFrame_unfold,
      EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
      EvmAsm.Evm64.divScratchOwn_unfold]
    pcFree
  have hRetFramed :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (resultSignFixPost (sp + 32) resultSign
        (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
        (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)
      hRetFramePc
      (savedRaRet_spec_in_sdivCodeV4
        (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) base)
  have hFall :
      (base + resultSignFixOff) + 84 = base + savedRaRetOff := by
    simp [resultSignFixOff, savedRaRetOff]
    bv_addr
  have hRetFramed' :
      EvmAsm.Rv64.cpsTripleWithin 1 ((base + resultSignFixOff) + 84)
        (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
          EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word))
        (sdivCodeV4 base)
        ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (resultSignFixPost (sp + 32) resultSign
          (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
          (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
          saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord))
        ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (resultSignFixPost (sp + 32) resultSign
          (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
          (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
          saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
    rw [hFall]
    exact hRetFramed
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [saveRaDivCallBzeroResultSignFixFrame_to_savedRaRet] at hp
      xperm_hyp hp)
    hPrefix hRetFramed'

/-- v4 SDIV wrapper prefix followed by any exact unsigned-DIV callable proof,
    result-sign-fix over the produced quotient word, and the saved-RA return. -/
theorem saveRa_signs_abs_signXor_then_divCall_then_return_of_callable_post_noX9_spec_in_sdivCodeV4
    {nSteps : Nat}
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (saveRaDivCallCallablePostNoX9 vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + nSteps) + 21) + 1)
      base (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallCallableReturnPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  rw [saveRaDivCallCallableReturnPostNoX9_unfold]
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_named_post_of_callable_post_noX9_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hCallable
  rw [saveRaDivCallResultSignFixPostNoX9_unfold] at hPrefix
  have hRetFramePc :
      (resultSignFixPost (sp + 32) resultSign
        (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
        (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord).pcFree := by
    rw [resultSignFixPost_unfold, saveRaDivCallSavedRaRetFrameNoX9_unfold,
      EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
      EvmAsm.Evm64.divScratchOwn_unfold]
    pcFree
  have hRetFramed :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (resultSignFixPost (sp + 32) resultSign
        (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
        (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)
      hRetFramePc
      (savedRaRet_spec_in_sdivCodeV4
        (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) base)
  have hFall :
      (base + resultSignFixOff) + 84 = base + savedRaRetOff := by
    simp [resultSignFixOff, savedRaRetOff]
    bv_addr
  have hRetFramed' :
      EvmAsm.Rv64.cpsTripleWithin 1 ((base + resultSignFixOff) + 84)
        (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
          EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word))
        (sdivCodeV4 base)
        ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (resultSignFixPost (sp + 32) resultSign
          (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
          (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
          saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord))
        ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (resultSignFixPost (sp + 32) resultSign
          (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
          (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
          saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) := by
    rw [hFall]
    exact hRetFramed
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [saveRaDivCallResultSignFixFrameNoX9_to_savedRaRet] at hp
      xperm_hyp hp)
    hPrefix hRetFramed'

/-- v4 normalized return-target view of the generic SDIV callable composition.
    This hides the two `signExtend12 0` artifacts from the saved-RA move and
    final `JALR`, leaving callers with the ordinary masked return address. -/
theorem saveRa_signs_abs_signXor_then_divCall_then_return_normalized_of_callable_post_spec_in_sdivCodeV4
    {nSteps : Nat}
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (saveRaDivCallBzeroCallablePost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + nSteps) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       (.x18 ↦ᵣ vRa) **
       (resultSignFixPost (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  have hExit :
      (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) =
        (vRa &&& ~~~(1 : Word)) := by
    rw [EvmAsm.Rv64.signExtend12_0]
    simp [BitVec.add_zero]
  rw [← hExit]
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      simp only [EvmAsm.Rv64.signExtend12_0] at hp ⊢
      have h_ra : (vRa + (0 : Word)) = vRa := by bv_omega
      rw [h_ra] at hp
      exact hp)
    (saveRa_signs_abs_signXor_then_divCall_then_return_of_callable_post_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hCallable)

/-- v4 named-post wrapper for the normalized generic SDIV callable composition.
    This is the stable handoff surface for later exact-callable proofs. -/
theorem saveRa_signs_abs_signXor_then_divCall_then_return_normalized_named_post_of_callable_post_spec_in_sdivCodeV4
    {nSteps : Nat}
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (saveRaDivCallBzeroCallablePost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + nSteps) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallCallableReturnPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  rw [saveRaDivCallCallableReturnPost_unfold]
  exact
    saveRa_signs_abs_signXor_then_divCall_then_return_normalized_of_callable_post_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hCallable

end EvmAsm.Evm64.SDiv.Compose
