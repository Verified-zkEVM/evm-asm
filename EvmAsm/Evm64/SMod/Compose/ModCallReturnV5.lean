/-
  EvmAsm.Evm64.SMod.Compose.ModCallReturnV5

  v5 SMOD return rung (B7), over `smodCodeV5`.  Composes the v5 B5 rung
  (`saveRaAbsThenModCall_then_resultSignFix_of_callable_post_noX9_spec_in_smodCodeV5`)
  with the saved-`ra` return instruction (`savedRaRet_spec_in_smodCodeV5`),
  mirroring the SMOD v4 return generic (`ModCallReturnGeneric.lean`) and the SDIV
  v5 B7 (`DivCallReturnV5.lean`), carrying the trailing PCFree frame
  `(regOwn .x9 ** memOwn (sp+3936))` through the return.
-/

import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixV5
import EvmAsm.Evm64.SMod.Compose.ModCallReturnGeneric
import EvmAsm.Evm64.SMod.Compose.BaseSpecsV5

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64

/-- B7: v5 SMOD prefix + exact MOD callable + result-sign-fix + saved-RA return,
    landing the explicit return post (+ trailing `regOwn .x9 ** memOwn (sp+3936)`). -/
theorem saveRaAbsThenModCall_then_return_of_callable_post_noX9_spec_in_smodCodeV5
    {nSteps : Nat}
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (smodCodeV5 base)
        (saveRaAbsThenModCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (saveRaAbsThenModCallCallablePost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
         (regOwn .x9 ** memOwn (sp + signExtend12 3936)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + nSteps) + 21) + 1)
      base (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) (smodCodeV5 base)
      (((((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendLimb0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendLimb1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendLimb2)))) **
       (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorLimb0) **
        ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorLimb1) **
        ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorLimb2))) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (let dividendAbsWord : EvmWord :=
         smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord : EvmWord :=
         smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
       let resultSign := smodAbsSign dividendTop
       ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (smodResultSignFixPost (sp + 32) resultSign
         (modWord.getLimbN 0) (modWord.getLimbN 1)
         (modWord.getLimbN 2) (modWord.getLimbN 3) **
        smodSavedRaRetFrame sp base dividendTop dividendAbsWord)) **
       (regOwn .x9 ** memOwn (sp + signExtend12 3936))) := by
  let dividendAbsWord : EvmWord :=
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
  let resultSign := smodAbsSign dividendTop
  have hPrefix :=
    saveRaAbsThenModCall_then_resultSignFix_of_callable_post_noX9_spec_in_smodCodeV5
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base hCallable
  have hRetFramePc :
      (smodResultSignFixPost (sp + 32) resultSign
        (modWord.getLimbN 0) (modWord.getLimbN 1)
        (modWord.getLimbN 2) (modWord.getLimbN 3) **
       smodSavedRaRetFrame sp base dividendTop dividendAbsWord).pcFree := by
    pcFree
  have hRetFramedInner :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (smodResultSignFixPost (sp + 32) resultSign
        (modWord.getLimbN 0) (modWord.getLimbN 1)
        (modWord.getLimbN 2) (modWord.getLimbN 3) **
       smodSavedRaRetFrame sp base dividendTop dividendAbsWord)
      hRetFramePc
      (savedRaRet_spec_in_smodCodeV5
        (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) base)
  have hTpc : (regOwn .x9 ** memOwn (sp + signExtend12 3936)).pcFree := by
    pcFree
  have hRetFramed :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (regOwn .x9 ** memOwn (sp + signExtend12 3936))
      hTpc hRetFramedInner
  have hFall :
      (base + resultSignFixOff) + 84 = base + savedRaRetOff := by
    simp [resultSignFixOff, savedRaRetOff]
    bv_addr
  have hRetFramed' :
      EvmAsm.Rv64.cpsTripleWithin 1 ((base + resultSignFixOff) + 84)
        (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
          EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word))
        (smodCodeV5 base)
        (((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (smodResultSignFixPost (sp + 32) resultSign
          (modWord.getLimbN 0) (modWord.getLimbN 1)
          (modWord.getLimbN 2) (modWord.getLimbN 3) **
          smodSavedRaRetFrame sp base dividendTop dividendAbsWord)) **
         (regOwn .x9 ** memOwn (sp + signExtend12 3936)))
        (((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (smodResultSignFixPost (sp + 32) resultSign
          (modWord.getLimbN 0) (modWord.getLimbN 1)
          (modWord.getLimbN 2) (modWord.getLimbN 3) **
          smodSavedRaRetFrame sp base dividendTop dividendAbsWord)) **
         (regOwn .x9 ** memOwn (sp + signExtend12 3936))) := by
    rw [hFall]
    exact hRetFramed
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [smodModCallResultSignFixFrame_to_savedRaRet] at hp
      xperm_hyp hp)
    hPrefix hRetFramed'

end EvmAsm.Evm64.SMod.Compose
