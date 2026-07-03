/-
  EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixV5

  v5 SMOD wrapper prefix + exact unsigned-MOD callable + result-sign-fix, over
  `smodCodeV5` (B5 of the SMOD `.proven` return chain).  Mirror of the SDIV v5
  `saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_of_callable_post_noX9_spec_in_sdivCodeV5`
  (DivCallResultSignFixV5.lean), but over the SMOD `ModCall*` family (SMOD negates
  the remainder by the dividend's sign x13, not the sign-XOR).  The callable proof
  carries the trailing PCFree frame `(regOwn .x9 ** memOwn (sp+3936))` that M2's
  x9-owned feed produces; it rides through the result-sign-fix block via
  `cpsTripleWithin_frameR`.
-/

import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFix
import EvmAsm.Evm64.SMod.Compose.PrefixChainV5
import EvmAsm.Evm64.SMod.Compose.ResultSignFixOwnV5

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64

/-- v5 SMOD wrapper prefix + any exact unsigned-MOD callable proof (carrying the
    trailing `regOwn .x9 ** memOwn (sp+3936)` frame), then result-sign-fix. -/
theorem saveRaAbsThenModCall_then_resultSignFix_of_callable_post_noX9_spec_in_smodCodeV5
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
    EvmAsm.Rv64.cpsTripleWithin ((49 + nSteps) + 21)
      base ((base + resultSignFixOff) + 84) (smodCodeV5 base)
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
       smodResultSignFixPost (sp + 32) resultSign
         (modWord.getLimbN 0) (modWord.getLimbN 1)
         (modWord.getLimbN 2) (modWord.getLimbN 3) **
       (smodModCallResultSignFixFrame vRa sp base dividendTop dividendAbsWord **
        (regOwn .x9 ** memOwn (sp + signExtend12 3936)))) := by
  let dividendAbsWord : EvmWord :=
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
  let resultSign := smodAbsSign dividendTop
  have hPrefix :=
    saveRa_signs_abs_then_modCall_dispatchReady_then_exact_callable_spec_in_smodCodeV5
      (callPost := saveRaAbsThenModCallCallablePost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
         (regOwn .x9 ** memOwn (sp + signExtend12 3936)))
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem
      base (base + resultSignFixOff) hCallable
  have hFramePc :
      (smodModCallResultSignFixFrame vRa sp base dividendTop dividendAbsWord **
        (regOwn .x9 ** memOwn (sp + signExtend12 3936))).pcFree :=
    EvmAsm.Rv64.pcFree_sepConj smodModCallResultSignFixFrame_pcFree (by pcFree)
  have hFix :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (smodModCallResultSignFixFrame vRa sp base dividendTop dividendAbsWord **
        (regOwn .x9 ** memOwn (sp + signExtend12 3936)))
      hFramePc
      (resultSignFix_regOwn_scratch_spec_in_smodCodeV5
        (sp + 32) resultSign
        (modWord.getLimbN 0) (modWord.getLimbN 1)
        (modWord.getLimbN 2) (modWord.getLimbN 3) base)
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [saveRaAbsThenModCallCallablePost_smodResultSignFixPreOwnScratch] at hp
      dsimp only [dividendAbsWord, divisorAbsWord, modWord, resultSign] at hp
      xperm_hyp hp)
    hPrefix hFix

end EvmAsm.Evm64.SMod.Compose
