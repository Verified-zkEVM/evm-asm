/-
  EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFixV5

  v5 SDIV wrapper prefix + exact unsigned-DIV callable + result-sign-fix, over
  `sdivCodeV5` (B5 of the SDIV `.proven` return chain).  Mirror of the v4
  `saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_of_callable_post_noX9_spec_in_sdivCodeV4`
  (DivCallResultSignFix.lean:267), but the callable proof carries the trailing
  PCFree frame `(regOwn .x9 ** memOwn (sp+3936))` that M2's x9-owned feed produces
  (v4 had exact x9 / no scratch).  The trailing frame rides through the
  result-sign-fix block via `cpsTripleWithin_frameR`.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFix
import EvmAsm.Evm64.SDiv.Compose.PrefixChainV5
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwnV5

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

/-- v5 SDIV wrapper prefix + any exact unsigned-DIV callable proof (carrying the
    trailing `regOwn .x9 ** memOwn (sp+3936)` frame), then result-sign-fix. -/
theorem saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_of_callable_post_noX9_spec_in_sdivCodeV5
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
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV5 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (saveRaDivCallCallablePostNoX9 vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
         (regOwn .x9 ** memOwn (sp + signExtend12 3936)))) :
    EvmAsm.Rv64.cpsTripleWithin ((49 + nSteps) + 21)
      base ((base + resultSignFixOff) + 84) (sdivCodeV5 base)
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
       (saveRaDivCallResultSignFixFrameNoX9 vRa sp base dividendAbsWord **
        (regOwn .x9 ** memOwn (sp + signExtend12 3936)))) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_then_exact_callable_spec_in_sdivCodeV5
      (callPost := saveRaDivCallCallablePostNoX9 vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
         (regOwn .x9 ** memOwn (sp + signExtend12 3936)))
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0
      base (base + resultSignFixOff) hCallable
  have hFramePc :
      (saveRaDivCallResultSignFixFrameNoX9 vRa sp base dividendAbsWord **
        (regOwn .x9 ** memOwn (sp + signExtend12 3936))).pcFree := by
    rw [saveRaDivCallResultSignFixFrameNoX9_unfold,
      EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
      EvmAsm.Evm64.divScratchOwn_unfold]
    pcFree
  have hFix :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (saveRaDivCallResultSignFixFrameNoX9 vRa sp base dividendAbsWord **
        (regOwn .x9 ** memOwn (sp + signExtend12 3936)))
      hFramePc
      (resultSignFix_regOwn_scratch_spec_in_sdivCodeV5
        (sp + 32) resultSign
        (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
        (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) base)
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h (hp : (saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       (regOwn .x9 ** memOwn (sp + signExtend12 3936))) h) => by
      rw [saveRaDivCallCallablePostNoX9_resultSignFixPreOwnScratch_quotient] at hp
      xperm_hyp hp)
    hPrefix hFix

end EvmAsm.Evm64.SDiv.Compose
