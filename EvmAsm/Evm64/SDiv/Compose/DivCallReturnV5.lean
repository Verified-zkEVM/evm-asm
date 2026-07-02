/-
  EvmAsm.Evm64.SDiv.Compose.DivCallReturnV5

  v5 SDIV return chain (B6, B7), over `sdivCodeV5`.  Mirrors of the v4 rungs
  `..._resultSignFix_named_post_...` (DivCallResultSignFixNamedPost.lean:140) and
  `..._then_return_of_callable_post_noX9_...` (DivCallReturnGeneric.lean:323),
  carrying the trailing PCFree frame `(regOwn .x9 ** memOwn (sp+3936))` from M2's
  x9-owned feed.  Neither `saveRaDivCallResultSignFixFrameNoX9` nor
  `saveRaDivCallSavedRaRetFrameNoX9` owns `[sp+3936]` (their `divScratchOwnCallNoX1`
  covers 3968/3960/3952/3944 + divScratchOwn only), so the trailing frame stays
  separate and rides through via `cpsTripleWithin_frameR`.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFixV5
import EvmAsm.Evm64.SDiv.Compose.DivCallReturnGeneric
import EvmAsm.Evm64.SDiv.Compose.BaseCodeV5

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

/-- B6: v5 result-sign-fix with the named post `saveRaDivCallResultSignFixPostNoX9`
    (+ trailing frame). -/
theorem saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_named_post_of_callable_post_noX9_spec_in_sdivCodeV5
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
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV5 base)
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
      (saveRaDivCallResultSignFixPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       (regOwn .x9 ** memOwn (sp + signExtend12 3936))) := by
  rw [saveRaDivCallResultSignFixPostNoX9_unfold]
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => by xperm_hyp hq)
    (saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_of_callable_post_noX9_spec_in_sdivCodeV5
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hCallable)

/-- B7: v5 prefix + divCall + result-sign-fix + saved-RA return, landing
    `saveRaDivCallCallableReturnPostNoX9` (+ trailing frame). -/
theorem saveRa_signs_abs_signXor_then_divCall_then_return_of_callable_post_noX9_spec_in_sdivCodeV5
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
    EvmAsm.Rv64.cpsTripleWithin (((49 + nSteps) + 21) + 1)
      base (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) (sdivCodeV5 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallCallableReturnPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       (regOwn .x9 ** memOwn (sp + signExtend12 3936))) := by
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
    saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_named_post_of_callable_post_noX9_spec_in_sdivCodeV5
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
  have hRetFramedInner :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (resultSignFixPost (sp + 32) resultSign
        (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
        (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)
      hRetFramePc
      (savedRaRet_spec_in_sdivCodeV5
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
        (sdivCodeV5 base)
        (((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (resultSignFixPost (sp + 32) resultSign
          (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
          (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
          saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) **
         (regOwn .x9 ** memOwn (sp + signExtend12 3936)))
        (((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (resultSignFixPost (sp + 32) resultSign
          (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
          (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
          saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) **
         (regOwn .x9 ** memOwn (sp + signExtend12 3936))) := by
    rw [hFall]
    exact hRetFramed
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [saveRaDivCallResultSignFixFrameNoX9_to_savedRaRet] at hp
      xperm_hyp hp)
    hPrefix hRetFramed'

end EvmAsm.Evm64.SDiv.Compose
