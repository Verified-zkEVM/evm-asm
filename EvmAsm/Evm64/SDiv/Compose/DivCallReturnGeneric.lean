import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFixNamedPost

namespace EvmAsm.Evm64.SDiv.Compose

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

end EvmAsm.Evm64.SDiv.Compose
