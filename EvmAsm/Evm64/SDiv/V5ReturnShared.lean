/- Shared declaration home for the SDIV V5 callable and return handoff wrappers. -/

import EvmAsm.Evm64.SDiv.Compose.CodeHandlesV5
import EvmAsm.Evm64.DivMod.Compose.DivCallableV5Assembly
import EvmAsm.Evm64.SDiv.DivCallExactShared
import EvmAsm.Evm64.SDiv.DivCallHandoffChainShared
import EvmAsm.Evm64.SDiv.Compose.PrefixChainV5
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwnV5
import EvmAsm.Evm64.SDiv.Compose.BaseCodeV5

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- v5 SDIV wrapper: M2's x9-owned callable spec framed by `F` and lifted onto
    `sdivCodeV5` (the embedded `evm_div_callable_v5` at `wrapperEndOff`).  x9 is
    already owned in the post and the `sp+3936` scratch cell rides through. -/
theorem evm_div_callable_v5_x9owned_framed_spec_in_sdivCodeV5
    {F : Assertion} [Assertion.PCFree F]
    (sp base x9In raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : (((base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV5 base)
      ((EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem)) ** F)
      ((EvmAsm.Evm64.divStackDispatchPostCallableX9Owned sp a b raVal **
        memOwn (sp + signExtend12 3936)) ** F) := by
  exact cpsTripleWithin_extend_code
    (hmono := evm_div_callable_code_v5_sub_sdivCodeV5 (base := base))
    (cpsTripleWithin_frameR F (by pcFree)
      (EvmAsm.Evm64.evm_div_callable_v5_stack_spec_within_x9owned
        sp (base + wrapperEndOff) a b x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign))


open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- v5 dispatch-ready callable handoff: from `saveRaDivCallDispatchReadyPost`
    (+ the `sp+3936` scratch cell) to `saveRaDivCallCallablePostNoX9` with x9
    owned and the scratch cell carried, over `sdivCodeV5`. -/
theorem saveRaDivCallDispatchReadyPost_x9owned_divCode_framed_spec_in_sdivCodeV5
    {F : Assertion} [Assertion.PCFree F]
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbase : base &&& 1 = 0)
    (halign : (((base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV5 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem) ** F)
      ((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (regOwn .x9 ** memOwn (sp + signExtend12 3936))) ** F) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSign := sdivAbsSign divisorTop
  let divisorMask := sdivAbsMask divisorTop
  let divisorSum3 := sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry3 := sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let resultSign := sdivDivCallResultSign dividendTop divisorTop
  let signFrameNoX9 : Assertion :=
    (.x8 ↦ᵣ resultSign) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))
  have hCallable :=
    evm_div_callable_v5_x9owned_framed_spec_in_sdivCodeV5
      (F := signFrameNoX9 ** F)
      sp base divisorSign ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem halign
  rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [saveRaDivCallDispatchReadyPost_unfold] at hp
      dsimp only [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask,
        divisorSum3, divisorCarry3, resultSign, signFrameNoX9,
        sdivDivCallResultSign, sdivAbsSign, sdivAbsMask,
        sdivAbsSum0, sdivAbsCarry0, sdivAbsSum1, sdivAbsCarry1,
        sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3, sdivAbsCarry3] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      rw [divStackDispatchPostCallableX9Owned_unfold] at hp
      rw [saveRaDivCallCallablePostNoX9_unfold]
      dsimp only [dividendAbsWord, divisorAbsWord, resultSign, signFrameNoX9,
        sdivDivCallResultSign] at hp ⊢
      xperm_hyp hp)
    hCallable


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
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV5 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (saveRaDivCallCallablePostNoX9 vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
         (regOwn .x9 ** memOwn (sp + signExtend12 3936)))) :
    EvmAsm.Rv64.cpsTripleWithin ((49 + nSteps) + 21)
      base ((base + resultSignFixOff) + 84) (sdivCodeV5 base)
      ((saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
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
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem
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
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV5 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (saveRaDivCallCallablePostNoX9 vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
         (regOwn .x9 ** memOwn (sp + signExtend12 3936)))) :
    EvmAsm.Rv64.cpsTripleWithin ((49 + nSteps) + 21)
      base ((base + resultSignFixOff) + 84) (sdivCodeV5 base)
      ((saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
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
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base hCallable)

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
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV5 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (saveRaDivCallCallablePostNoX9 vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
         (regOwn .x9 ** memOwn (sp + signExtend12 3936)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + nSteps) + 21) + 1)
      base (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) (sdivCodeV5 base)
      ((saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
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
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base hCallable
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


open EvmAsm.Rv64

/-- B8: v5 SDIV wrapper prefix + exact unsigned-DIV callable (M2 feed) + result
    sign-fix + saved-RA return, from the concrete step-2 handoff, over
    `sdivCodeV5`. -/
theorem saveRa_signs_abs_signXor_then_divCall_exact_then_return_normalized_named_post_from_handoff_spec_in_sdivCodeV5
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (halign : (((base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV5 base)
      ((saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (saveRaDivCallCallableReturnPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       (regOwn .x9 ** memOwn (sp + signExtend12 3936))) := by
  have hExit :
      (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) =
        (vRa &&& ~~~(1 : Word)) := by
    rw [EvmAsm.Rv64.signExtend12_0]
    simp [BitVec.add_zero]
  rw [← hExit]
  have hStep2 :=
    saveRaDivCallDispatchReadyPost_x9owned_divCode_framed_spec_in_sdivCodeV5
      (F := empAssertion)
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem hbase halign
  simp only [sepConj_emp_right'] at hStep2
  exact
    saveRa_signs_abs_signXor_then_divCall_then_return_of_callable_post_noX9_spec_in_sdivCodeV5
      (nSteps := EvmAsm.Evm64.unifiedDivBound + 1)
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base hStep2

end EvmAsm.Evm64.SDiv.Compose
