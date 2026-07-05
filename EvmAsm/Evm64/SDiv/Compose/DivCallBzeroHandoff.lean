/-
  EvmAsm.Evm64.SDiv.Compose.DivCallBzeroHandoff

  Zero-divisor callable handoff from the SDIV div-call dispatch-ready bundle.
-/

import EvmAsm.Evm64.SDiv.Compose.BzeroCallablePost
import EvmAsm.Evm64.SDiv.Compose.DispatchReadyPost
import EvmAsm.Evm64.SDiv.Compose.DivCallAbsComponents
import EvmAsm.Evm64.SDiv.Compose.DivCallExactCallable
import EvmAsm.Evm64.SDiv.Compose.DivCallFramedCallable
import EvmAsm.Evm64.DivMod.CallableBzeroV4

namespace EvmAsm.Evm64.SDiv.Compose

/-- v4 version of the named zero-divisor callable handoff from the SDIV
    dispatch-ready bundle to the zero-divisor callable post. -/
theorem saveRaDivCallDispatchReadyPost_bzero_callable_spec_in_sdivCodeV4
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSign := sdivAbsSign divisorTop
  let divisorMask := sdivAbsMask divisorTop
  let divisorSum0 := sdivAbsSum0 divisorLimb0 divisorTop
  let divisorCarry0 := sdivAbsCarry0 divisorLimb0 divisorTop
  let divisorSum1 := sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop
  let divisorCarry1 := sdivAbsCarry1 divisorLimb0 divisorLimb1 divisorTop
  let divisorSum2 := sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry2 := sdivAbsCarry2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSum3 := sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry3 := sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let resultSign := sdivDivCallResultSign dividendTop divisorTop
  let signFrameNoX9 : EvmAsm.Rv64.Assertion :=
    ((.x8 ↦ᵣ resultSign) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))
  have hCallableRaw :=
    EvmAsm.Evm64.evm_div_callable_bzero_v4_concrete_preserving_x1_spec
      sp (base + wrapperEndOff) divisorSign ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by simpa [divisorAbsWord] using hbz)
  have hCallableCode :=
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base)) hCallableRaw
  have hCallableFramed :=
    EvmAsm.Rv64.cpsTripleWithin_frameR signFrameNoX9 (by
      dsimp [signFrameNoX9]
      pcFree) hCallableCode
  have hCallableExit :
      EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          signFrameNoX9)
        (EvmAsm.Evm64.divConcretePostNoX1Frame sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v6 divisorSum3 divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** signFrameNoX9) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact hCallableFramed
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, saveRaDivCallSignFrame,
      sdivDivCallResultSign, sdivAbsSign, sdivAbsMask, sdivAbsSum0, sdivAbsCarry0,
      sdivAbsSum1, sdivAbsCarry1, sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3,
      sdivAbsCarry3] at hp ⊢
    dsimp [signFrameNoX9] at hp ⊢
    exact hp) (fun h hp => by
    have hPublic :
        ((((EvmAsm.Evm64.divStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ divisorSign)) ** signFrameNoX9) h) := by
      refine EvmAsm.Rv64.sepConj_mono ?_ ?_ h hp
      · intro hLeft hpLeft
        exact EvmAsm.Evm64.divConcretePostNoX1_weaken_callable_frame
          sp dividendAbsWord divisorAbsWord hLeft hpLeft
      · intro hRight hpRight
        exact hpRight
    rw [saveRaDivCallBzeroCallablePost_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign, signFrameNoX9,
      saveRaDivCallSignFrame, sdivDivCallResultSign, sdivAbsSign] at hp hPublic ⊢
    xperm_hyp hPublic) hCallableExit

end EvmAsm.Evm64.SDiv.Compose
