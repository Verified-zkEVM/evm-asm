/-
  EvmAsm.Evm64.SDiv.Compose.DivCallExactHandoff

  Exact-`x1` callable handoff from the SDIV div-call dispatch-ready bundle.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallExactCallable
import EvmAsm.Evm64.SDiv.Compose.DivCallFramedCallable

namespace EvmAsm.Evm64.SDiv.Compose

/-- v4 generic exact-`x1` callable handoff from the SDIV dispatch-ready bundle.
    The branch-specific obligation is the `sharedDivModCodeNoNop_v4` proof
    `hStack`, whose precondition already carries SDIV's exact return address
    in `x1`. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_spec_in_sdivCodeV4
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (saveRaDivCallCallablePostNoX9 vRa sp base
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
    (.x8 ↦ᵣ resultSign) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))
  have hCallableFramed :=
    evm_div_callable_v4_preserving_x1_exact_pre_framed_spec_in_sdivCodeV4
      (F := signFrameNoX9)
      sp base divisorSign ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by
        dsimp [dividendAbsWord, divisorAbsWord, divisorSum3, divisorMask,
          divisorCarry3] at hStack ⊢
        exact hStack)
  have hCallableExit :
      EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          signFrameNoX9)
        ((EvmAsm.Evm64.divStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          signFrameNoX9) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact hCallableFramed
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, saveRaDivCallSignFrame,
      sdivDivCallResultSign, sdivAbsSign, sdivAbsMask, sdivAbsSum0, sdivAbsCarry0,
      sdivAbsSum1, sdivAbsCarry1, sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3,
      sdivAbsCarry3, signFrameNoX9] at hp ⊢
    exact hp) (fun h hp => by
    rw [saveRaDivCallCallablePostNoX9_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign,
      signFrameNoX9, sdivDivCallResultSign, sdivAbsSign] at hp ⊢
    exact hp) hCallableExit

/-- v4 exact callable handoff for already-framed unsigned-DIV body proofs that
    return an exact `x9` value and carry an explicit PC-free frame. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 x9Out : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ x9Out)) ** F)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ x9Out)) ** F)) := by
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
    (.x8 ↦ᵣ resultSign) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))
  have hCallableFramed :=
    evm_div_callable_v4_preserving_x1_x9out_exact_pre_body_framed_spec_in_sdivCodeV4
      (F := signFrameNoX9 ** F)
      sp base divisorSign x9Out ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by
        dsimp [dividendAbsWord, divisorAbsWord, divisorSum3, divisorMask,
          divisorCarry3] at hStack ⊢
        exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
          xperm_hyp hp) (fun h hp => by
          xperm_hyp hp)
          (EvmAsm.Rv64.cpsTripleWithin_frameR signFrameNoX9 (by
            dsimp [signFrameNoX9]
            pcFree) hStack))
  have hCallableExit :
      EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        ((EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask
          divisorCarry3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** signFrameNoX9) ** F)
        ((((EvmAsm.Evm64.divStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) ** signFrameNoX9) **
          (.x9 ↦ᵣ x9Out)) ** F) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
      xperm_hyp hp) (fun h hp => by
      xperm_hyp hp) hCallableFramed
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, saveRaDivCallSignFrame,
      sdivDivCallResultSign, sdivAbsSign, sdivAbsMask, sdivAbsSum0, sdivAbsCarry0,
      sdivAbsSum1, sdivAbsCarry1, sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3,
      sdivAbsCarry3, signFrameNoX9] at hp ⊢
    exact hp) (fun h hp => by
    rw [saveRaDivCallCallablePostNoX9_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign,
      signFrameNoX9, sdivDivCallResultSign, sdivAbsSign] at hp ⊢
    exact hp) hCallableExit

/-- v4 exact callable handoff for already-framed full `divCode_noNop_v4`
    unsigned-DIV body proofs that return an exact `x9` value. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 x9Out : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ x9Out)) ** F)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ x9Out)) ** F)) := by
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
    (.x8 ↦ᵣ resultSign) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))
  have hCallableFramed :=
    evm_div_callable_v4_preserving_x1_x9out_exact_pre_divCode_body_framed_spec_in_sdivCodeV4
      (F := signFrameNoX9 ** F)
      sp base divisorSign x9Out ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by
        dsimp [dividendAbsWord, divisorAbsWord, divisorSum3, divisorMask,
          divisorCarry3] at hStack ⊢
        exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
          xperm_hyp hp) (fun h hp => by
          xperm_hyp hp)
          (EvmAsm.Rv64.cpsTripleWithin_frameR signFrameNoX9 (by
            dsimp [signFrameNoX9]
            pcFree) hStack))
  have hCallableExit :
      EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        ((EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask
          divisorCarry3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** signFrameNoX9) ** F)
        ((((EvmAsm.Evm64.divStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) ** signFrameNoX9) **
          (.x9 ↦ᵣ x9Out)) ** F) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
      xperm_hyp hp) (fun h hp => by
      xperm_hyp hp) hCallableFramed
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, saveRaDivCallSignFrame,
      sdivDivCallResultSign, sdivAbsSign, sdivAbsMask, sdivAbsSum0, sdivAbsCarry0,
      sdivAbsSum1, sdivAbsCarry1, sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3,
      sdivAbsCarry3, signFrameNoX9] at hp ⊢
    exact hp) (fun h hp => by
    rw [saveRaDivCallCallablePostNoX9_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign,
      signFrameNoX9, sdivDivCallResultSign, sdivAbsSign] at hp ⊢
    exact hp) hCallableExit

/-- v4 exact callable handoff for full `divCode_noNop_v4` unsigned-DIV body
    proofs that transform an explicit frame and return an exact `x9` value. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_frame_transform_spec_in_sdivCodeV4
    {FPre FPost : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree FPost]
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 x9Out : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** FPre)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ x9Out)) ** FPost)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** FPre)
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ x9Out)) ** FPost)) := by
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
    (.x8 ↦ᵣ resultSign) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))
  have hCallableFramed :=
    evm_div_callable_v4_preserving_x1_x9out_exact_pre_divCode_body_frame_transform_spec_in_sdivCodeV4
      (FPre := signFrameNoX9 ** FPre) (FPost := signFrameNoX9 ** FPost)
      sp base divisorSign x9Out ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by
        dsimp [dividendAbsWord, divisorAbsWord, divisorSum3, divisorMask,
          divisorCarry3] at hStack ⊢
        exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
          xperm_hyp hp) (fun h hp => by
          xperm_hyp hp)
          (EvmAsm.Rv64.cpsTripleWithin_frameR signFrameNoX9 (by
            dsimp [signFrameNoX9]
            pcFree) hStack))
  have hCallableExit :
      EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        ((EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask
          divisorCarry3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** signFrameNoX9) ** FPre)
        ((((EvmAsm.Evm64.divStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) ** signFrameNoX9) **
          (.x9 ↦ᵣ x9Out)) ** FPost) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
      xperm_hyp hp) (fun h hp => by
      xperm_hyp hp) hCallableFramed
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, saveRaDivCallSignFrame,
      sdivDivCallResultSign, sdivAbsSign, sdivAbsMask, sdivAbsSum0, sdivAbsCarry0,
      sdivAbsSum1, sdivAbsCarry1, sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3,
      sdivAbsCarry3, signFrameNoX9] at hp ⊢
    exact hp) (fun h hp => by
    rw [saveRaDivCallCallablePostNoX9_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign,
      signFrameNoX9, sdivDivCallResultSign, sdivAbsSign] at hp ⊢
    exact hp) hCallableExit

/-- v4 exact callable handoff for full `divCode_noNop_v4` body proofs whose
    precondition has the N1-style zero `x9` value. This specializes the generic
    SDIV handoff to the branch where the saved divisor sign is zero. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_zeroX9_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 x9Out : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hdivisorSign :
      sdivAbsSign divisorTop = EvmAsm.Rv64.signExtend12 (4 : BitVec 12) - (4 : Word))
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (EvmAsm.Rv64.signExtend12 (4 : BitVec 12) - (4 : Word))
          ((base + divCallOff) + 4)
          v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ x9Out)) ** F)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ x9Out)) ** F)) := by
  apply saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_framed_spec_in_sdivCodeV4
    (F := F) vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
    divisorLimb0 divisorLimb1 divisorLimb2 divisorTop v2 v5 v6 x9Out
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 hbase
  rwa [hdivisorSign]

end EvmAsm.Evm64.SDiv.Compose
