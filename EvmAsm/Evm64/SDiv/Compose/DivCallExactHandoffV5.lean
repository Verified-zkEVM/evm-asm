/-
  EvmAsm.Evm64.SDiv.Compose.DivCallExactHandoffV5

  v5 SDIV dispatch-ready handoff: wraps the v5 code adapter
  (`evm_div_callable_v5_x9owned_framed_spec_in_sdivCodeV5`) in the SDIV abs/sign
  frame, landing `saveRaDivCallCallablePostNoX9` with `regOwn .x9` + the `sp+3936`
  scratch cell carried through (instead of v4's exact `(.x9 ↦ x9Out)`).  Mirror of
  `saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_framed_spec_in_sdivCodeV4`.

  Step 2 of the SDIV `.proven` flip over `evm_div_callable_v5`.  Because M2's
  callable spec is UNCONDITIONAL, this takes no `hStack` hypothesis (unlike v4).
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallExactCallableV5
import EvmAsm.Evm64.SDiv.Compose.DivCallExactHandoff

namespace EvmAsm.Evm64.SDiv.Compose

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

end EvmAsm.Evm64.SDiv.Compose
