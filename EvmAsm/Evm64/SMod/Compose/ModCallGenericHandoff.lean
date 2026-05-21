/-
  EvmAsm.Evm64.SMod.Compose.ModCallGenericHandoff

  Generic handoff from the SMOD wrapper's normalized dispatch-ready frame into
  the appended unsigned MOD callable, parameterized by the no-NOP body proof.
-/

import EvmAsm.Evm64.SMod.Compose.BaseTopLevel
import EvmAsm.Evm64.SMod.Compose.ModCallPost

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64

theorem saveRaAbsThenModCallDispatchReadyPost_callable_from_noNop_spec_in_smodCodeV4
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (h_base : base &&& 1 = 0)
    (h_stack :
      cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff) ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreCallable sp
          (smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          ((base + modCallOff) + 4)
          v2 v5 v6
          (smodAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (smodAbsMask divisorTop)
          (smodAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp
          (smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + modCallOff) + 4)))) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (smodCodeV4 base)
      (saveRaAbsThenModCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (saveRaAbsThenModCallCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  let dividendSign := smodAbsSign dividendTop
  let divisorSign := smodAbsSign divisorTop
  let divisorMask := smodAbsMask divisorTop
  let divisorSum3 :=
    smodAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry3 :=
    smodAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let dividendAbsWord : EvmWord :=
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let retAddr := (base + modCallOff) + 4
  let privateFrame := smodModCallPrivateFrame vRa dividendTop divisorTop
  have h_stack' :
      cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff) ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreCallable sp dividendAbsWord divisorAbsWord
          retAddr v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ retAddr)) := by
    simpa [dividendAbsWord, divisorAbsWord, retAddr, divisorSum3, divisorMask,
      divisorCarry3] using h_stack
  have h_callable_raw :
      cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (retAddr &&& ~~~(1 : Word))
        (EvmAsm.Evm64.evm_mod_callable_code_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreCallable sp dividendAbsWord divisorAbsWord
          retAddr v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ retAddr)) := by
    exact
      EvmAsm.Evm64.evm_mod_callable_v4_spec_from_noNop_preserving_x1_noX9
        sp (base + wrapperEndOff) retAddr dividendAbsWord divisorAbsWord
        v2 v5 v6 divisorSum3 divisorMask divisorCarry3
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0
        h_stack'
  have h_callable_code :
      cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (retAddr &&& ~~~(1 : Word)) (smodCodeV4 base)
        (EvmAsm.Evm64.divModStackDispatchPreCallable sp dividendAbsWord divisorAbsWord
          retAddr v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ retAddr)) := by
    exact cpsTripleWithin_extend_code evm_mod_callable_code_v4_sub_smodCodeV4 h_callable_raw
  have h_callable_framed :
      cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (retAddr &&& ~~~(1 : Word)) (smodCodeV4 base)
        (EvmAsm.Evm64.divModStackDispatchPreCallable sp dividendAbsWord divisorAbsWord
          retAddr v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** privateFrame)
        ((EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ retAddr)) ** privateFrame) := by
    exact cpsTripleWithin_frameR privateFrame (by
      dsimp [privateFrame]
      exact smodModCallPrivateFrame_pcFree) h_callable_code
  rw [show retAddr &&& ~~~(1 : Word) = base + resultSignFixOff by
    dsimp [retAddr]
    exact modCall_return_andn_one_eq_resultSignFixOff base h_base] at h_callable_framed
  exact
    cpsTripleWithin_weaken
      (fun h hp => by
        rw [saveRaAbsThenModCallDispatchReadyPost_unfold_smod_components] at hp
        dsimp only at hp
        rw [EvmAsm.Evm64.divModStackDispatchPreCallable_unfold]
        dsimp [privateFrame]
        rw [smodModCallPrivateFrame_unfold]
        dsimp only
        rw [EvmAsm.Evm64.divModStackDispatchPreNoX1_unfold] at hp
        change
          (((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ retAddr) ** (.x2 ↦ᵣ v2) **
            (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ divisorSum3) **
            (.x10 ↦ᵣ divisorMask) ** (.x11 ↦ᵣ divisorCarry3) **
            (.x0 ↦ᵣ (0 : Word)) ** evmWordIs sp dividendAbsWord **
            evmWordIs (sp + (32 : Word)) divisorAbsWord **
            EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
              shiftMem nMem jMem retMem dMem dloMem scratchUn0) **
            (.x9 ↦ᵣ smodAbsSign divisorTop) **
            (.x8 ↦ᵣ smodAbsSign dividendTop) ** (.x13 ↦ᵣ smodAbsSign dividendTop) **
            (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) h
        xperm_hyp hp)
      (fun h hp => by
        rw [saveRaAbsThenModCallCallablePost_unfold]
        dsimp only
        rw [smodModCallPrivateFrame_unfold]
        dsimp only
        dsimp [privateFrame] at hp
        rw [smodModCallPrivateFrame_unfold] at hp
        dsimp only at hp
        xperm_hyp hp)
      h_callable_framed

end EvmAsm.Evm64.SMod.Compose
