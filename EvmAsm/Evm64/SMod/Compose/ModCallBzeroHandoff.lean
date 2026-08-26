/-
  EvmAsm.Evm64.SMod.Compose.ModCallBzeroHandoff

  Zero-divisor handoff from the SMOD wrapper's normalized dispatch-ready frame
  into the appended unsigned MOD callable.
-/

module

public import EvmAsm.Evm64.SMod.Compose.BaseTopLevel
public import EvmAsm.Evm64.SMod.Compose.ModCallPost

public section

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64

theorem saveRaAbsThenModCallDispatchReadyPost_bzero_callable_spec_in_smodCodeV4
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (h_base : base &&& 1 = 0)
    (h_bzero :
      smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
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
  -- New: 2-arg privateFrame (no x9). Frame x9 separately for the bzero callable.
  -- x9 is placed first so that frameWithX9 is right-associative after unfolding.
  let privateFrame := smodModCallPrivateFrame vRa dividendTop
  let frameWithX9 : EvmAsm.Rv64.Assertion :=
    (.x9 ↦ᵣ divisorSign) ** privateFrame
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
      EvmAsm.Evm64.evm_mod_callable_bzero_v4_preserving_x1_noX9_spec
        sp (base + wrapperEndOff) retAddr dividendAbsWord divisorAbsWord
        v2 v5 v6 divisorSum3 divisorMask divisorCarry3
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0
        (by simpa [divisorAbsWord] using h_bzero)
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
  -- Frame with frameWithX9 = (.x9 ↦ divisorSign) ** privateFrame
  have h_callable_framed :
      cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (retAddr &&& ~~~(1 : Word)) (smodCodeV4 base)
        (EvmAsm.Evm64.divModStackDispatchPreCallable sp dividendAbsWord divisorAbsWord
          retAddr v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** frameWithX9)
        ((EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ retAddr)) ** frameWithX9) := by
    exact cpsTripleWithin_frameR frameWithX9 (by
      dsimp only [frameWithX9]
      pcFree) h_callable_code
  rw [show retAddr &&& ~~~(1 : Word) = base + resultSignFixOff by
    dsimp [retAddr]
    exact modCall_return_andn_one_eq_resultSignFixOff base h_base] at h_callable_framed
  exact
    cpsTripleWithin_weaken
      (fun h hp => by
        rw [saveRaAbsThenModCallDispatchReadyPost_unfold_smod_components] at hp
        dsimp only at hp
        rw [EvmAsm.Evm64.divModStackDispatchPreCallable_unfold]
        dsimp only [frameWithX9, privateFrame]
        rw [smodModCallPrivateFrame_unfold]
        dsimp only
        rw [EvmAsm.Evm64.divModStackDispatchPreNoX1_unfold] at hp
        -- frameWithX9 = (.x9 ↦ divisorSign) ** privateFrame is already right-assoc
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
        -- Unfold frameWithX9 and privateFrame in hp
        dsimp only [frameWithX9, privateFrame] at hp
        rw [smodModCallPrivateFrame_unfold] at hp
        dsimp only at hp
        -- hp : ((moddispatch ** .x1) ** ((.x9 ↦ divisorSign) ** (x8 ** x13 ** x18))) h
        -- Decompose to extract x9 and weaken to regOwn .x9
        obtain ⟨hAB, hX9C, hd1, hu1, hAB_h, hX9C_h⟩ := hp
        -- hX9C_h : ((.x9 ↦ divisorSign) ** (x8 ** x13 ** x18)) hX9C
        obtain ⟨hX9, hC, hd3, hu3, hX9_h, hC_h⟩ := hX9C_h
        have hregown := regIs_implies_regOwn .x9 hX9 hX9_h
        -- Build (regOwn .x9 ** (x8 ** x13 ** x18)) (hX9 ∪ hC)
        have h_inner : (EvmAsm.Rv64.regOwn .x9 **
            ((.x8 ↦ᵣ smodAbsSign dividendTop) ** (.x13 ↦ᵣ smodAbsSign dividendTop) **
             (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))) (hX9.union hC) :=
          ⟨hX9, hC, hd3, rfl, hregown, hC_h⟩
        -- hAB.Disjoint (hX9 ∪ hC) follows directly from hu3 and hd1
        have h_new_disjoint : hAB.Disjoint (hX9.union hC) := by
          rw [hu3]; exact hd1
        have h_new_union : hAB.union (hX9.union hC) = h := by
          rw [hu3]; exact hu1
        -- Construct hp' with weakened x9
        have hp' : ((EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
                     (.x1 ↦ᵣ retAddr)) **
                    (EvmAsm.Rv64.regOwn .x9 **
                     ((.x8 ↦ᵣ smodAbsSign dividendTop) ** (.x13 ↦ᵣ smodAbsSign dividendTop) **
                      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))))) h :=
          ⟨hAB, hX9.union hC, h_new_disjoint, h_new_union, hAB_h, h_inner⟩
        -- re-associate from ((A ** B) ** (C ** D)) to A ** (B ** (C ** D)) then exact
        rw [sepConj_assoc] at hp'
        exact hp')
      h_callable_framed

end EvmAsm.Evm64.SMod.Compose
