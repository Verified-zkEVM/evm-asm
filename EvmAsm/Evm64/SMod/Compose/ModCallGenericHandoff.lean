/-
  EvmAsm.Evm64.SMod.Compose.ModCallGenericHandoff

  Generic handoff from the SMOD wrapper's normalized dispatch-ready frame into
  the appended unsigned MOD callable, parameterized by the no-NOP body proof.
  h_stack uses divModStackDispatchPreNoX1 (with explicit x9=divisorSign) and
  includes regOwn .x9 and memOwn of the div128 scratch cell in the postcondition.
  The scratch cell at sp + signExtend12 3936 is used by the n=3/n=2 div128 trial-call
  and must be owned by the caller.
-/

module

public import EvmAsm.Evm64.SMod.Compose.BaseTopLevel
public import EvmAsm.Evm64.SMod.Compose.ModCallPost
public import EvmAsm.Evm64.DivMod.CallableV4Mod

@[expose] public section

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64

theorem saveRaAbsThenModCallDispatchReadyPost_callable_from_noNop_spec_in_smodCodeV4
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (h_base : base &&& 1 = 0)
    (h_stack :
      cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff) ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.modCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (smodAbsSign divisorTop)
          ((base + modCallOff) + 4)
          v2 v5 v6
          (smodAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (smodAbsMask divisorTop)
          (smodAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          (sp + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp
          (smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
          EvmAsm.Rv64.regOwn .x9 **
          memOwn (sp + signExtend12 (3936 : BitVec 12)))) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (smodCodeV4 base)
      (saveRaAbsThenModCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
      (saveRaAbsThenModCallCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       memOwn (sp + signExtend12 (3936 : BitVec 12))) := by
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
  let privateFrame := smodModCallPrivateFrame vRa dividendTop
  have h_stack' :
      cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff) ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.modCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign retAddr v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          (sp + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ retAddr) ** EvmAsm.Rv64.regOwn .x9 **
          memOwn (sp + signExtend12 (3936 : BitVec 12))) := by
    simpa [dividendAbsWord, divisorAbsWord, divisorSign, retAddr, divisorSum3,
      divisorMask, divisorCarry3] using h_stack
  -- Extend body from modCode_noNop_v4 to evm_mod_callable_code_v4
  have h_body_call := cpsTripleWithin_extend_code
    EvmAsm.Evm64.modCode_noNop_v4_sub_mod_callable_code_v4 h_stack'
  -- Return instruction: JALR is a pure read of .x1, so .x1 ↦ retAddr is preserved
  have h_ret := cpsTripleWithin_extend_code
    (EvmAsm.Evm64.evm_mod_callable_code_v4_ret_sub (base := base + wrapperEndOff))
    (ret_spec_within' ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff) retAddr)
  -- Frame (PostCallable ** regOwn .x9 ** memOwn (sp+3936)) around return
  have h_ret_framed := cpsTripleWithin_frameL
    (EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
      EvmAsm.Rv64.regOwn .x9 ** memOwn (sp + signExtend12 (3936 : BitVec 12)))
    (by
      rw [EvmAsm.Evm64.modStackDispatchPostCallable_unfold,
        EvmAsm.Evm64.divScratchOwnCallNoX1_unfold, EvmAsm.Evm64.divScratchOwn_unfold]
      pcFree)
    h_ret
  -- Sequence body → ret (with xperm to bridge post-of-body to pre-of-ret)
  have h_callable_raw :
      cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (retAddr &&& ~~~(1 : Word))
        (EvmAsm.Evm64.evm_mod_callable_code_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign retAddr v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          (sp + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ retAddr) ** EvmAsm.Rv64.regOwn .x9 **
          memOwn (sp + signExtend12 (3936 : BitVec 12))) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        h_body_call h_ret_framed)
  -- Extend to smodCodeV4
  have h_callable_code :
      cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (retAddr &&& ~~~(1 : Word)) (smodCodeV4 base)
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign retAddr v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          (sp + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ retAddr) ** EvmAsm.Rv64.regOwn .x9 **
          memOwn (sp + signExtend12 (3936 : BitVec 12))) :=
    cpsTripleWithin_extend_code evm_mod_callable_code_v4_sub_smodCodeV4 h_callable_raw
  -- Frame with privateFrame (x8 ** x13 ** x18, no x9); scratchMem is inside h_stack
  have h_callable_framed :
      cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (retAddr &&& ~~~(1 : Word)) (smodCodeV4 base)
        ((EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign retAddr v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)) ** privateFrame)
        ((EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ retAddr) ** EvmAsm.Rv64.regOwn .x9 **
          memOwn (sp + signExtend12 (3936 : BitVec 12))) ** privateFrame) := by
    exact cpsTripleWithin_frameR privateFrame (by
      dsimp only [privateFrame]
      pcFree) h_callable_code
  rw [show retAddr &&& ~~~(1 : Word) = base + resultSignFixOff by
    dsimp [retAddr]
    exact modCall_return_andn_one_eq_resultSignFixOff base h_base] at h_callable_framed
  exact
    cpsTripleWithin_weaken
      (fun h hp => by
        -- Pre-weakener: dispatch-ready ** scratchMem → PreNoX1 ** scratchMem ** privateFrame
        rw [saveRaAbsThenModCallDispatchReadyPost_unfold_smod_components] at hp
        dsimp only at hp
        rw [EvmAsm.Evm64.divModStackDispatchPreNoX1_unfold]
        dsimp only [privateFrame]
        rw [smodModCallPrivateFrame_unfold]
        dsimp only
        rw [EvmAsm.Evm64.divModStackDispatchPreNoX1_unfold] at hp
        xperm_hyp hp)
      (fun h hp => by
        -- Post-weakener: (PostCallable ** .x1 ** regOwn .x9 ** memOwn) ** privateFrame
        -- → saveRaAbsThenModCallCallablePost ** memOwn (sp + 3936)
        rw [saveRaAbsThenModCallCallablePost_unfold]
        dsimp only
        rw [smodModCallPrivateFrame_unfold]
        dsimp only
        dsimp only [privateFrame] at hp
        rw [smodModCallPrivateFrame_unfold] at hp
        xperm_hyp hp)
      h_callable_framed

end EvmAsm.Evm64.SMod.Compose
