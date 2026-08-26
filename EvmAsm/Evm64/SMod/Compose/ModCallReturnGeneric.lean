/-
  EvmAsm.Evm64.SMod.Compose.ModCallReturnGeneric

  Composition from the unsigned MOD callable and SMOD result-sign-fix block
  through the final saved-`ra` return instruction.
-/

module

public import EvmAsm.Evm64.SMod.Compose.SavedRaRetFrame
public import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixGeneric
public import EvmAsm.Evm64.SMod.Compose.SavedRaRet

public section

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64.Tactics

theorem saveRaAbsThenModCall_then_return_from_noNop_spec_in_smodCodeV4
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (h_base : base &&& 1 = 0)
    (h_stack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
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
          (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp
          (smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
          EvmAsm.Rv64.regOwn .x9 **
          EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)))) :
    EvmAsm.Rv64.cpsTripleWithin (((EvmAsm.Evm64.unifiedDivBound + 1) + 21) + 1)
      (base + wrapperEndOff)
      (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word))
      (smodCodeV4 base)
      (saveRaAbsThenModCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
        (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
      (let dividendAbsWord : EvmWord :=
         smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord : EvmWord :=
         smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
       let resultSign := smodAbsSign dividendTop
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (smodResultSignFixPost (sp + 32) resultSign
         (modWord.getLimbN 0) (modWord.getLimbN 1)
         (modWord.getLimbN 2) (modWord.getLimbN 3) **
        smodSavedRaRetFrame sp base dividendTop dividendAbsWord) **
       EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12))) := by
  let dividendAbsWord : EvmWord :=
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
  let resultSign := smodAbsSign dividendTop
  have hPrefix :=
    saveRaAbsThenModCall_then_resultSignFix_from_noNop_spec_in_smodCodeV4
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem
      h_base h_stack
  have hRetFramePc :
      ((smodResultSignFixPost (sp + 32) resultSign
        (modWord.getLimbN 0) (modWord.getLimbN 1)
        (modWord.getLimbN 2) (modWord.getLimbN 3) **
       smodSavedRaRetFrame sp base dividendTop dividendAbsWord) **
       EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12))).pcFree := by
    pcFree
  have hRetFramed :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      ((smodResultSignFixPost (sp + 32) resultSign
        (modWord.getLimbN 0) (modWord.getLimbN 1)
        (modWord.getLimbN 2) (modWord.getLimbN 3) **
       smodSavedRaRetFrame sp base dividendTop dividendAbsWord) **
       EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)))
      hRetFramePc
      (savedRaRet_spec_in_smodCodeV4
        (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) base)
  have hFall :
      (base + resultSignFixOff) + 84 = base + savedRaRetOff := by
    simp [resultSignFixOff, savedRaRetOff]
    bv_addr
  have hRetFramed' :
      EvmAsm.Rv64.cpsTripleWithin 1 ((base + resultSignFixOff) + 84)
        (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
          EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word))
        (smodCodeV4 base)
        ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         ((smodResultSignFixPost (sp + 32) resultSign
          (modWord.getLimbN 0) (modWord.getLimbN 1)
          (modWord.getLimbN 2) (modWord.getLimbN 3) **
          smodSavedRaRetFrame sp base dividendTop dividendAbsWord) **
          EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12))))
        ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         ((smodResultSignFixPost (sp + 32) resultSign
          (modWord.getLimbN 0) (modWord.getLimbN 1)
          (modWord.getLimbN 2) (modWord.getLimbN 3) **
          smodSavedRaRetFrame sp base dividendTop dividendAbsWord) **
          EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)))) := by
    rw [hFall]
    exact hRetFramed
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [smodModCallResultSignFixFrame_to_savedRaRet] at hp
      xperm_hyp hp)
    hPrefix hRetFramed'

end EvmAsm.Evm64.SMod.Compose
