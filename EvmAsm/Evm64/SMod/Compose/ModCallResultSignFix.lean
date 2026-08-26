/-
  EvmAsm.Evm64.SMod.Compose.ModCallResultSignFix

  Composition from the unsigned MOD callable return point through the SMOD-local
  result-sign-fix block.
-/

module

public import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixPost

@[expose] public section

namespace EvmAsm.Evm64.SMod.Compose

theorem saveRaAbsThenModCall_then_resultSignFix_of_callable_post_spec_in_smodCodeV4
    {nSteps : Nat}
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps
        (base + wrapperEndOff) (base + resultSignFixOff) (smodCodeV4 base)
        (saveRaAbsThenModCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
        (saveRaAbsThenModCallCallablePost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
          EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)))) :
    EvmAsm.Rv64.cpsTripleWithin (nSteps + 21)
      (base + wrapperEndOff) ((base + resultSignFixOff) + 84) (smodCodeV4 base)
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
       smodResultSignFixPost (sp + 32) resultSign
         (modWord.getLimbN 0) (modWord.getLimbN 1)
         (modWord.getLimbN 2) (modWord.getLimbN 3) **
       smodModCallResultSignFixFrame vRa sp base dividendTop
         dividendAbsWord **
       EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12))) := by
  let dividendAbsWord : EvmWord :=
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
  let resultSign := smodAbsSign dividendTop
  let frame := smodModCallResultSignFixFrame vRa sp base dividendTop
    dividendAbsWord ** EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12))
  have hFramePc : frame.pcFree := by
    dsimp [frame]
    exact EvmAsm.Rv64.pcFree_sepConj
      smodModCallResultSignFixFrame_pcFree EvmAsm.Rv64.pcFree_memOwn
  have hFix :
      EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
        ((base + resultSignFixOff) + 84) (smodCodeV4 base)
        (smodResultSignFixPreOwnScratch (sp + 32) resultSign
          (modWord.getLimbN 0) (modWord.getLimbN 1)
          (modWord.getLimbN 2) (modWord.getLimbN 3) ** frame)
        (smodResultSignFixPost (sp + 32) resultSign
          (modWord.getLimbN 0) (modWord.getLimbN 1)
          (modWord.getLimbN 2) (modWord.getLimbN 3) ** frame) := by
    exact EvmAsm.Rv64.cpsTripleWithin_frameR frame hFramePc
      (resultSignFix_regOwn_scratch_spec_in_smodCodeV4
        (sp + 32) resultSign
        (modWord.getLimbN 0) (modWord.getLimbN 1)
        (modWord.getLimbN 2) (modWord.getLimbN 3) base)
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [saveRaAbsThenModCallCallablePost_smodResultSignFixPreOwnScratch] at hp
      dsimp only [dividendAbsWord, divisorAbsWord, modWord, resultSign] at hp
      dsimp only [frame]
      xperm_hyp hp)
    hCallable hFix

end EvmAsm.Evm64.SMod.Compose
