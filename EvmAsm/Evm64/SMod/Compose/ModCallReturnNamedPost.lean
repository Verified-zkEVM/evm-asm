/-
  EvmAsm.Evm64.SMod.Compose.ModCallReturnNamedPost

  Named postcondition for the SMOD path after the unsigned MOD callable,
  result-sign-fix block, and final saved-`ra` return instruction.
-/

module

public import EvmAsm.Evm64.SMod.Compose.ModCallReturnGeneric
public import EvmAsm.Evm64.SMod.Compose.ResultSignFixView

@[expose] public section

namespace EvmAsm.Evm64.SMod.Compose

@[irreducible]
def saveRaAbsThenModCallReturnPost
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    EvmAsm.Rv64.Assertion :=
  let dividendAbsWord : EvmWord :=
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
  let resultSign := smodAbsSign dividendTop
  let mask := (0 : Word) - resultSign
  let sum0 := (modWord.getLimbN 0 ^^^ mask) + resultSign
  let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
  let sum1 := (modWord.getLimbN 1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (modWord.getLimbN 2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (modWord.getLimbN 3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
    (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) **
      (.x13 ↦ᵣ resultSign) ** (.x10 ↦ᵣ mask) **
      (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
      evmWordIs (sp + 32)
        (smodResultSignFixedWord dividendTop
          (modWord.getLimbN 0) (modWord.getLimbN 1)
          (modWord.getLimbN 2) (modWord.getLimbN 3))) **
      smodSavedRaRetFrame sp base dividendTop dividendAbsWord)

theorem saveRaAbsThenModCallReturnPost_unfold
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaAbsThenModCallReturnPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord : EvmWord :=
         smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord : EvmWord :=
         smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
       let resultSign := smodAbsSign dividendTop
       let mask := (0 : Word) - resultSign
       let sum0 := (modWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (modWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (modWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (modWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) **
           (.x13 ↦ᵣ resultSign) ** (.x10 ↦ᵣ mask) **
           (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
           evmWordIs (sp + 32)
             (smodResultSignFixedWord dividendTop
               (modWord.getLimbN 0) (modWord.getLimbN 1)
               (modWord.getLimbN 2) (modWord.getLimbN 3))) **
           smodSavedRaRetFrame sp base dividendTop dividendAbsWord)) := by
  delta saveRaAbsThenModCallReturnPost
  rfl

theorem saveRaAbsThenModCall_then_return_named_post_from_noNop_spec_in_smodCodeV4
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
      (saveRaAbsThenModCallReturnPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12))) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => by
      rw [saveRaAbsThenModCallReturnPost_unfold]
      dsimp only
      rw [← smodResultSignFixPost_smodResultSign_word]
      xperm_hyp hq)
    (saveRaAbsThenModCall_then_return_from_noNop_spec_in_smodCodeV4
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem
      h_base h_stack)

end EvmAsm.Evm64.SMod.Compose
