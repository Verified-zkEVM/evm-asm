/-
  EvmAsm.Evm64.SMod.Compose.ResultSignFixView

  Views for the SMOD result-sign-fix postcondition.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFix
import EvmAsm.Evm64.SMod.Compose.Words

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Evm64.SDiv.Compose (resultSignFixPost resultSignFixPost_unfold)

/-- Postcondition view for a general SMOD result-sign-fix output: the four
    result memory cells fold into the named result-sign-fixed EVM word, while
    the scratch registers remain exposed explicitly. -/
theorem resultSignFixPost_smodResultSign_word
    (sp dividendTop limb0 limb1 limb2 limb3 : Word) :
    let resultSign := dividendTop >>> (63 : BitVec 6).toNat
    let mask := (0 : Word) - resultSign
    let sum0 := (limb0 ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := (limb1 ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := (limb2 ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := (limb3 ^^^ mask) + carry2
    let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
    resultSignFixPost sp resultSign limb0 limb1 limb2 limb3 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ resultSign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       evmWordIs sp (smodResultSignFixedWord dividendTop limb0 limb1 limb2 limb3)) := by
  dsimp only
  rw [resultSignFixPost_unfold, evmWordIs_sp_unfold]
  unfold smodResultSignFixedWord
  dsimp only
  simp only [EvmAsm.Rv64.signExtend12_0, EvmAsm.Rv64.signExtend12_8,
    EvmAsm.Rv64.signExtend12_16, EvmAsm.Rv64.signExtend12_24,
    EvmWord.getLimbN_fromLimbs_gen_0, EvmWord.getLimbN_fromLimbs_gen_1,
    EvmWord.getLimbN_fromLimbs_gen_2, EvmWord.getLimbN_fromLimbs_gen_3]
  rw [show (sp + 0 : Word) = sp by bv_decide]

/-- Postcondition view for the SMOD zero-divisor branch after result-sign
    fixup: conditional negation of the zero modulo result is still zero. -/
theorem resultSignFixPost_smodResultSign_zero_word
    (sp dividendTop : Word) :
    let resultSign := dividendTop >>> (63 : BitVec 6).toNat
    let mask := (0 : Word) - resultSign
    let sum0 := ((0 : Word) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := ((0 : Word) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := ((0 : Word) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := ((0 : Word) ^^^ mask) + carry2
    let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
    resultSignFixPost sp resultSign 0 0 0 0 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ resultSign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ carry3) **
       evmWordIs sp (0 : EvmWord)) := by
  dsimp only
  obtain h_sign | h_sign := smodResultSign_bool dividendTop
  · rw [h_sign]
    rw [resultSignFixPost_unfold, evmWordIs_zero]
    dsimp only
    simp only [EvmAsm.Rv64.signExtend12_0, EvmAsm.Rv64.signExtend12_8,
      EvmAsm.Rv64.signExtend12_16, EvmAsm.Rv64.signExtend12_24]
    simp
  · rw [h_sign]
    rw [resultSignFixPost_unfold, evmWordIs_zero]
    dsimp only
    simp only [EvmAsm.Rv64.signExtend12_0, EvmAsm.Rv64.signExtend12_8,
      EvmAsm.Rv64.signExtend12_16, EvmAsm.Rv64.signExtend12_24]
    simp

end EvmAsm.Evm64.SMod.Compose
