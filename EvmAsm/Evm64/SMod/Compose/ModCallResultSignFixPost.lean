/-
  EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixPost

  Frame reshaping between the unsigned MOD callable post and the SMOD-local
  result-sign-fix precondition.
-/

module

public import EvmAsm.Evm64.SMod.Compose.ModCallPost
public import EvmAsm.Evm64.SMod.Compose.ResultSignFixOwn
public import EvmAsm.Rv64.Tactics.XSimp

@[expose] public section

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64.Tactics

@[irreducible]
def smodModCallResultSignFixFrame
    (vRa sp base dividendTop : Word) (dividendAbsWord : EvmWord) :
    EvmAsm.Rv64.Assertion :=
  let dividendSign := smodAbsSign dividendTop
  (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
    EvmAsm.Rv64.regOwn .x9 ** (.x8 ↦ᵣ dividendSign) **
    (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
    EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 **
    EvmAsm.Rv64.regOwn .x6 ** evmWordIs sp dividendAbsWord **
    EvmAsm.Evm64.divScratchOwnCallNoX1 sp

theorem smodModCallResultSignFixFrame_unfold
    {vRa sp base dividendTop : Word} {dividendAbsWord : EvmWord} :
    smodModCallResultSignFixFrame vRa sp base dividendTop dividendAbsWord =
      (let dividendSign := smodAbsSign dividendTop
       (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
         EvmAsm.Rv64.regOwn .x9 ** (.x8 ↦ᵣ dividendSign) **
         (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 **
         EvmAsm.Rv64.regOwn .x6 ** evmWordIs sp dividendAbsWord **
         EvmAsm.Evm64.divScratchOwnCallNoX1 sp) := by
  delta smodModCallResultSignFixFrame
  rfl

theorem smodModCallResultSignFixFrame_pcFree
    {vRa sp base dividendTop : Word} {dividendAbsWord : EvmWord} :
    (smodModCallResultSignFixFrame vRa sp base dividendTop dividendAbsWord).pcFree := by
  rw [smodModCallResultSignFixFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  dsimp only
  pcFree

instance pcFreeInst_smodModCallResultSignFixFrame
    (vRa sp base dividendTop : Word) (dividendAbsWord : EvmWord) :
    EvmAsm.Rv64.Assertion.PCFree
      (smodModCallResultSignFixFrame vRa sp base dividendTop dividendAbsWord) :=
  ⟨smodModCallResultSignFixFrame_pcFree⟩

theorem saveRaAbsThenModCallCallablePost_smodResultSignFixPreOwnScratch
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaAbsThenModCallCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord : EvmWord :=
         smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord : EvmWord :=
         smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
       let resultSign := smodAbsSign dividendTop
       smodResultSignFixPreOwnScratch (sp + 32) resultSign
         (modWord.getLimbN 0) (modWord.getLimbN 1)
         (modWord.getLimbN 2) (modWord.getLimbN 3) **
       smodModCallResultSignFixFrame vRa sp base dividendTop dividendAbsWord) := by
  dsimp only
  rw [saveRaAbsThenModCallCallablePost_unfold]
  dsimp only
  rw [EvmAsm.Evm64.modStackDispatchPostCallable_unfold]
  rw [smodResultSignFixPreOwnScratch_unfold,
    smodModCallResultSignFixFrame_unfold, smodModCallPrivateFrame_unfold,
    evmWordIs_sp32_unfold]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (0 : BitVec 12) : Word) = sp + 32 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (8 : BitVec 12) : Word) = sp + 40 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (16 : BitVec 12) : Word) = sp + 48 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (24 : BitVec 12) : Word) = sp + 56 by bv_addr]
  xperm

end EvmAsm.Evm64.SMod.Compose
