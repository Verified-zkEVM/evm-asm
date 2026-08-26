/-
  EvmAsm.Evm64.SDiv.Compose.BzeroPost

  Named postconditions and frame reshaping lemmas for the SDIV zero-divisor
  div-call path.
-/

module

public import EvmAsm.Evm64.SDiv.Compose.BzeroCallablePost
public import EvmAsm.Evm64.SDiv.Compose.BzeroFrames
public import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwnPre

@[expose] public section

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

/-- Zero-divisor callable post reshaped as the result-sign-fix precondition
    over the current quotient cell plus an explicit frame. -/
theorem saveRaDivCallBzeroCallablePost_resultSignFixPreOwnScratch
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       resultSignFixPreOwnScratch (sp + 32) resultSign 0 0 0 0 **
       saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord) := by
  rw [saveRaDivCallBzeroCallablePost_unfold_zero_quotient hbz]
  dsimp only
  rw [resultSignFixPreOwnScratch_unfold,
    saveRaDivCallBzeroResultSignFixFrame_unfold, evmWordIs_zero]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (0 : BitVec 12) : Word) = sp + 32 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (8 : BitVec 12) : Word) = (sp + 32) + 8 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (16 : BitVec 12) : Word) = (sp + 32) + 16 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (24 : BitVec 12) : Word) = (sp + 32) + 24 by bv_addr]
  xperm

/-- Callable post reshaped as the result-sign-fix precondition over the
    unsigned DIV quotient plus the saved-RA/sign frame. The zero-divisor
    specialization below is the same shape with the quotient reduced to zero. -/
theorem saveRaDivCallBzeroCallablePost_resultSignFixPreOwnScratch_quotient
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       resultSignFixPreOwnScratch (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
       saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord) := by
  rw [saveRaDivCallBzeroCallablePost_unfold,
    EvmAsm.Evm64.divStackDispatchPostCallable_unfold]
  dsimp only
  rw [resultSignFixPreOwnScratch_unfold,
    saveRaDivCallBzeroResultSignFixFrame_unfold, evmWordIs_sp32_unfold]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (0 : BitVec 12) : Word) = sp + 32 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (8 : BitVec 12) : Word) = sp + 40 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (16 : BitVec 12) : Word) = sp + 48 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (24 : BitVec 12) : Word) = sp + 56 by bv_addr]
  xperm

theorem saveRaDivCallCallablePostNoX9_resultSignFixPreOwnScratch_quotient
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       resultSignFixPreOwnScratch (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
       saveRaDivCallResultSignFixFrameNoX9 vRa sp base dividendAbsWord) := by
  rw [saveRaDivCallCallablePostNoX9_unfold,
    EvmAsm.Evm64.divStackDispatchPostCallable_unfold]
  dsimp only
  rw [resultSignFixPreOwnScratch_unfold,
    saveRaDivCallResultSignFixFrameNoX9_unfold, evmWordIs_sp32_unfold]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (0 : BitVec 12) : Word) = sp + 32 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (8 : BitVec 12) : Word) = sp + 40 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (16 : BitVec 12) : Word) = sp + 48 by bv_addr]
  rw [show (sp + 32 + EvmAsm.Rv64.signExtend12 (24 : BitVec 12) : Word) = sp + 56 by bv_addr]
  xperm

end EvmAsm.Evm64.SDiv.Compose
