/-
  EvmAsm.Evm64.SMod.Compose.ModCallPost

  Named postconditions for the unsigned MOD callable when reached through the
  SMOD wrapper.
-/

import EvmAsm.Evm64.SMod.Compose.DispatchReadyView

namespace EvmAsm.Evm64.SMod.Compose

/-- SMOD-private frame carried across the unsigned MOD callable. The callable
    owns the normalized stack/scratch state, while SMOD keeps the divisor sign
    in `x9`, the dividend/result sign in `x8` and `x13`, and the original
    return address in `x18`. -/
@[irreducible]
def smodModCallPrivateFrame
    (vRa dividendTop divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendSign := smodAbsSign dividendTop
  let divisorSign := smodAbsSign divisorTop
  (.x9 ↦ᵣ divisorSign) **
    ((.x8 ↦ᵣ dividendSign) ** (.x13 ↦ᵣ dividendSign) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))

theorem smodModCallPrivateFrame_unfold
    {vRa dividendTop divisorTop : Word} :
    smodModCallPrivateFrame vRa dividendTop divisorTop =
      (let dividendSign := smodAbsSign dividendTop
       let divisorSign := smodAbsSign divisorTop
       (.x9 ↦ᵣ divisorSign) **
         ((.x8 ↦ᵣ dividendSign) ** (.x13 ↦ᵣ dividendSign) **
           (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))) := by
  delta smodModCallPrivateFrame
  rfl

theorem smodModCallPrivateFrame_pcFree
    {vRa dividendTop divisorTop : Word} :
    (smodModCallPrivateFrame vRa dividendTop divisorTop).pcFree := by
  rw [smodModCallPrivateFrame_unfold]
  dsimp
  pcFree

instance pcFreeInst_smodModCallPrivateFrame
    (vRa dividendTop divisorTop : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (smodModCallPrivateFrame vRa dividendTop divisorTop) :=
  ⟨smodModCallPrivateFrame_pcFree⟩

/-- Postcondition after the unsigned MOD callable returns to the SMOD wrapper:
    the normalized MOD callable post plus the private SMOD sign/return frame. -/
@[irreducible]
def saveRaAbsThenModCallCallablePost
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    EvmAsm.Rv64.Assertion :=
  let dividendAbsWord : EvmWord :=
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
    (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
    smodModCallPrivateFrame vRa dividendTop divisorTop

theorem saveRaAbsThenModCallCallablePost_unfold
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
       EvmAsm.Evm64.modStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
         (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
         smodModCallPrivateFrame vRa dividendTop divisorTop) := by
  delta saveRaAbsThenModCallCallablePost
  rfl

theorem saveRaAbsThenModCallCallablePost_pcFree
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    (saveRaAbsThenModCallCallablePost vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).pcFree := by
  rw [saveRaAbsThenModCallCallablePost_unfold]
  dsimp
  rw [EvmAsm.Evm64.modStackDispatchPostCallable_unfold]
  rw [EvmAsm.Evm64.divScratchOwnCallNoX1_unfold, EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_saveRaAbsThenModCallCallablePost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop divisorLimb0
      divisorLimb1 divisorLimb2 divisorTop : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (saveRaAbsThenModCallCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) :=
  ⟨saveRaAbsThenModCallCallablePost_pcFree⟩

end EvmAsm.Evm64.SMod.Compose
