/-
  EvmAsm.Evm64.SMod.Compose.Bridges

  SMOD-offset-shaped expansions for generic DivMod dispatch assertions.
-/

import EvmAsm.Evm64.SMod.Compose.QuadMemBridges
import EvmAsm.Evm64.DivMod.Spec.Dispatcher

namespace EvmAsm.Evm64.SMod.Compose

/-- SMOD-offset-shaped expansion for `divModStackDispatchPreNoX1`.
    This keeps the stack memory slots in the form produced by the SMOD wrapper
    postcondition, avoiding an address-normalization step before `xperm_hyp`. -/
theorem divModStackDispatchPreNoX1_unfold_explicit_smod
    {sp : Word} {a b : EvmWord}
    {x9Val v1 v2 v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
     retMem dMem dloMem scratch_un0 : Word} :
    EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b x9Val v1 v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
      retMem dMem dloMem scratch_un0 =
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
     (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ a.getLimbN 0) **
      ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ a.getLimbN 1) **
      ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ a.getLimbN 2) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        a.getLimbN 3)) **
     (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ b.getLimbN 0) **
      ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ b.getLimbN 1) **
      ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ b.getLimbN 2) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
        b.getLimbN 3)) **
    EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  rw [EvmAsm.Evm64.divModStackDispatchPreNoX1_unfold,
    evmWordIs_sp_unfold, evmWordIs_sp32_unfold]
  rw [EvmAsm.Evm64.SMod.AddrNorm.stackSlot0 sp,
    EvmAsm.Evm64.SMod.AddrNorm.stackSlot8 sp,
    EvmAsm.Evm64.SMod.AddrNorm.stackSlot16 sp,
    EvmAsm.Evm64.SMod.AddrNorm.dividendTopSlot sp,
    EvmAsm.Evm64.SMod.AddrNorm.stackSlot32 sp,
    EvmAsm.Evm64.SMod.AddrNorm.stackSlot40 sp,
    EvmAsm.Evm64.SMod.AddrNorm.stackSlot48 sp,
    EvmAsm.Evm64.SMod.AddrNorm.divisorTopSlot sp]

end EvmAsm.Evm64.SMod.Compose
