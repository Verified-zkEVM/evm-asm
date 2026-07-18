/-
  Ambient dual of extract load type/inner (E+112 → E+144).

  Register-only + tea memIs — already ambient-shaped. Pass loadPtr as s0 and
  teer of `txSlice` for type/inner values.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressLoadType
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec

/-- Ambient load type/inner: s0=loadPtr, tea cells hold teer of txSlice. -/
theorem extractLoadTypeInnerAmbient
    (loadPtr lenW : Word) (bs : List (BitVec 8)) (off len : Nat)
    (v5 v10 v11 v20 v30 : Word)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word)) :
    cpsTripleWithin 8 AfterTypeBeqz WalkInitJalPc extractLinkedCode
      ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x20 ↦ᵣ v20) ** (.x30 ↦ᵣ v30) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2))
      ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2)) :=
  extractLoadTypeInner_teer loadPtr lenW (txSlice bs off len)
    v5 v10 v11 v20 v30 hsuccess

#print axioms extractLoadTypeInnerAmbient

end EvmAsm.Codegen.TxExtractToAddressSpec
