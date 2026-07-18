/-
  Extract mid: type_dispatch success + load type/inner
  AfterPreZero (E+72) → WalkInitJalPc (E+144) under extractLinkedCode.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTypeCall
import EvmAsm.Codegen.Programs.TxExtractToAddressLoadType
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (nTypeSteps teaScratchOwn)

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact bytesRegion_pcFree _ _)

set_option maxRecDepth 8000 in
/-- Load under teer; peels regOwn x5/x11/x30 (type post has regOwn). -/
theorem extractLoadTypeInner_teer_own
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (v10 v20 : Word)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word)) :
    cpsTripleWithin 8 AfterTypeBeqz WalkInitJalPc extractLinkedCode
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x20 ↦ᵣ v20) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        regOwn .x5 ** regOwn .x11 ** regOwn .x30)
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + (teerTxTypeDispatch txBytes).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch txBytes).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch txBytes).2.2) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2)) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x30)
      (P := (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x20 ↦ᵣ v20) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        regOwn .x5 ** regOwn .x11)
      (fun v30 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11)
      (P := (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x20 ↦ᵣ v20) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        regOwn .x5 ** (.x30 ↦ᵣ v30))
      (fun v11 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x20 ↦ᵣ v20) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        (.x30 ↦ᵣ v30) ** (.x11 ↦ᵣ v11))
      (fun v5 => ?_))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (extractLoadTypeInner_teer txBase lenW txBytes v5 v10 v11 v20 v30 hsuccess)

set_option maxRecDepth 8000 in
/-- Type success + load: AfterPreZero → WalkInitJalPc. -/
theorem extractTypeThenLoad
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (old1 v10 v11 v12 v13 v20 : Word)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin ((6 + (1 + nTypeSteps) + 1) + 8)
      AfterPreZero WalkInitJalPc extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x20 ↦ᵣ v20) **
        bytesRegion txBase txBytes **
        teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + (teerTxTypeDispatch txBytes).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch txBytes).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch txBytes).2.2) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        regOwn .x6 ** regOwn .x7 **
        regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x31) := by
  have ht := extractTypeSuccess txBase lenW txBytes old1 v10 v11 v12 v13
    hlen hsuccess halign hover hvalid0
  -- frame s4 (x20); type does not mention it
  have htF := cpsTripleWithin_frameR ((.x20 ↦ᵣ v20)) (by pcf) ht
  have htW : cpsTripleWithin (6 + (1 + nTypeSteps) + 1)
      AfterPreZero AfterTypeBeqz extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x20 ↦ᵣ v20) **
        bytesRegion txBase txBytes ** teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) ** (.x20 ↦ᵣ v20) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) htF
  have hl := extractLoadTypeInner_teer_own txBase lenW txBytes (0 : Word) v20 hsuccess
  have hlF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion txBase txBytes **
      regOwn .x6 ** regOwn .x7 **
      regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x31) (by pcf) hl
  have hlW : cpsTripleWithin 8 AfterTypeBeqz WalkInitJalPc extractLinkedCode
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) ** (.x20 ↦ᵣ v20) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + (teerTxTypeDispatch txBytes).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch txBytes).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch txBytes).2.2) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        regOwn .x6 ** regOwn .x7 **
        regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x31) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hlF
  exact cpsTripleWithin_seq_same_cr htW hlW

#print axioms extractLoadTypeInner_teer_own
#print axioms extractTypeThenLoad

end EvmAsm.Codegen.TxExtractToAddressSpec
