/-
  Ambient dual: type_dispatch success + load type/inner
  AfterPreZero (E+72) → WalkInitJalPc (E+144) under extractLinkedCode.

  Post a0 = loadPtr + inner (slice-relative); ambient walk_init uses
  regionBase + absOff with absOff = off + inner.toNat via loadPtr_add_rel_eq.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressTypeCallAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressLoadType
import EvmAsm.Codegen.Programs.TxExtractToAddressLoadTypeAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec
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
/-- Load under teer(txSlice); peels regOwn x5/x11/x30. -/
theorem extractLoadTypeInnerAmbient_own
    (loadPtr lenW : Word) (bs : List (BitVec 8)) (off len : Nat)
    (v10 v20 : Word)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word)) :
    cpsTripleWithin 8 AfterTypeBeqz WalkInitJalPc extractLinkedCode
      ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x20 ↦ᵣ v20) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x5 ** regOwn .x11 ** regOwn .x30)
      ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2)) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x30)
      (P := (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x20 ↦ᵣ v20) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x5 ** regOwn .x11)
      (fun v30 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11)
      (P := (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x20 ↦ᵣ v20) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x5 ** (.x30 ↦ᵣ v30))
      (fun v11 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x20 ↦ᵣ v20) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        (.x30 ↦ᵣ v30) ** (.x11 ↦ᵣ v11))
      (fun v5 => ?_))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (extractLoadTypeInnerAmbient loadPtr lenW bs off len v5 v10 v11 v20 v30 hsuccess)

set_option maxRecDepth 8000 in
/-- Ambient type success + load: AfterPreZero → WalkInitJalPc. -/
theorem extractTypeThenLoadAmbient
    (regionBase loadPtr lenW : Word) (bs : List (BitVec 8)) (off len : Nat)
    (old1 v10 v11 v12 v13 v20 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hbound : off + len ≤ bs.length)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin ((6 + (1 + nTypeSteps) + 1) + 8)
      AfterPreZero WalkInitJalPc extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x20 ↦ᵣ v20) **
        bytesRegion regionBase bs **
        teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x6 ** regOwn .x7 **
        regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x31) := by
  have ht := extractTypeSuccessAmbient regionBase loadPtr lenW bs off len
    old1 v10 v11 v12 v13 hptr hlen hsuccess halign hbound hover hvalid0
  have htF := cpsTripleWithin_frameR ((.x20 ↦ᵣ v20)) (by pcf) ht
  have htW : cpsTripleWithin (6 + (1 + nTypeSteps) + 1)
      AfterPreZero AfterTypeBeqz extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x20 ↦ᵣ v20) **
        bytesRegion regionBase bs **
        teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x20 ↦ᵣ v20) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) htF
  have hl := extractLoadTypeInnerAmbient_own loadPtr lenW bs off len (0 : Word) v20
    hsuccess
  have hlF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion regionBase bs **
      regOwn .x6 ** regOwn .x7 **
      regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x31) (by pcf) hl
  have hlW : cpsTripleWithin 8 AfterTypeBeqz WalkInitJalPc extractLinkedCode
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x20 ↦ᵣ v20) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x6 ** regOwn .x7 **
        regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x31) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hlF
  exact cpsTripleWithin_seq_same_cr htW hlW

#print axioms extractLoadTypeInnerAmbient_own
#print axioms extractTypeThenLoadAmbient

end EvmAsm.Codegen.TxExtractToAddressSpec
