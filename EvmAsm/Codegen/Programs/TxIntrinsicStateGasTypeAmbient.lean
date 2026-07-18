/-
  Ambient type-dispatch setup+call+BNE under TypeDispatchAssumedAmbientFull
  (multi-tx Option A).
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasType
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasExtractAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbientTop
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch txSlice TypeDispatchAssumedAmbientFull)

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsSaved _ _ _)

/-- Ambient type callee: loadPtr in a0; owns full regionBase/bs. -/
def typeCalleePAmbient (regionBase loadPtr lenW : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
  (.x12 ↦ᵣ TypeAddr) ** (.x13 ↦ᵣ InnerOffAddr) **
  bytesRegion regionBase bs **
  memOwn TypeAddr ** memOwn InnerOffAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

def typeCalleeQAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) **
  bytesRegion regionBase bs **
  memOwn TypeAddr ** memOwn InnerOffAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem typeCalleePAmbient_pcFree (regionBase loadPtr lenW : Word)
    (bs : List (BitVec 8)) :
    (typeCalleePAmbient regionBase loadPtr lenW bs).pcFree := by
  unfold typeCalleePAmbient; pcf

set_option maxRecDepth 8000 in
theorem tisTypeCallAmbient
    (asm : TypeDispatchAssumedAmbientFull fullCode)
    (hentry : asm.entry = TypeEntry)
    (regionBase loadPtr lenW : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (old1 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin (1 + nTypeSteps) (T + 104) LinkType fullCode
      ((.x1 ↦ᵣ old1) ** typeCalleePAmbient regionBase loadPtr lenW bs)
      ((.x1 ↦ᵣ LinkType) ** typeCalleeQAmbient regionBase bs) := by
  have hret : (LinkType &&& ~~~(1 : Word)) = LinkType := by
    simp only [LinkType, T]; decide
  have hcallee0 := asm.success_flat LinkType regionBase loadPtr lenW
    TypeAddr InnerOffAddr bs off len
    hret hptr hlen hsuccess halign hbound hover hvalid0
  have hcallee0' : cpsTripleWithin nTypeSteps asm.entry LinkType fullCode
      ((.x1 ↦ᵣ LinkType) ** typeCalleePAmbient regionBase loadPtr lenW bs)
      ((.x1 ↦ᵣ LinkType) ** typeCalleeQAmbient regionBase bs) := by
    unfold typeCalleePAmbient typeCalleeQAmbient
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcallee : cpsTripleWithin nTypeSteps TypeEntry LinkType fullCode
      ((.x1 ↦ᵣ LinkType) ** typeCalleePAmbient regionBase loadPtr lenW bs)
      ((.x1 ↦ᵣ LinkType) ** typeCalleeQAmbient regionBase bs) := by
    rw [← hentry]; exact hcallee0'
  have hcall := callWithin_spec (T + 104) TypeEntry old1 typeJalOff nTypeSteps
    (by show (T + 104) + signExtend21 typeJalOff = TypeEntry; decide)
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 104) tisProg 26
        (.JAL .x1 typeJalOff) (by bv_omega) (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi))
    (typeCalleePAmbient_pcFree regionBase loadPtr lenW bs)
    hcallee
  rw [show (T + 104 + 4 : Word) = LinkType from by
    simp only [LinkType]; bv_omega] at hcall
  exact hcall

set_option maxRecDepth 8000 in
/-- Type path AfterExtractBne → AfterTypeBne under ambient TypeDispatchAssumed. -/
theorem tisTypeSuccessAmbient
    (asm : TypeDispatchAssumedAmbientFull fullCode)
    (hentry : asm.entry = TypeEntry)
    (regionBase loadPtr lenW outPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (old1 v10 v11 v12 v13 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x18 ↦ᵣ outPtr) **
        bytesRegion regionBase bs **
        memOwn TypeAddr ** memOwn InnerOffAddr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr) **
        bytesRegion regionBase bs **
        memOwn TypeAddr ** memOwn InnerOffAddr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  have hsetup := tisTypeSetup loadPtr lenW v10 v11 v12 v13
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** (.x18 ↦ᵣ outPtr) **
      bytesRegion regionBase bs **
      memOwn TypeAddr ** memOwn InnerOffAddr **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hsetup
  have hcall := tisTypeCallAmbient asm hentry regionBase loadPtr lenW
    bs off len old1 hptr hlen hsuccess halign hbound hover hvalid0
  have hcallF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr)) (by pcf) hcall
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold typeCalleePAmbient at *
    xperm_hyp hp) hsetupF hcallF
  have hbne := tisTypeBneOk
  have hbneF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkType) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ outPtr) **
      bytesRegion regionBase bs **
      memOwn TypeAddr ** memOwn InnerOffAddr **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by pcf) hbne
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold typeCalleeQAmbient at *
    xperm_hyp hp) h01 hbneF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h12

#print axioms tisTypeCallAmbient
#print axioms tisTypeSuccessAmbient

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
