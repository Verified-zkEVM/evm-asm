/-
  Ambient TIS Top dualization (multi-tx Option A).

  bodyFrame pins loadPtr; bodyPayloadAmbient owns regionBase/bs.
  Extract/type framed under ambient Assumed. Ets/success compose residual.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasTop
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasExtractAmbient
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasTypeAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbientTop
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.DualReadByteScan
  (validByteRange validByteRange_head isValidByteAccess_of_validByteRange)
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch teer_success_implies_nonempty txSlice txSlice_length
    TypeDispatchAssumedAmbientFull)
open EvmAsm.Codegen.TxExtractToAddressModel (extractSuccess)
open EvmAsm.Codegen.TxExtractToAddressSpec
  (ExtractAssumedAmbient TisCalleeAssumptionsAmbient)

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_extractToBufOwn _
      | exact pcFree_teaScratchOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_stackFree _ _)

/-- Ambient payload: full blob region (not loadPtr slice). -/
def bodyPayloadAmbient (regionBase : Word) (bs : List (BitVec 8))
    (outPtr oldOut : Word) : Assertion :=
  bytesRegion regionBase bs **
  extractToBufOwn ToBufAddr ** memOwn IsCreationAddr **
  memOwn TypeAddr ** memOwn InnerOffAddr ** teaScratchOwn **
  (outPtr ↦ₘ oldOut)

def bodyPayloadOkAmbient (regionBase : Word) (bs : List (BitVec 8))
    (outPtr : Word) : Assertion :=
  bytesRegion regionBase bs **
  extractToBufOwn ToBufAddr ** memOwn IsCreationAddr **
  memOwn TypeAddr ** memOwn InnerOffAddr ** teaScratchOwn **
  (outPtr ↦ₘ (0 : Word))

private theorem prologue_to_extractPreAmbient
    (spC : Word) (s : TisSaved)
    (regionBase loadPtr lenW outPtr oldOut s7 : Word) (bs : List (BitVec 8))
    (old5 old6 old7 old13 old14 old15 old16 : Word) :
    ∀ h,
      (prologuePost spC s loadPtr lenW outPtr
          old5 old6 old7 old13 old14 old15 old16 **
        stackFree spC nExtractStackDwords **
        bodyPayloadAmbient regionBase bs outPtr oldOut **
        (Reg.x23 ↦ᵣ s7)) h →
      (((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ spC) ** stackFree spC nExtractStackDwords **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
          (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (Reg.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13) **
          bytesRegion regionBase bs **
          extractToBufOwn ToBufAddr ** memOwn IsCreationAddr ** teaScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word))) **
        (bodyFrameAmbient spC s **
          memOwn TypeAddr ** memOwn InnerOffAddr **
          (outPtr ↦ₘ oldOut))) h := by
  intro h hp
  unfold prologuePost prologueAbiRest bodyPayloadAmbient at hp
  have hp1 :
      (((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
          (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) ** (.x16 ↦ᵣ old16)) **
        ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ spC) ** stackFree spC nExtractStackDwords **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
          (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (Reg.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13) **
          bytesRegion regionBase bs **
          extractToBufOwn ToBufAddr ** memOwn IsCreationAddr ** teaScratchOwn **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsSaved tisFrame spC (tisSavedVals s) **
          memOwn TypeAddr ** memOwn InnerOffAddr **
          (outPtr ↦ₘ oldOut))) h := by
    xperm_hyp hp
  have hp2 :=
    sepConj_mono (pack6 old5 old6 old7 old14 old15 old16)
      (fun _ hh => hh) h hp1
  unfold bodyFrameAmbient
  xperm_hyp hp2

private theorem extractPost_to_bodyAmbient
    (spC : Word) (s : TisSaved)
    (regionBase loadPtr lenW outPtr oldOut s7 : Word) (bs : List (BitVec 8)) :
    ∀ h,
      ((((.x1 ↦ᵣ LinkExtract) ** (.x2 ↦ᵣ spC) ** stackFree spC nExtractStackDwords **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
          (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (Reg.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs **
          extractToBufOwn ToBufAddr ** memOwn IsCreationAddr ** teaScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
        (bodyFrameAmbient spC s **
          memOwn TypeAddr ** memOwn InnerOffAddr **
          (outPtr ↦ₘ oldOut))) h) →
      ((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s loadPtr lenW outPtr **
        bodyPayloadAmbient regionBase bs outPtr oldOut **
        bodyScratch ** (Reg.x23 ↦ᵣ s7)) h := by
  intro h hp
  unfold bodyFrameAmbient at hp
  unfold bodyFrame bodyPayloadAmbient bodyScratch
  xperm_hyp hp

set_option maxRecDepth 8000 in
theorem tisExtractFramedAmbient
    (asm : ExtractAssumedAmbient fullCode)
    (hentry : asm.entry = ExtractEntry)
    (spC : Word) (s : TisSaved)
    (regionBase loadPtr lenW outPtr oldOut s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (old5 old6 old7 old13 old14 old15 old16 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : extractSuccess (txSlice bs off len))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htvalid : isValidMemAccess (ToBufAddr + (16 : Word)) = true) :
    cpsTripleWithin (4 + (1 + nExtractSteps) + 1) (T + 56) AfterExtractBne fullCode
      (prologuePost spC s loadPtr lenW outPtr
        old5 old6 old7 old13 old14 old15 old16 **
        stackFree spC nExtractStackDwords **
        bodyPayloadAmbient regionBase bs outPtr oldOut **
        (Reg.x23 ↦ᵣ s7))
      ((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s loadPtr lenW outPtr **
        bodyPayloadAmbient regionBase bs outPtr oldOut **
        bodyScratch ** (Reg.x23 ↦ᵣ s7)) := by
  have hex0 := tisExtractSuccessAmbient asm hentry spC regionBase loadPtr lenW outPtr
    s.s3 s.s4 s.s5 s.s6 s7 bs off len s.ra outPtr old13
    hptr hlen hsuccess halign hbound hover hvalidBuf htvalid
  have hexF := cpsTripleWithin_frameR
    (bodyFrameAmbient spC s **
      memOwn TypeAddr ** memOwn InnerOffAddr **
      (outPtr ↦ₘ oldOut))
    (by unfold bodyFrameAmbient; pcf) hex0
  exact cpsTripleWithin_weaken
    (prologue_to_extractPreAmbient spC s regionBase loadPtr lenW outPtr oldOut s7 bs
      old5 old6 old7 old13 old14 old15 old16)
    (extractPost_to_bodyAmbient spC s regionBase loadPtr lenW outPtr oldOut s7 bs) hexF

private def typePreConcreteAmbient (spC : Word) (s : TisSaved)
    (regionBase loadPtr lenW outPtr oldOut s7 : Word) (bs : List (BitVec 8))
    (v11 v12 v13 : Word) : Assertion :=
  (.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
  bodyFrame spC s loadPtr lenW outPtr **
  bodyPayloadAmbient regionBase bs outPtr oldOut **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (Reg.x23 ↦ᵣ s7)

private theorem typeCoreAmbient
    (asm : TypeDispatchAssumedAmbientFull fullCode)
    (hentry : asm.entry = TypeEntry)
    (spC : Word) (s : TisSaved)
    (regionBase loadPtr lenW outPtr oldOut s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (v11 v12 v13 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
      (typePreConcreteAmbient spC s regionBase loadPtr lenW outPtr oldOut s7 bs
        v11 v12 v13)
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s loadPtr lenW outPtr **
        bodyPayloadAmbient regionBase bs outPtr oldOut **
        bodyScratch ** (Reg.x23 ↦ᵣ s7)) := by
  have hty0 := tisTypeSuccessAmbient asm hentry regionBase loadPtr lenW outPtr
    bs off len LinkExtract 0 v11 v12 v13
    hptr hlen hsuccess halign hbound hover hvalid0
  have htyF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** stackFree spC nExtractStackDwords **
      (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
      (Reg.x23 ↦ᵣ s7) **
      frameSlotsSaved tisFrame spC (tisSavedVals s) **
      extractToBufOwn ToBufAddr ** memOwn IsCreationAddr ** teaScratchOwn **
      (outPtr ↦ₘ oldOut))
    (by pcf) hty0
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      unfold typePreConcreteAmbient bodyFrame bodyPayloadAmbient at *
      xperm_hyp hp)
    (fun _ hq => by
      unfold bodyFrame bodyPayloadAmbient bodyScratch at *
      xperm_hyp hq) htyF

set_option maxRecDepth 8000 in
theorem tisTypeFramedAmbient
    (asm : TypeDispatchAssumedAmbientFull fullCode)
    (hentry : asm.entry = TypeEntry)
    (spC : Word) (s : TisSaved)
    (regionBase loadPtr lenW outPtr oldOut s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
      ((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s loadPtr lenW outPtr **
        bodyPayloadAmbient regionBase bs outPtr oldOut **
        bodyScratch ** (Reg.x23 ↦ᵣ s7))
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s loadPtr lenW outPtr **
        bodyPayloadAmbient regionBase bs outPtr oldOut **
        bodyScratch ** (Reg.x23 ↦ᵣ s7)) := by
  have hcore (v11 v12 v13 : Word) :=
    typeCoreAmbient asm hentry spC s regionBase loadPtr lenW outPtr oldOut s7
      bs off len v11 v12 v13 hptr hlen hsuccess halign hbound hover hvalid0
  have h13 : cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
      (((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bodyFrame spC s loadPtr lenW outPtr **
          bodyPayloadAmbient regionBase bs outPtr oldOut **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (Reg.x23 ↦ᵣ s7)) **
        regOwn .x13)
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s loadPtr lenW outPtr **
        bodyPayloadAmbient regionBase bs outPtr oldOut **
        bodyScratch ** (Reg.x23 ↦ᵣ s7)) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x13) (fun v13 => ?_)
    have h12 : cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
        (((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            bodyFrame spC s loadPtr lenW outPtr **
            bodyPayloadAmbient regionBase bs outPtr oldOut **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 **
            regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (Reg.x23 ↦ᵣ s7) **
            (.x13 ↦ᵣ v13)) **
          regOwn .x12)
        ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bodyFrame spC s loadPtr lenW outPtr **
          bodyPayloadAmbient regionBase bs outPtr oldOut **
          bodyScratch ** (Reg.x23 ↦ᵣ s7)) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12) (fun v12 => ?_)
      have h11 : cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
          (((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              bodyFrame spC s loadPtr lenW outPtr **
              bodyPayloadAmbient regionBase bs outPtr oldOut **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (Reg.x23 ↦ᵣ s7) **
              (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13)) **
            regOwn .x11)
          ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            bodyFrame spC s loadPtr lenW outPtr **
            bodyPayloadAmbient regionBase bs outPtr oldOut **
            bodyScratch ** (Reg.x23 ↦ᵣ s7)) := by
        refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11) (fun v11 => ?_)
        exact cpsTripleWithin_weaken
          (fun _ hp => by
            unfold typePreConcreteAmbient bodyFrame bodyPayloadAmbient at *
            xperm_hyp hp)
          (fun _ hq => hq)
          (hcore v11 v12 v13)
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) h11
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h12
  exact cpsTripleWithin_weaken
    (fun _ hp => by unfold bodyScratch at hp; xperm_hyp hp)
    (fun _ hq => hq) h13

#print axioms tisExtractFramedAmbient
#print axioms tisTypeFramedAmbient

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
