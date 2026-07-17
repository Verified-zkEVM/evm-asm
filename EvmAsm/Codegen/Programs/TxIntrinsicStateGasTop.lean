/-
  Top success theorem for `tx_intrinsic_state_gas` under TisCalleeAssumptions.

  Composition:
    prologue (14) ;; extract ;; type ;; ets (proven *out=0) ;; epilogue (10)
  → a0 = 0 ∧ *out = pureIntrinsicStateGasSuccess (= 0), frame restored.

  Extract/type are named hypotheses; ets is fully proven.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasEts
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasEpilogue
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)
open EvmAsm.Codegen.TxExtractToAddressModel (extractSuccess teerExtractToAddress)

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
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_frameSlotsOwn _ _)

def nTisTopSteps : Nat := 14 + (4 + (1 + nExtractSteps) + 1) +
  (6 + (1 + nTypeSteps) + 1) + (5 + 2 + 1 + 1 + (1 + 4) + 1) + 10

private theorem prologue_full
    (sp0 spC : Word) (s : TisSaved)
    (txBase txLenW outPtr : Word)
    (old5 old6 old7 old13 old14 old15 old16 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 14 T (T + 56) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt tisFrame (tisSavedVals s) **
        frameSlotsOwn tisFrame spC **
        prologueAbiRest txBase txLenW outPtr old5 old6 old7 old13 old14 old15 old16)
      (prologuePost spC s txBase txLenW outPtr
        old5 old6 old7 old13 old14 old15 old16) :=
  cpsTripleWithin_extend_code tis_mono
    (tisPrologue sp0 spC s txBase txLenW outPtr
      old5 old6 old7 old13 old14 old15 old16 hspC)

private theorem epi_full
    (sp0 spC : Word) (s cur : TisSaved) (a0v : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 10 EpiRestore s.ra fullCode
      ((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ spC) **
        regsAt tisFrame (tisSavedVals cur) **
        frameSlotsSaved tisFrame spC (tisSavedVals s))
      ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        frameSlotsSaved tisFrame spC (tisSavedVals s)) :=
  cpsTripleWithin_extend_code tis_mono
    (tisEpilogueSuccess sp0 spC s cur a0v hspC hret)

/-- Saved body frame including x18 (s2/out). -/
def bodyFrame (spC : Word) (s : TisSaved) (txBase lenW outPtr : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr) **
  (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
  frameSlotsSaved tisFrame spC (tisSavedVals s)

/-- Extract owns x18; frame across extract excludes it. -/
def bodyFrameNoX18 (spC : Word) (s : TisSaved) (txBase lenW : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
  (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
  frameSlotsSaved tisFrame spC (tisSavedVals s)

def bodyFrameAfterEts (spC : Word) (s : TisSaved)
    (txBase lenW outPtr : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr) **
  (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
  frameSlotsSaved tisFrame spC (tisSavedVals s)

def bodyScratch : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

def bodyPayload (txBase : Word) (txBytes : List (BitVec 8))
    (outPtr oldOut : Word) : Assertion :=
  bytesRegion txBase txBytes **
  memOwn ToBufAddr ** memOwn IsCreationAddr **
  memOwn TypeAddr ** memOwn InnerOffAddr **
  (outPtr ↦ₘ oldOut)

def bodyPayloadOk (txBase : Word) (txBytes : List (BitVec 8))
    (outPtr : Word) : Assertion :=
  bytesRegion txBase txBytes **
  memOwn ToBufAddr ** memOwn IsCreationAddr **
  memOwn TypeAddr ** memOwn InnerOffAddr **
  (outPtr ↦ₘ (0 : Word))

private theorem pack6
    (v5 v6 v7 v14 v15 v16 : Word) :
    ∀ h, ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16)) h →
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16) h := by
  intro h hp
  exact sepConj_mono (regIs_to_regOwn .x5 v5)
    (sepConj_mono (regIs_to_regOwn .x6 v6)
      (sepConj_mono (regIs_to_regOwn .x7 v7)
        (sepConj_mono (regIs_to_regOwn .x14 v14)
          (sepConj_mono (regIs_to_regOwn .x15 v15)
            (regIs_to_regOwn .x16 v16))))) h hp

private theorem pack_ets_temps (isC outPtr : Word) :
    ∀ h, ((.x5 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
      (.x14 ↦ᵣ isC) ** (.x15 ↦ᵣ outPtr) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) h →
    bodyScratch h := by
  intro h hp
  unfold bodyScratch
  have hp' :=
    sepConj_mono (regIs_to_regOwn .x5 (0 : Word))
      (sepConj_mono (regIs_to_regOwn .x11 (0 : Word))
        (sepConj_mono (regIs_to_regOwn .x12 (0 : Word))
          (sepConj_mono (regIs_to_regOwn .x13 (0 : Word))
            (sepConj_mono (regIs_to_regOwn .x14 isC)
              (sepConj_mono (regIs_to_regOwn .x15 outPtr)
                (fun _ hh => hh)))))) h hp
  xperm_hyp hp'

private theorem prologue_to_extractPre
    (spC : Word) (s : TisSaved)
    (txBase lenW outPtr oldOut : Word) (txBytes : List (BitVec 8))
    (old5 old6 old7 old13 old14 old15 old16 : Word) :
    ∀ h,
      (prologuePost spC s txBase lenW outPtr
          old5 old6 old7 old13 old14 old15 old16 **
        bodyPayload txBase txBytes outPtr oldOut) h →
      (((.x1 ↦ᵣ s.ra) ** (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13) ** (.x18 ↦ᵣ outPtr) **
          bytesRegion txBase txBytes **
          memOwn ToBufAddr ** memOwn IsCreationAddr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word))) **
        (bodyFrameNoX18 spC s txBase lenW **
          memOwn TypeAddr ** memOwn InnerOffAddr **
          (outPtr ↦ₘ oldOut))) h := by
  intro h hp
  unfold prologuePost prologueAbiRest bodyPayload at hp
  have hp1 :
      (((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
          (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) ** (.x16 ↦ᵣ old16)) **
        ((.x1 ↦ᵣ s.ra) ** (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ old13) ** (.x18 ↦ᵣ outPtr) **
          bytesRegion txBase txBytes **
          memOwn ToBufAddr ** memOwn IsCreationAddr **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
          (.x22 ↦ᵣ s.s6) **
          frameSlotsSaved tisFrame spC (tisSavedVals s) **
          memOwn TypeAddr ** memOwn InnerOffAddr **
          (outPtr ↦ₘ oldOut))) h := by
    xperm_hyp hp
  have hp2 :=
    sepConj_mono (pack6 old5 old6 old7 old14 old15 old16)
      (fun _ hh => hh) h hp1
  unfold bodyFrameNoX18
  xperm_hyp hp2

private theorem extractPost_to_body
    (spC : Word) (s : TisSaved)
    (txBase lenW outPtr oldOut : Word) (txBytes : List (BitVec 8)) :
    ∀ h,
      ((((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x18 ↦ᵣ outPtr) **
          bytesRegion txBase txBytes **
          memOwn ToBufAddr ** memOwn IsCreationAddr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
        (bodyFrameNoX18 spC s txBase lenW **
          memOwn TypeAddr ** memOwn InnerOffAddr **
          (outPtr ↦ₘ oldOut))) h) →
      ((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s txBase lenW outPtr **
        bodyPayload txBase txBytes outPtr oldOut **
        bodyScratch) h := by
  intro h hp
  unfold bodyFrameNoX18 at hp
  unfold bodyFrame bodyPayload bodyScratch
  xperm_hyp hp

set_option maxRecDepth 8000 in
theorem tisExtractFramed
    (asm : ExtractAssumed fullCode)
    (hentry : asm.entry = ExtractEntry)
    (spC : Word) (s : TisSaved)
    (txBase lenW outPtr oldOut : Word) (txBytes : List (BitVec 8))
    (old5 old6 old7 old13 old14 old15 old16 : Word)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : TxExtractToAddressModel.extractSuccess txBytes) :
    cpsTripleWithin (4 + (1 + nExtractSteps) + 1) (T + 56) AfterExtractBne fullCode
      (prologuePost spC s txBase lenW outPtr
        old5 old6 old7 old13 old14 old15 old16 **
        bodyPayload txBase txBytes outPtr oldOut)
      ((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s txBase lenW outPtr **
        bodyPayload txBase txBytes outPtr oldOut **
        bodyScratch) := by
  have hex0 := tisExtractSuccess asm hentry txBase lenW outPtr txBytes
    s.ra outPtr old13 hlen hsuccess
  have hexF := cpsTripleWithin_frameR
    (bodyFrameNoX18 spC s txBase lenW **
      memOwn TypeAddr ** memOwn InnerOffAddr **
      (outPtr ↦ₘ oldOut))
    (by unfold bodyFrameNoX18; pcf) hex0
  exact cpsTripleWithin_weaken
    (prologue_to_extractPre spC s txBase lenW outPtr oldOut txBytes
      old5 old6 old7 old13 old14 old15 old16)
    (extractPost_to_body spC s txBase lenW outPtr oldOut txBytes) hexF

private def typePreConcrete (spC : Word) (s : TisSaved)
    (txBase lenW outPtr oldOut : Word) (txBytes : List (BitVec 8))
    (v11 v12 v13 : Word) : Assertion :=
  (.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
  bodyFrame spC s txBase lenW outPtr **
  bodyPayload txBase txBytes outPtr oldOut **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

private theorem typeCore
    (asm : TypeDispatchAssumed fullCode)
    (hentry : asm.entry = TypeEntry)
    (spC : Word) (s : TisSaved)
    (txBase lenW outPtr oldOut : Word) (txBytes : List (BitVec 8))
    (v11 v12 v13 : Word)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
      (typePreConcrete spC s txBase lenW outPtr oldOut txBytes v11 v12 v13)
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s txBase lenW outPtr **
        bodyPayload txBase txBytes outPtr oldOut **
        bodyScratch) := by
  have hty0 := tisTypeSuccess asm hentry txBase lenW outPtr txBytes
    LinkExtract 0 v11 v12 v13 hlen hsuccess halign hover hvalid0
  have htyF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
      frameSlotsSaved tisFrame spC (tisSavedVals s) **
      memOwn ToBufAddr ** memOwn IsCreationAddr **
      (outPtr ↦ₘ oldOut))
    (by pcf) hty0
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      unfold typePreConcrete bodyFrame bodyPayload at *
      xperm_hyp hp)
    (fun _ hq => by
      unfold bodyFrame bodyPayload bodyScratch at *
      xperm_hyp hq) htyF

set_option maxRecDepth 8000 in
theorem tisTypeFramed
    (asm : TypeDispatchAssumed fullCode)
    (hentry : asm.entry = TypeEntry)
    (spC : Word) (s : TisSaved)
    (txBase lenW outPtr oldOut : Word) (txBytes : List (BitVec 8))
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
      ((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s txBase lenW outPtr **
        bodyPayload txBase txBytes outPtr oldOut **
        bodyScratch)
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s txBase lenW outPtr **
        bodyPayload txBase txBytes outPtr oldOut **
        bodyScratch) := by
  have hcore (v11 v12 v13 : Word) :=
    typeCore asm hentry spC s txBase lenW outPtr oldOut txBytes v11 v12 v13 hlen hsuccess halign hover hvalid0
  -- rightmost peels: x13, then x12, then x11
  have h13 : cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
      (((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bodyFrame spC s txBase lenW outPtr **
          bodyPayload txBase txBytes outPtr oldOut **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
        regOwn .x13)
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s txBase lenW outPtr **
        bodyPayload txBase txBytes outPtr oldOut **
        bodyScratch) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x13) (fun v13 => ?_)
    have h12 : cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
        (((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            bodyFrame spC s txBase lenW outPtr **
            bodyPayload txBase txBytes outPtr oldOut **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 **
            regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x13 ↦ᵣ v13)) **
          regOwn .x12)
        ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bodyFrame spC s txBase lenW outPtr **
          bodyPayload txBase txBytes outPtr oldOut **
          bodyScratch) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12) (fun v12 => ?_)
      have h11 : cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
          (((.x1 ↦ᵣ LinkExtract) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              bodyFrame spC s txBase lenW outPtr **
              bodyPayload txBase txBytes outPtr oldOut **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13)) **
            regOwn .x11)
          ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            bodyFrame spC s txBase lenW outPtr **
            bodyPayload txBase txBytes outPtr oldOut **
            bodyScratch) := by
        refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11) (fun v11 => ?_)
        exact cpsTripleWithin_weaken
          (fun _ hp => by
            unfold typePreConcrete bodyFrame bodyPayload at *
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

/-- Ets core under concrete isC + temps. -/
private theorem etsCore
    (spC : Word) (s : TisSaved)
    (txBase lenW outPtr oldOut : Word) (txBytes : List (BitVec 8))
    (isC v5 v11 v12 v13 v14 v15 : Word)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts) :
    cpsTripleWithin (5 + 2 + 1 + 1 + (1 + 4) + 1) AfterTypeBne EpiRestore fullCode
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s txBase lenW outPtr **
        bytesRegion txBase txBytes **
        memOwn ToBufAddr ** (IsCreationAddr ↦ₘ isC) **
        memOwn TypeAddr ** memOwn InnerOffAddr **
        (outPtr ↦ₘ oldOut) **
        (.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrameAfterEts spC s txBase lenW outPtr **
        bodyPayloadOk txBase txBytes outPtr **
        bodyScratch) := by
  have hets0 := tisEtsSuccess outPtr oldOut isC v5 0 v11 v12 v13 v14 v15 s.s4
    LinkType hlink
  have hetsF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x19 ↦ᵣ s.s3) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
      frameSlotsSaved tisFrame spC (tisSavedVals s) **
      bytesRegion txBase txBytes **
      memOwn ToBufAddr ** memOwn TypeAddr ** memOwn InnerOffAddr **
      regOwn .x6 ** regOwn .x7 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by pcf) hets0
  exact cpsTripleWithin_weaken
    (fun _ hp => by unfold bodyFrame at *; xperm_hyp hp)
    (fun h hq => by
      have hq1 :
          (((.x5 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
              (.x14 ↦ᵣ isC) ** (.x15 ↦ᵣ outPtr) **
              regOwn .x6 ** regOwn .x7 ** regOwn .x16 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
            ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr) **
              (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ (0 : Word)) **
              (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
              frameSlotsSaved tisFrame spC (tisSavedVals s) **
              bytesRegion txBase txBytes **
              memOwn ToBufAddr ** (IsCreationAddr ↦ₘ isC) **
              memOwn TypeAddr ** memOwn InnerOffAddr **
              (outPtr ↦ₘ (0 : Word)))) h := by
        xperm_hyp hq
      have hq2 :=
        sepConj_mono (pack_ets_temps isC outPtr) (fun _ hh => hh) h hq1
      have hq3 :
          ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              bodyFrameAfterEts spC s txBase lenW outPtr **
              bytesRegion txBase txBytes **
              memOwn ToBufAddr ** (IsCreationAddr ↦ₘ isC) **
              memOwn TypeAddr ** memOwn InnerOffAddr **
              (outPtr ↦ₘ (0 : Word)) **
              bodyScratch) h := by
        unfold bodyFrameAfterEts bodyScratch at *
        xperm_hyp hq2
      -- pull IsCreation rightmost for mono, then memIs→memOwn
      have hq4 :
          (((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              bodyFrameAfterEts spC s txBase lenW outPtr **
              bytesRegion txBase txBytes **
              memOwn ToBufAddr **
              memOwn TypeAddr ** memOwn InnerOffAddr **
              (outPtr ↦ₘ (0 : Word)) **
              bodyScratch) **
            (IsCreationAddr ↦ₘ isC)) h := by
        xperm_hyp hq3
      have hq5 :=
        sepConj_mono (fun _ x => x)
          (memIs_implies_memOwn (a := IsCreationAddr) (v := isC)) h hq4
      unfold bodyPayloadOk bodyFrameAfterEts bodyScratch at *
      xperm_hyp hq5) hetsF

set_option maxRecDepth 8000 in
theorem tisEtsFramed
    (spC : Word) (s : TisSaved)
    (txBase lenW outPtr oldOut : Word) (txBytes : List (BitVec 8))
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts) :
    cpsTripleWithin (5 + 2 + 1 + 1 + (1 + 4) + 1) AfterTypeBne EpiRestore fullCode
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrame spC s txBase lenW outPtr **
        bodyPayload txBase txBytes outPtr oldOut **
        bodyScratch)
      ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrameAfterEts spC s txBase lenW outPtr **
        bodyPayloadOk txBase txBytes outPtr **
        bodyScratch) := by
  have hcore (isC v5 v11 v12 v13 v14 v15 : Word) :=
    etsCore spC s txBase lenW outPtr oldOut txBytes isC v5 v11 v12 v13 v14 v15 hlink
  -- peel rightmost: temps then IsCreation (rebuild with owns rightmost stepwise)
  have hpeel : cpsTripleWithin (5 + 2 + 1 + 1 + (1 + 4) + 1) AfterTypeBne EpiRestore fullCode
      (((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bodyFrame spC s txBase lenW outPtr **
          bytesRegion txBase txBytes **
          memOwn ToBufAddr **
          memOwn TypeAddr ** memOwn InnerOffAddr **
          (outPtr ↦ₘ oldOut) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
        memOwn IsCreationAddr)
      ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrameAfterEts spC s txBase lenW outPtr **
        bodyPayloadOk txBase txBytes outPtr **
        bodyScratch) := by
    refine cpsTripleWithin_of_forall_memIs_to_memOwn (a := IsCreationAddr) (fun isC => ?_)
    -- now peel x5 rightmost
    have hx5 : cpsTripleWithin (5 + 2 + 1 + 1 + (1 + 4) + 1) AfterTypeBne EpiRestore fullCode
        (((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            bodyFrame spC s txBase lenW outPtr **
            bytesRegion txBase txBytes **
            memOwn ToBufAddr ** (IsCreationAddr ↦ₘ isC) **
            memOwn TypeAddr ** memOwn InnerOffAddr **
            (outPtr ↦ₘ oldOut) **
            regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
          regOwn .x5)
        ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bodyFrameAfterEts spC s txBase lenW outPtr **
          bodyPayloadOk txBase txBytes outPtr **
          bodyScratch) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5) (fun v5 => ?_)
      have hx15 : cpsTripleWithin (5 + 2 + 1 + 1 + (1 + 4) + 1) AfterTypeBne EpiRestore fullCode
          (((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              bodyFrame spC s txBase lenW outPtr **
              bytesRegion txBase txBytes **
              memOwn ToBufAddr ** (IsCreationAddr ↦ₘ isC) **
              memOwn TypeAddr ** memOwn InnerOffAddr **
              (outPtr ↦ₘ oldOut) **
              (.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
              regOwn .x14 ** regOwn .x16 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
            regOwn .x15)
          ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            bodyFrameAfterEts spC s txBase lenW outPtr **
            bodyPayloadOk txBase txBytes outPtr **
            bodyScratch) := by
        refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x15) (fun v15 => ?_)
        have hx14 : cpsTripleWithin (5 + 2 + 1 + 1 + (1 + 4) + 1) AfterTypeBne EpiRestore fullCode
            (((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                bodyFrame spC s txBase lenW outPtr **
                bytesRegion txBase txBytes **
                memOwn ToBufAddr ** (IsCreationAddr ↦ₘ isC) **
                memOwn TypeAddr ** memOwn InnerOffAddr **
                (outPtr ↦ₘ oldOut) **
                (.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
                regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
                regOwn .x16 **
                regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
                (.x15 ↦ᵣ v15)) **
              regOwn .x14)
            ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              bodyFrameAfterEts spC s txBase lenW outPtr **
              bodyPayloadOk txBase txBytes outPtr **
              bodyScratch) := by
          refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x14) (fun v14 => ?_)
          have hx13 : cpsTripleWithin (5 + 2 + 1 + 1 + (1 + 4) + 1) AfterTypeBne EpiRestore fullCode
              (((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                  bodyFrame spC s txBase lenW outPtr **
                  bytesRegion txBase txBytes **
                  memOwn ToBufAddr ** (IsCreationAddr ↦ₘ isC) **
                  memOwn TypeAddr ** memOwn InnerOffAddr **
                  (outPtr ↦ₘ oldOut) **
                  (.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
                  regOwn .x11 ** regOwn .x12 **
                  regOwn .x16 **
                  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
                  (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15)) **
                regOwn .x13)
              ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                bodyFrameAfterEts spC s txBase lenW outPtr **
                bodyPayloadOk txBase txBytes outPtr **
                bodyScratch) := by
            refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x13) (fun v13 => ?_)
            have hx12 : cpsTripleWithin (5 + 2 + 1 + 1 + (1 + 4) + 1) AfterTypeBne EpiRestore fullCode
                (((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                    bodyFrame spC s txBase lenW outPtr **
                    bytesRegion txBase txBytes **
                    memOwn ToBufAddr ** (IsCreationAddr ↦ₘ isC) **
                    memOwn TypeAddr ** memOwn InnerOffAddr **
                    (outPtr ↦ₘ oldOut) **
                    (.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
                    regOwn .x11 **
                    regOwn .x16 **
                    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
                    (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15)) **
                  regOwn .x12)
                ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                  bodyFrameAfterEts spC s txBase lenW outPtr **
                  bodyPayloadOk txBase txBytes outPtr **
                  bodyScratch) := by
              refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12) (fun v12 => ?_)
              have hx11 : cpsTripleWithin (5 + 2 + 1 + 1 + (1 + 4) + 1) AfterTypeBne EpiRestore fullCode
                  (((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                      bodyFrame spC s txBase lenW outPtr **
                      bytesRegion txBase txBytes **
                      memOwn ToBufAddr ** (IsCreationAddr ↦ₘ isC) **
                      memOwn TypeAddr ** memOwn InnerOffAddr **
                      (outPtr ↦ₘ oldOut) **
                      (.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
                      regOwn .x16 **
                      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
                      (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
                      (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15)) **
                    regOwn .x11)
                  ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                    bodyFrameAfterEts spC s txBase lenW outPtr **
                    bodyPayloadOk txBase txBytes outPtr **
                    bodyScratch) := by
                refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11) (fun v11 => ?_)
                exact cpsTripleWithin_weaken
                  (fun _ hp => by xperm_hyp hp)
                  (fun _ hq => hq)
                  (hcore isC v5 v11 v12 v13 v14 v15)
              exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
                (fun _ hq => hq) hx11
            exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
              (fun _ hq => hq) hx12
          exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
            (fun _ hq => hq) hx13
        exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) hx14
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hx15
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hx5
  exact cpsTripleWithin_weaken
    (fun _ hp => by unfold bodyPayload bodyScratch at hp; xperm_hyp hp)
    (fun _ hq => hq) hpeel

/-- Live saved-register values at EpiRestore after ets success. -/
def etsCurSaved (s : TisSaved) (txBase lenW outPtr : Word) : TisSaved :=
  { ra := LinkEts, s0 := txBase, s1 := lenW, s2 := outPtr
    s3 := s.s3, s4 := 0, s5 := s.s5, s6 := s.s6 }

/-- Reshape ets post → epi pre (regsAt cur + payload). -/
private theorem etsPost_to_epiPre
    (spC : Word) (s : TisSaved)
    (txBase lenW outPtr : Word) (txBytes : List (BitVec 8)) :
    ∀ h,
      ((.x1 ↦ᵣ LinkEts) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bodyFrameAfterEts spC s txBase lenW outPtr **
        bodyPayloadOk txBase txBytes outPtr **
        bodyScratch) h →
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt tisFrame (tisSavedVals (etsCurSaved s txBase lenW outPtr)) **
          frameSlotsSaved tisFrame spC (tisSavedVals s)) **
        (bodyPayloadOk txBase txBytes outPtr ** bodyScratch **
          (.x0 ↦ᵣ (0 : Word)))) h := by
  intro h hp
  unfold bodyFrameAfterEts bodyPayloadOk bodyScratch at hp
  unfold bodyPayloadOk bodyScratch
  rw [regsAt_tisFrame]
  simp only [etsCurSaved]
  xperm_hyp hp

set_option maxRecDepth 8000 in
theorem txIntrinsicStateGas_success_spec_within
    (asm : TisCalleeAssumptions fullCode)
    (hextract : asm.extract.entry = ExtractEntry)
    (htype : asm.typeDispatch.entry = TypeEntry)
    (sp0 spC : Word) (s : TisSaved)
    (txBase lenW outPtr oldOut : Word)
    (txBytes : List (BitVec 8))
    (old5 old6 old7 old13 old14 old15 old16 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts)
    (hextractOk : extractSuccess txBytes)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin nTisTopSteps T s.ra fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt tisFrame (tisSavedVals s) **
        frameSlotsOwn tisFrame spC **
        prologueAbiRest txBase lenW outPtr old5 old6 old7 old13 old14 old15 old16 **
        bodyPayload txBase txBytes outPtr oldOut)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        frameSlotsSaved tisFrame spC (tisSavedVals s) **
        bodyPayloadOk txBase txBytes outPtr **
        bodyScratch ** (.x0 ↦ᵣ (0 : Word))) := by
  have hpro0 := prologue_full sp0 spC s txBase lenW outPtr
    old5 old6 old7 old13 old14 old15 old16 hspC
  have hpro := cpsTripleWithin_frameR
    (bodyPayload txBase txBytes outPtr oldOut)
    (by unfold bodyPayload; pcf) hpro0
  have hex := tisExtractFramed asm.extract hextract spC s
    txBase lenW outPtr oldOut txBytes
    old5 old6 old7 old13 old14 old15 old16 hlen hextractOk
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hpro hex
  have hty := tisTypeFramed asm.typeDispatch htype spC s
    txBase lenW outPtr oldOut txBytes hlen hsuccess halign hover hvalid0
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hty
  have hets := tisEtsFramed spC s txBase lenW outPtr oldOut txBytes hlink
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 hets
  have hepi0 := epi_full sp0 spC s (etsCurSaved s txBase lenW outPtr) 0 hspC hret
  have hepi := cpsTripleWithin_frameR
    (bodyPayloadOk txBase txBytes outPtr ** bodyScratch **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold bodyPayloadOk bodyScratch; pcf) hepi0
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (etsPost_to_epiPre spC s txBase lenW outPtr txBytes) c03 hepi
  have hle : 14 + (4 + (1 + nExtractSteps) + 1) + (6 + (1 + nTypeSteps) + 1) +
      (5 + 2 + 1 + 1 + (1 + 4) + 1) + 10 ≤ nTisTopSteps := by
    simp only [nTisTopSteps]; omega
  have c04' := cpsTripleWithin_mono_nSteps hle c04
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      unfold bodyPayloadOk bodyScratch at *
      xperm_hyp hq) c04'

#print axioms txIntrinsicStateGas_success_spec_within

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
