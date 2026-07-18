/-
  Ambient extract setup+call+BNE under ExtractAssumedAmbient (multi-tx Option A).

  Slice form owns bytesRegion loadPtr slice (loadPtr%8=0). Ambient keeps
  bytesRegion regionBase bs with loadPtr = regionBase+off.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasExtract
import EvmAsm.Codegen.Programs.TxExtractToAddressAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.DualReadByteScan (validByteRange)
open EvmAsm.Codegen
open EvmAsm.Codegen.TxExtractToAddressSpec (ExtractAssumedAmbient)
open EvmAsm.Codegen.TxExtractToAddressModel (extractSuccess)
open EvmAsm.Codegen.TxTypeDispatchSpec (txSlice)

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
      | exact pcFree_stackFree _ _)

/-- Ambient callee footprint: loadPtr in a0; owns full regionBase/bs. -/
def extractCalleePAmbient (spVal regionBase loadPtr lenW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spVal) ** stackFree spVal nExtractStackDwords **
  (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
  (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
  (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
  (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
  (.x12 ↦ᵣ ToBufAddr) ** (.x13 ↦ᵣ IsCreationAddr) **
  bytesRegion regionBase bs **
  extractToBufOwn ToBufAddr ** memOwn IsCreationAddr ** teaScratchOwn **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

def extractCalleeQAmbient (spVal regionBase : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spVal) ** stackFree spVal nExtractStackDwords **
  (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
  (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
  (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
  (.x10 ↦ᵣ (0 : Word)) **
  bytesRegion regionBase bs **
  extractToBufOwn ToBufAddr ** memOwn IsCreationAddr ** teaScratchOwn **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem extractCalleePAmbient_pcFree (spVal regionBase loadPtr lenW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word) (bs : List (BitVec 8)) :
    (extractCalleePAmbient spVal regionBase loadPtr lenW
      s0 s1 s2 s3 s4 s5 s6 s7 bs).pcFree := by
  unfold extractCalleePAmbient; pcf

private theorem toBufAddr_align_amb : ToBufAddr.toNat % 8 = 0 := by
  simp only [ToBufAddr]; decide

private theorem toBufAddr_over_amb : ToBufAddr.toNat + 16 < 2 ^ 64 := by
  simp only [ToBufAddr]; decide

set_option maxRecDepth 8000 in
/-- Call extract under ExtractAssumedAmbient; success a0=0 at LinkExtract. -/
theorem tisExtractCallAmbient
    (asm : ExtractAssumedAmbient fullCode)
    (hentry : asm.entry = ExtractEntry)
    (spVal regionBase loadPtr lenW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (old1 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : extractSuccess (txSlice bs off len))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htvalid : isValidMemAccess (ToBufAddr + (16 : Word)) = true) :
    cpsTripleWithin (1 + nExtractSteps) (T + 72) LinkExtract fullCode
      ((.x1 ↦ᵣ old1) **
        extractCalleePAmbient spVal regionBase loadPtr lenW
          s0 s1 s2 s3 s4 s5 s6 s7 bs)
      ((.x1 ↦ᵣ LinkExtract) **
        extractCalleeQAmbient spVal regionBase s0 s1 s2 s3 s4 s5 s6 s7 bs) := by
  have hret : (LinkExtract &&& ~~~(1 : Word)) = LinkExtract := by
    simp only [LinkExtract, T]; decide
  have hcallee0 := asm.success_flat LinkExtract spVal regionBase loadPtr lenW
    ToBufAddr IsCreationAddr s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlen hsuccess halign hbound hover hvalidBuf
    toBufAddr_align_amb toBufAddr_over_amb htvalid
  have hcallee0' : cpsTripleWithin nExtractSteps asm.entry LinkExtract fullCode
      ((.x1 ↦ᵣ LinkExtract) **
        extractCalleePAmbient spVal regionBase loadPtr lenW
          s0 s1 s2 s3 s4 s5 s6 s7 bs)
      ((.x1 ↦ᵣ LinkExtract) **
        extractCalleeQAmbient spVal regionBase s0 s1 s2 s3 s4 s5 s6 s7 bs) := by
    unfold extractCalleePAmbient extractCalleeQAmbient
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcallee : cpsTripleWithin nExtractSteps ExtractEntry LinkExtract fullCode
      ((.x1 ↦ᵣ LinkExtract) **
        extractCalleePAmbient spVal regionBase loadPtr lenW
          s0 s1 s2 s3 s4 s5 s6 s7 bs)
      ((.x1 ↦ᵣ LinkExtract) **
        extractCalleeQAmbient spVal regionBase s0 s1 s2 s3 s4 s5 s6 s7 bs) := by
    rw [← hentry]; exact hcallee0'
  have hcall := callWithin_spec (T + 72) ExtractEntry old1 extractJalOff nExtractSteps
    (by show (T + 72) + signExtend21 extractJalOff = ExtractEntry; decide)
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 72) tisProg 18
        (.JAL .x1 extractJalOff) (by bv_omega) (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi))
    (extractCalleePAmbient_pcFree spVal regionBase loadPtr lenW
      s0 s1 s2 s3 s4 s5 s6 s7 bs)
    hcallee
  rw [show (T + 72 + 4 : Word) = LinkExtract from by
    simp only [LinkExtract]; bv_omega] at hcall
  exact hcall

set_option maxRecDepth 8000 in
/-- Extract setup + call + BNE ok under ExtractAssumedAmbient.
    Live s-regs: s0=loadPtr, s1=lenW, s2=outPtr, s3–s6 from TisSaved, s7 free. -/
theorem tisExtractSuccessAmbient
    (asm : ExtractAssumedAmbient fullCode)
    (hentry : asm.entry = ExtractEntry)
    (spVal regionBase loadPtr lenW outPtr : Word)
    (s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (old1 v12 v13 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : extractSuccess (txSlice bs off len))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htvalid : isValidMemAccess (ToBufAddr + (16 : Word)) = true) :
    cpsTripleWithin (4 + (1 + nExtractSteps) + 1) (T + 56) AfterExtractBne fullCode
      ((.x1 ↦ᵣ old1) ** (.x2 ↦ᵣ spVal) ** stackFree spVal nExtractStackDwords **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        bytesRegion regionBase bs **
        extractToBufOwn ToBufAddr ** memOwn IsCreationAddr ** teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkExtract) ** (.x2 ↦ᵣ spVal) ** stackFree spVal nExtractStackDwords **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        extractToBufOwn ToBufAddr ** memOwn IsCreationAddr ** teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  have hsetup := tisExtractSetup loadPtr lenW outPtr v12 v13
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** (.x2 ↦ᵣ spVal) ** stackFree spVal nExtractStackDwords **
      (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
      (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
      bytesRegion regionBase bs **
      extractToBufOwn ToBufAddr ** memOwn IsCreationAddr ** teaScratchOwn **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hsetup
  have hcall := tisExtractCallAmbient asm hentry spVal regionBase loadPtr lenW
    loadPtr lenW outPtr s3 s4 s5 s6 s7 bs off len old1
    hptr hlen hsuccess halign hbound hover hvalidBuf htvalid
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold extractCalleePAmbient at *
    xperm_hyp hp) hsetupF hcall
  have hbne := tisExtractBneOk
  have hbneF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkExtract) ** (.x2 ↦ᵣ spVal) ** stackFree spVal nExtractStackDwords **
      (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
      (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
      bytesRegion regionBase bs **
      extractToBufOwn ToBufAddr ** memOwn IsCreationAddr ** teaScratchOwn **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by pcf) hbne
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold extractCalleeQAmbient at *
    xperm_hyp hp) h01 hbneF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h12

#print axioms tisExtractCallAmbient
#print axioms tisExtractSuccessAmbient

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
