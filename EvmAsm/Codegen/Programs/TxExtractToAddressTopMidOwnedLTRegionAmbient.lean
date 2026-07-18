/-
  Ambient dual: legacy HaveField copy under midOwned (region partition).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwnedLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopJoinRegionAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressCopyFromRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressTopLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)

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
      | exact bytesRegion_pcFree _ _)

set_option maxRecDepth 8000 in
theorem extractLegacyHaveFieldCopy_then_epi_region_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff3 q : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hnext : next = regionBase + BitVec.ofNat 64 (8 * q) + (20 : Word))
    (hq : 8 * q + 16 < bs.length)
    (halign : regionBase.toNat % 8 = 0)
    (hcover : regionBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    let contentPtr := regionBase + BitVec.ofNat 64 (8 * q)
    let _w0 := (contentWordsAt bs q).1
    let _w1 := (contentWordsAt bs q).2.1
    let w2 := (contentWordsAt bs q).2.2
    cpsTripleWithin
      ((1 + 1) +
        ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11))
      AfterLegacyWalk3Bne s.ra extractLinkedCode
      (leg3OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next
          (20 : Word) bs absOff3 **
        midOwned spC s toBuf isCreationPtr s7)
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        extractToBufOwn toBuf **
        (isCreationPtr ↦ₘ (0 : Word)) **
        (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        (.x5 ↦ᵣ (extractWord32 w2
            (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
        (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
  intro contentPtr _w0 _w1 w2
  let cursor := regionBase + BitVec.ofNat 64 absOff3
  have hsub : next - (20 : Word) = contentPtr := by
    rw [hnext]; exact BitVec.add_sub_cancel contentPtr (20 : Word)
  have hTo := extractLegacyToHaveField_owned_ambient spC s loadPtr regionBase
    lenW innerW endPtr next (20 : Word) toBuf isCreationPtr s7 bs absOff3
  have hCopy :
      cpsTripleWithin
        ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)
        HaveField s.ra extractLinkedCode
        (legStableAmbient loadPtr lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
          bytesRegion regionBase bs **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          midOwned spC s toBuf isCreationPtr s7)
        ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
          stackFree sp0 nExtractStackDwords **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs **
          extractToBufOwn toBuf **
          (isCreationPtr ↦ₘ (0 : Word)) **
          (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
          (Reg.x23 ↦ᵣ s.s7) **
          (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
          (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
    let Pcore : Assertion :=
      haveFieldCopyAmbientNoBytes loadPtr lenW (0 : Word) innerW endPtr cursor **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkLegacyWalk3) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) **
        (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x10 ↦ᵣ next) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        memOwn toBuf ** memOwn (toBuf + 8) ** memOwn isCreationPtr **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30
    have htemps :
        cpsTripleWithin
          ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)
          HaveField s.ra extractLinkedCode
          (Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** regOwn .x6 ** regOwn .x5)
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            stackFree sp0 nExtractStackDwords **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion regionBase bs **
            extractToBufOwn toBuf **
            (isCreationPtr ↦ₘ (0 : Word)) **
            (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
            (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
            (Reg.x23 ↦ᵣ s.s7) **
            (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
            (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
            (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
            (.x31 ↦ᵣ contentPtr) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
          (P := Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** regOwn .x6)
          (fun t0Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
          (P := Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** (.x5 ↦ᵣ t0Old))
          (fun t1Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
          (P := Pcore ** memOwn (toBuf + 16) ** (.x6 ↦ᵣ t1Old) ** (.x5 ↦ᵣ t0Old))
          (fun t2Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_memIs_to_memOwn (a := toBuf + 16)
          (P := Pcore ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) ** (.x5 ↦ᵣ t0Old))
          (fun old16' => ?_))
      have h := extractHaveFieldCopy_then_epi_region_ambient sp0 spC s loadPtr
        regionBase lenW (0 : Word) innerW endPtr cursor toBuf isCreationPtr t2Old t1Old
        t0Old next old16' LinkLegacyWalk3 s7 bs q hspC hret hq halign hcover hcvalid
        htalign htover htvalid
      have hF := cpsTripleWithin_frameR
        (regOwn .x28 ** regOwn .x29 ** regOwn .x30)
        (by
          apply pcFree_sepConj
          · exact pcFree_regOwn
          · apply pcFree_sepConj
            · exact pcFree_regOwn
            · exact pcFree_regOwn) h
      exact cpsTripleWithin_weaken (fun _ hp => by
        dsimp only [Pcore, contentPtr, w0, w1, w2] at hp ⊢
        xperm_hyp hp) (fun _ hq => by
        dsimp only [contentPtr, w0, w1, w2] at hq ⊢
        xperm_hyp hq) hF
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, midOwned, joinStackAmbient, haveFieldCopyAmbientNoBytes,
        extractToBufOwn, legStableAmbient, contentPtr] at hp ⊢
      xperm_hyp hp) (fun _ hq => hq) htemps
  have hTo2 :
      cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
        (leg3OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next
            (20 : Word) bs absOff3 **
          midOwned spC s toBuf isCreationPtr s7)
        (legStableAmbient loadPtr lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
          bytesRegion regionBase bs **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
      dsimp only [contentPtr, cursor, hsub] at hq ⊢
      simp only [hsub] at hq ⊢
      xperm_hyp hq) hTo
  exact cpsTripleWithin_seq_same_cr hTo2 hCopy

#print axioms extractLegacyHaveFieldCopy_then_epi_region_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
