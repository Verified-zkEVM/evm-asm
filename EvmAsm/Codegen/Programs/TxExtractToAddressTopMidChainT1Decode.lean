/-
  T1 mid-chain of_decode: AfterSave → AfterT1Walk4Bne under pure decode.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidSeqT1Decode
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwnedLT
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)

/-- Reshape t1 start frame (+ midOwned) to t10 CallOk pre under hcur. -/
theorem t1StartFrame_to_t10CallPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat)
    (hcur : cursor = txBase + BitVec.ofNat 64 srcOff0) :
    ∀ h, (t1StartFrame txBase lenW innerW cursor endPtr txBytes **
        midOwned spC s toBuf isCreationPtr s7) h →
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff0) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff0)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) h := by
  intro h hp
  -- Put x5 rightmost before (x0 ** midOwned); convert to regOwn; xperm to goal
  let Core : Assertion :=
    (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
      bytesRegion txBase txBytes **
      (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff0)) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x21 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff0)) **
      (.x22 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (1 : Word))
  let Tail : Assertion :=
    (.x0 ↦ᵣ (0 : Word)) ** midOwned spC s toBuf isCreationPtr s7
  have hp1 : ((Core ** (.x5 ↦ᵣ (1 : Word))) ** Tail) h := by
    simp only [hcur, t1StartFrame, afterSaveFrameTy, Core, Tail] at hp ⊢
    xperm_hyp hp
  obtain ⟨ha, hb, hda, hua, hCoreX5, hTail⟩ := hp1
  obtain ⟨hc, hd', hdc, huc, hCore, hx5⟩ := hCoreX5
  have hx5' : regOwn .x5 hd' := ⟨(1 : Word), hx5⟩
  have hp2 : ((Core ** regOwn .x5) ** Tail) h :=
    ⟨ha, hb, hda, hua, ⟨hc, hd', hdc, huc, hCore, hx5'⟩, hTail⟩
  simp only [t1Stable, Core, Tail] at hp2 ⊢
  xperm_hyp hp2

set_option maxRecDepth 8000 in
/-- T1 AfterSave → AfterT1Walk0Bne under pure decode. -/
theorem extractT1ToWalk0Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat)
    (hcur : cursor = txBase + BitVec.ofNat 64 srcOff0)
    (hsalign : txBase.toNat % 8 = 0)

    (hoff0 : srcOff0 < txBytes.length)
    (hover0 : txBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < txBytes.length ∧ txBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff0 + 1 +
          ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1 + j)) = true)
    (hll0 : ¬ BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff0 + 1 +
          ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1 + j)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode txBytes srcOff0 (txBase + BitVec.ofNat 64 srcOff0)
        endPtr next0 len0)
    (hinb0 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff0) endPtr = true)
 :
    cpsTripleWithin
      (((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1))
      AfterSaveCursor AfterT1Walk0Bne extractLinkedCode
      (afterSaveFrameTy txBase lenW (1 : Word) innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (1 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next0 len0 : Word,
        (t10OkConcrete txBase lenW innerW endPtr next0 len0
          txBytes srcOff0 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hBr := extractTypeBranchT1_owned spC s txBase lenW innerW
    cursor endPtr toBuf isCreationPtr s7 txBytes
  -- Branch post ↔ t1StartFrame ** midOwned (assoc)
  have hBr' :
      cpsTripleWithin (1 + (1 + (1 + 1))) AfterSaveCursor T1Start extractLinkedCode
        (afterSaveFrameTy txBase lenW (1 : Word) innerW cursor endPtr txBytes **
          (.x20 ↦ᵣ (1 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
          midOwned spC s toBuf isCreationPtr s7)
        (t1StartFrame txBase lenW innerW cursor endPtr txBytes **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [t1StartFrame] at hq ⊢
      xperm_hyp hq) hBr
  have hLoad := extractT1LoadArgs_owned spC s txBase lenW innerW
    cursor endPtr toBuf isCreationPtr s7 txBytes
  have hBrLoad := cpsTripleWithin_seq_same_cr hBr' hLoad
  have hBrLoad2 :
      cpsTripleWithin ((1 + (1 + (1 + 1))) + (1 + 1))
        AfterSaveCursor T1Walk0JalPc extractLinkedCode
        (afterSaveFrameTy txBase lenW (1 : Word) innerW cursor endPtr txBytes **
          (.x20 ↦ᵣ (1 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
          midOwned spC s toBuf isCreationPtr s7)
        (t1Stable txBase lenW innerW endPtr
            (txBase + BitVec.ofNat 64 srcOff0) **
          (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff0)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq =>
      t1StartFrame_to_t10CallPre spC s txBase lenW innerW cursor
        endPtr toBuf isCreationPtr s7 txBytes srcOff0 hcur _ hq) hBrLoad
  have hOk := extractT1Walk0CallOk_owned_of_decode spC s txBase lenW innerW endPtr
    toBuf isCreationPtr s7 txBytes srcOff0
    hsalign hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
  exact cpsTripleWithin_seq_same_cr hBrLoad2 hOk


set_option maxRecDepth 8000 in
/-- AfterT1Walk0Bne → AfterT1Walk1Bne under pure decode. -/
theorem extractT1Walk0to1Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next0 len0 toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 srcOff1 : Nat)
    (hnext : next0 = txBase + BitVec.ofNat 64 srcOff1)
    (hsalign : txBase.toNat % 8 = 0)

    (hoff1 : srcOff1 < txBytes.length)
    (hover1 : txBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < txBytes.length ∧ txBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff1 + 1 +
          ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + j)) = true)
    (hll1 : ¬ BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff1 + 1 +
          ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + j)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode txBytes srcOff1 (txBase + BitVec.ofNat 64 srcOff1)
        endPtr next1 len1)
    (hinb1 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff1) endPtr = true)
 :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk0Bne AfterT1Walk1Bne extractLinkedCode
      (t10OkConcrete txBase lenW innerW endPtr next0 len0
          txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next1 len1 : Word,
        (t11OkConcrete txBase lenW innerW endPtr next1 len1
          txBytes srcOff1 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractT1Walk1PrepCallOk_owned_of_decode spC s txBase lenW innerW endPtr
    next0 len0 toBuf isCreationPtr s7 txBytes srcOff0 srcOff1
    hnext hsalign hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1


set_option maxRecDepth 8000 in
/-- AfterT1Walk1Bne → AfterT1Walk2Bne under pure decode. -/
theorem extractT1Walk1to2Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next1 len1 toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff1 srcOff2 : Nat)
    (hnext : next1 = txBase + BitVec.ofNat 64 srcOff2)
    (hsalign : txBase.toNat % 8 = 0)

    (hoff2 : srcOff2 < txBytes.length)
    (hover2 : txBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < txBytes.length ∧ txBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff2 + 1 +
          ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff2 + 1 + j)) = true)
    (hll2 : ¬ BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff2 + 1 +
          ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff2 + 1 + j)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode txBytes srcOff2 (txBase + BitVec.ofNat 64 srcOff2)
        endPtr next2 len2)
    (hinb2 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff2) endPtr = true)
 :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk1Bne AfterT1Walk2Bne extractLinkedCode
      (t11OkConcrete txBase lenW innerW endPtr next1 len1
          txBytes srcOff1 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next2 len2 : Word,
        (t12OkConcrete txBase lenW innerW endPtr next2 len2
          txBytes srcOff2 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractT1Walk2PrepCallOk_owned_of_decode spC s txBase lenW innerW endPtr
    next1 len1 toBuf isCreationPtr s7 txBytes srcOff1 srcOff2
    hnext hsalign hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2


set_option maxRecDepth 8000 in
/-- AfterT1Walk2Bne → AfterT1Walk3Bne under pure decode. -/
theorem extractT1Walk2to3Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next2 len2 toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff2 srcOff3 : Nat)
    (hnext : next2 = txBase + BitVec.ofNat 64 srcOff3)
    (hsalign : txBase.toNat % 8 = 0)

    (hoff3 : srcOff3 < txBytes.length)
    (hover3 : txBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < txBytes.length ∧ txBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff3 + 1 +
          ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff3 + 1 + j)) = true)
    (hll3 : ¬ BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff3 + 1 +
          ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff3 + 1 + j)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode txBytes srcOff3 (txBase + BitVec.ofNat 64 srcOff3)
        endPtr next3 len3)
    (hinb3 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff3) endPtr = true)
 :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk2Bne AfterT1Walk3Bne extractLinkedCode
      (t12OkConcrete txBase lenW innerW endPtr next2 len2
          txBytes srcOff2 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next3 len3 : Word,
        (t13OkConcrete txBase lenW innerW endPtr next3 len3
          txBytes srcOff3 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractT1Walk3PrepCallOk_owned_of_decode spC s txBase lenW innerW endPtr
    next2 len2 toBuf isCreationPtr s7 txBytes srcOff2 srcOff3
    hnext hsalign hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3


theorem extractT1Walk3to4Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next3 len3 toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff3 srcOff4 : Nat)
    (hnext : next3 = txBase + BitVec.ofNat 64 srcOff4)
    (hsalign : txBase.toNat % 8 = 0)

    (hoff4 : srcOff4 < txBytes.length)
    (hover4 : txBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < txBytes.length ∧ txBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff4 + 1 +
          ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff4 + 1 + j)) = true)
    (hll4 : ¬ BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff4 + 1 +
          ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff4 + 1 + j)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4)
        endPtr next4 len4)
    (hinb4 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff4) endPtr = true)
 :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk3Bne AfterT1Walk4Bne extractLinkedCode
      (t13OkConcrete txBase lenW innerW endPtr next3 len3
          txBytes srcOff3 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next4 len4 : Word,
        (t14OkConcrete txBase lenW innerW endPtr next4 len4
          txBytes srcOff4 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractT1Walk4PrepCallOk_owned_of_decode spC s txBase lenW innerW endPtr
    next3 len3 toBuf isCreationPtr s7 txBytes srcOff3 srcOff4
    hnext hsalign hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4



theorem extractT1ToWalk4Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8))
    (srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 : Nat)
    (hcur : cursor = txBase + BitVec.ofNat 64 srcOff0)
    (hsalign : txBase.toNat % 8 = 0)

    (hoff0 : srcOff0 < txBytes.length)
    (hover0 : txBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < txBytes.length ∧ txBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff0 + 1 +
          ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1 + j)) = true)
    (hll0 : ¬ BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff0 + 1 +
          ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1 + j)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode txBytes srcOff0 (txBase + BitVec.ofNat 64 srcOff0)
        endPtr next0 len0)
    (hinb0 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff0) endPtr = true)
    (hoff1 : srcOff1 < txBytes.length)
    (hover1 : txBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < txBytes.length ∧ txBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff1 + 1 +
          ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + j)) = true)
    (hll1 : ¬ BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff1 + 1 +
          ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + j)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode txBytes srcOff1 (txBase + BitVec.ofNat 64 srcOff1)
        endPtr next1 len1)
    (hinb1 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff1) endPtr = true)
    (hoff2 : srcOff2 < txBytes.length)
    (hover2 : txBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < txBytes.length ∧ txBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff2 + 1 +
          ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff2 + 1 + j)) = true)
    (hll2 : ¬ BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff2 + 1 +
          ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff2 + 1 + j)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode txBytes srcOff2 (txBase + BitVec.ofNat 64 srcOff2)
        endPtr next2 len2)
    (hinb2 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff2) endPtr = true)
    (hoff3 : srcOff3 < txBytes.length)
    (hover3 : txBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < txBytes.length ∧ txBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff3 + 1 +
          ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff3 + 1 + j)) = true)
    (hll3 : ¬ BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff3 + 1 +
          ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff3 + 1 + j)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode txBytes srcOff3 (txBase + BitVec.ofNat 64 srcOff3)
        endPtr next3 len3)
    (hinb3 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff3) endPtr = true)
    (hoff4 : srcOff4 < txBytes.length)
    (hover4 : txBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < txBytes.length ∧ txBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff4 + 1 +
          ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff4 + 1 + j)) = true)
    (hll4 : ¬ BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff4 + 1 +
          ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff4 + 1 + j)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4)
        endPtr next4 len4)
    (hinb4 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff4) endPtr = true)
    (hnext1 : ∀ (next0 len0 : Word),
      rlpItemDecode txBytes srcOff0 (txBase + BitVec.ofNat 64 srcOff0)
        endPtr next0 len0 →
      next0 = txBase + BitVec.ofNat 64 srcOff1)
    (hnext2 : ∀ (next1 len1 : Word),
      rlpItemDecode txBytes srcOff1 (txBase + BitVec.ofNat 64 srcOff1)
        endPtr next1 len1 →
      next1 = txBase + BitVec.ofNat 64 srcOff2)
    (hnext3 : ∀ (next2 len2 : Word),
      rlpItemDecode txBytes srcOff2 (txBase + BitVec.ofNat 64 srcOff2)
        endPtr next2 len2 →
      next2 = txBase + BitVec.ofNat 64 srcOff3)
    (hnext4 : ∀ (next3 len3 : Word),
      rlpItemDecode txBytes srcOff3 (txBase + BitVec.ofNat 64 srcOff3)
        endPtr next3 len3 →
      next3 = txBase + BitVec.ofNat 64 srcOff4)
 :
    cpsTripleWithin
      (((((((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1))
      AfterSaveCursor AfterT1Walk4Bne extractLinkedCode
      (afterSaveFrameTy txBase lenW (1 : Word) innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (1 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next4 len4 : Word,
        (t14OkConcrete txBase lenW innerW endPtr next4 len4
          txBytes srcOff4 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h0 := extractT1ToWalk0Ok_owned_of_decode spC s txBase lenW innerW
    cursor endPtr toBuf isCreationPtr s7 txBytes srcOff0
    hcur hsalign hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
  have h1 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterT1Walk0Bne AfterT1Walk1Bne extractLinkedCode
        (fun h => ∃ next0 len0 : Word,
          (t10OkConcrete txBase lenW innerW endPtr next0 len0
            txBytes srcOff0 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next1 len1 : Word,
          (t11OkConcrete txBase lenW innerW endPtr next1 len1
            txBytes srcOff1 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next0 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len0 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterT1Walk0Bne AfterT1Walk1Bne extractLinkedCode
          (⌜rlpItemDecode txBytes srcOff0 (txBase + BitVec.ofNat 64 srcOff0)
              endPtr next0 len0⌝ **
            (t10OkRegs txBase lenW innerW endPtr next0 len0
              txBytes srcOff0 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next1 len1 : Word,
            (t11OkConcrete txBase lenW innerW endPtr next1 len1
              txBytes srcOff1 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractT1Walk0to1Ok_owned_of_decode spC s txBase lenW
        innerW endPtr next0 len0 toBuf isCreationPtr s7 txBytes
        srcOff0 srcOff1
        (hnext1 next0 len0 hdecN) hsalign
        hoff1 hover1 hvalid1 hss1 hls1 hll1
        hdec1 hinb1
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : t10OkConcrete txBase lenW innerW endPtr next0 len0
            txBytes srcOff0 h1 := by
          simp only [t10OkConcrete]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [t10OkConcrete] using hOkC)
      have hRest :
          (t10OkRegs txBase lenW innerW endPtr next0 len0
            txBytes srcOff0 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure
  have h2 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterT1Walk1Bne AfterT1Walk2Bne extractLinkedCode
        (fun h => ∃ next1 len1 : Word,
          (t11OkConcrete txBase lenW innerW endPtr next1 len1
            txBytes srcOff1 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next2 len2 : Word,
          (t12OkConcrete txBase lenW innerW endPtr next2 len2
            txBytes srcOff2 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next1 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len1 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterT1Walk1Bne AfterT1Walk2Bne extractLinkedCode
          (⌜rlpItemDecode txBytes srcOff1 (txBase + BitVec.ofNat 64 srcOff1)
              endPtr next1 len1⌝ **
            (t11OkRegs txBase lenW innerW endPtr next1 len1
              txBytes srcOff1 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next2 len2 : Word,
            (t12OkConcrete txBase lenW innerW endPtr next2 len2
              txBytes srcOff2 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractT1Walk1to2Ok_owned_of_decode spC s txBase lenW
        innerW endPtr next1 len1 toBuf isCreationPtr s7 txBytes
        srcOff1 srcOff2
        (hnext2 next1 len1 hdecN) hsalign
        hoff2 hover2 hvalid2 hss2 hls2 hll2
        hdec2 hinb2
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : t11OkConcrete txBase lenW innerW endPtr next1 len1
            txBytes srcOff1 h1 := by
          simp only [t11OkConcrete]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [t11OkConcrete] using hOkC)
      have hRest :
          (t11OkRegs txBase lenW innerW endPtr next1 len1
            txBytes srcOff1 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure
  have h3 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterT1Walk2Bne AfterT1Walk3Bne extractLinkedCode
        (fun h => ∃ next2 len2 : Word,
          (t12OkConcrete txBase lenW innerW endPtr next2 len2
            txBytes srcOff2 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next3 len3 : Word,
          (t13OkConcrete txBase lenW innerW endPtr next3 len3
            txBytes srcOff3 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next2 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len2 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterT1Walk2Bne AfterT1Walk3Bne extractLinkedCode
          (⌜rlpItemDecode txBytes srcOff2 (txBase + BitVec.ofNat 64 srcOff2)
              endPtr next2 len2⌝ **
            (t12OkRegs txBase lenW innerW endPtr next2 len2
              txBytes srcOff2 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next3 len3 : Word,
            (t13OkConcrete txBase lenW innerW endPtr next3 len3
              txBytes srcOff3 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractT1Walk2to3Ok_owned_of_decode spC s txBase lenW
        innerW endPtr next2 len2 toBuf isCreationPtr s7 txBytes
        srcOff2 srcOff3
        (hnext3 next2 len2 hdecN) hsalign
        hoff3 hover3 hvalid3 hss3 hls3 hll3
        hdec3 hinb3
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : t12OkConcrete txBase lenW innerW endPtr next2 len2
            txBytes srcOff2 h1 := by
          simp only [t12OkConcrete]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [t12OkConcrete] using hOkC)
      have hRest :
          (t12OkRegs txBase lenW innerW endPtr next2 len2
            txBytes srcOff2 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure
  have h4 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterT1Walk3Bne AfterT1Walk4Bne extractLinkedCode
        (fun h => ∃ next3 len3 : Word,
          (t13OkConcrete txBase lenW innerW endPtr next3 len3
            txBytes srcOff3 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next4 len4 : Word,
          (t14OkConcrete txBase lenW innerW endPtr next4 len4
            txBytes srcOff4 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next3 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len3 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterT1Walk3Bne AfterT1Walk4Bne extractLinkedCode
          (⌜rlpItemDecode txBytes srcOff3 (txBase + BitVec.ofNat 64 srcOff3)
              endPtr next3 len3⌝ **
            (t13OkRegs txBase lenW innerW endPtr next3 len3
              txBytes srcOff3 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next4 len4 : Word,
            (t14OkConcrete txBase lenW innerW endPtr next4 len4
              txBytes srcOff4 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractT1Walk3to4Ok_owned_of_decode spC s txBase lenW
        innerW endPtr next3 len3 toBuf isCreationPtr s7 txBytes
        srcOff3 srcOff4
        (hnext4 next3 len3 hdecN) hsalign
        hoff4 hover4 hvalid4 hss4 hls4 hll4
        hdec4 hinb4
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : t13OkConcrete txBase lenW innerW endPtr next3 len3
            txBytes srcOff3 h1 := by
          simp only [t13OkConcrete]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [t13OkConcrete] using hOkC)
      have hRest :
          (t13OkRegs txBase lenW innerW endPtr next3 len3
            txBytes srcOff3 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure
  have h01 := cpsTripleWithin_seq_same_cr h0 h1
  have h012 := cpsTripleWithin_seq_same_cr h01 h2
  have h0123 := cpsTripleWithin_seq_same_cr h012 h3
  exact cpsTripleWithin_seq_same_cr h0123 h4


#print axioms extractT1ToWalk0Ok_owned_of_decode
#print axioms extractT1Walk0to1Ok_owned_of_decode
#print axioms extractT1Walk1to2Ok_owned_of_decode
#print axioms extractT1Walk2to3Ok_owned_of_decode
#print axioms extractT1Walk3to4Ok_owned_of_decode
#print axioms extractT1ToWalk4Ok_owned_of_decode
