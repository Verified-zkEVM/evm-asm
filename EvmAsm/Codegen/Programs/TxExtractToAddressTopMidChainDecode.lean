/-
  Mid-chain of_decode: replace universal hok with pure decode+inbounds.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidChain
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidChainRest
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidSeq
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidSeqDecode
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)

set_option maxRecDepth 8000 in
/-- type234 AfterSave → AfterWalkNext0Bne under pure decode (no universal hok). -/
theorem extractType234ToWn0Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat)
    (hcur : cursor = txBase + BitVec.ofNat 64 srcOff0)
    (hne0 : typeW ≠ 0) (hne1 : typeW ≠ 1)
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
        ∀ k, k < ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff0 + 1 +
          ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode txBytes srcOff0 (txBase + BitVec.ofNat 64 srcOff0)
        endPtr next0 len0)
    (hinb0 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff0) endPtr = true) :
    cpsTripleWithin
      (((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1))
      AfterSaveCursor AfterWalkNext0Bne extractLinkedCode
      (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next0 len0 : Word,
        (wn0OkConcrete txBase lenW typeW innerW endPtr next0 len0
          txBytes srcOff0 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hBr := extractType234ToWalkNext0_owned spC s txBase lenW typeW innerW
    cursor endPtr toBuf isCreationPtr s7 txBytes hne0 hne1
  have hBr2 :
      cpsTripleWithin ((1 + (1 + (1 + 1))) + (1 + 1))
        AfterSaveCursor WalkNext0JalPc extractLinkedCode
        (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
          (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
          midOwned spC s toBuf isCreationPtr s7)
        (type234StartFrame txBase lenW typeW innerW
            (txBase + BitVec.ofNat 64 srcOff0) endPtr txBytes **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [hcur] at hq
      exact hq) hBr
  have hOk := extractWalkNext0CallOk_owned_of_decode spC s txBase lenW typeW innerW endPtr
    toBuf isCreationPtr s7 txBytes srcOff0
    hsalign hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
  exact cpsTripleWithin_seq_same_cr hBr2 hOk

set_option maxRecDepth 8000 in
/-- AfterWalkNext0Bne → AfterWalkNext1Bne under pure decode. -/
theorem extractWalkNext0to1Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next0 len0 toBuf isCreationPtr s7 : Word)
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
        ∀ k, k < ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff1 + 1 +
          ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode txBytes srcOff1 (txBase + BitVec.ofNat 64 srcOff1)
        endPtr next1 len1)
    (hinb1 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff1) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterWalkNext0Bne AfterWalkNext1Bne extractLinkedCode
      (wn0OkConcrete txBase lenW typeW innerW endPtr next0 len0
          txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next1 len1 : Word,
        (wn1OkConcrete txBase lenW typeW innerW endPtr next1 len1
          txBytes srcOff1 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractWalkNext1PrepCallOk_owned_of_decode spC s txBase lenW typeW innerW endPtr
    next0 len0 toBuf isCreationPtr s7 txBytes srcOff0 srcOff1
    hnext hsalign hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1

set_option maxRecDepth 8000 in
/-- AfterWalkNext1Bne → AfterWalkNext2Bne under pure decode. -/
theorem extractWalkNext1to2Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next1 len1 toBuf isCreationPtr s7 : Word)
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
        ∀ k, k < ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff2 + 1 +
          ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode txBytes srcOff2 (txBase + BitVec.ofNat 64 srcOff2)
        endPtr next2 len2)
    (hinb2 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff2) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterWalkNext1Bne AfterWalkNext2Bne extractLinkedCode
      (wn1OkConcrete txBase lenW typeW innerW endPtr next1 len1
          txBytes srcOff1 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next2 len2 : Word,
        (wn2OkConcrete txBase lenW typeW innerW endPtr next2 len2
          txBytes srcOff2 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractWalkNext2PrepCallOk_owned_of_decode spC s txBase lenW typeW innerW endPtr
    next1 len1 toBuf isCreationPtr s7 txBytes srcOff1 srcOff2
    hnext hsalign hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2

set_option maxRecDepth 8000 in
/-- AfterWalkNext2Bne → AfterWalkNext3Bne under pure decode. -/
theorem extractWalkNext2to3Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next2 len2 toBuf isCreationPtr s7 : Word)
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
        ∀ k, k < ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff3 + 1 +
          ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode txBytes srcOff3 (txBase + BitVec.ofNat 64 srcOff3)
        endPtr next3 len3)
    (hinb3 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff3) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterWalkNext2Bne AfterWalkNext3Bne extractLinkedCode
      (wn2OkConcrete txBase lenW typeW innerW endPtr next2 len2
          txBytes srcOff2 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next3 len3 : Word,
        (wn3OkConcrete txBase lenW typeW innerW endPtr next3 len3
          txBytes srcOff3 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractWalkNext3PrepCallOk_owned_of_decode spC s txBase lenW typeW innerW endPtr
    next2 len2 toBuf isCreationPtr s7 txBytes srcOff2 srcOff3
    hnext hsalign hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3

set_option maxRecDepth 8000 in
/-- AfterWalkNext3Bne → AfterWalkNext4Bne under pure decode. -/
theorem extractWalkNext3to4Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next3 len3 toBuf isCreationPtr s7 : Word)
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
        ∀ k, k < ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff4 + 1 +
          ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4)
        endPtr next4 len4)
    (hinb4 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff4) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterWalkNext3Bne AfterWalkNext4Bne extractLinkedCode
      (wn3OkConcrete txBase lenW typeW innerW endPtr next3 len3
          txBytes srcOff3 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next4 len4 : Word,
        (wn4OkConcrete txBase lenW typeW innerW endPtr next4 len4
          txBytes srcOff4 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractWalkNext4PrepCallOk_owned_of_decode spC s txBase lenW typeW innerW endPtr
    next3 len3 toBuf isCreationPtr s7 txBytes srcOff3 srcOff4
    hnext hsalign hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4

set_option maxRecDepth 8000 in
/-- AfterWalkNext4Bne → AfterWalkNext5Bne under pure decode. -/
theorem extractWalkNext4to5Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next4 len4 toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff4 srcOff5 : Nat)
    (hnext : next4 = txBase + BitVec.ofNat 64 srcOff5)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff5 : srcOff5 < txBytes.length)
    (hover5 : txBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((txBytes[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < txBytes.length ∧ txBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((txBytes[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff5 + 1 +
          ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((txBytes[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff5 + 1 +
          ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next5 len5 : Word,
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5)
        endPtr next5 len5)
    (hinb5 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff5) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterWalkNext4Bne AfterWalkNext5Bne extractLinkedCode
      (wn4OkConcrete txBase lenW typeW innerW endPtr next4 len4
          txBytes srcOff4 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next5 len5 : Word,
        (wn5OkConcrete txBase lenW typeW innerW endPtr next5 len5
          txBytes srcOff5 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractWalkNext5PrepCallOk_owned_of_decode spC s txBase lenW typeW innerW endPtr
    next4 len4 toBuf isCreationPtr s7 txBytes srcOff4 srcOff5
    hnext hsalign hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5

set_option maxRecDepth 8000 in
/-- type234 AfterSave → AfterWalkNext5Bne under pure decode (no universal hok). -/
theorem extractType234ToWn5Ok_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8))
    (srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 srcOff5 : Nat)
    (hcur : cursor = txBase + BitVec.ofNat 64 srcOff0)
    (hne0 : typeW ≠ 0) (hne1 : typeW ≠ 1)
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
        ∀ k, k < ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((txBytes[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff0 + 1 +
          ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
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
        ∀ k, k < ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((txBytes[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff1 + 1 +
          ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
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
        ∀ k, k < ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((txBytes[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff2 + 1 +
          ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
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
        ∀ k, k < ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((txBytes[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff3 + 1 +
          ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
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
        ∀ k, k < ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((txBytes[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff4 + 1 +
          ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4)
        endPtr next4 len4)
    (hinb4 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff4) endPtr = true)
    (hoff5 : srcOff5 < txBytes.length)
    (hover5 : txBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((txBytes[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < txBytes.length ∧ txBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((txBytes[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff5 + 1 +
          ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((txBytes[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff5 + 1 +
          ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next5 len5 : Word,
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5)
        endPtr next5 len5)
    (hinb5 : BitVec.ult (txBase + BitVec.ofNat 64 srcOff5) endPtr = true)
    (hnext1 : ∀ (next0 : Word) (_len0 : Word),
      next0 = txBase + BitVec.ofNat 64 srcOff1)
    (hnext2 : ∀ (next1 : Word) (_len1 : Word),
      next1 = txBase + BitVec.ofNat 64 srcOff2)
    (hnext3 : ∀ (next2 : Word) (_len2 : Word),
      next2 = txBase + BitVec.ofNat 64 srcOff3)
    (hnext4 : ∀ (next3 : Word) (_len3 : Word),
      next3 = txBase + BitVec.ofNat 64 srcOff4)
    (hnext5 : ∀ (next4 : Word) (_len4 : Word),
      next4 = txBase + BitVec.ofNat 64 srcOff5)
 :
    cpsTripleWithin ((((((((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1)) + (((1 + (1 + 1)) + (1 + 87)) + 1)) + (((1 + (1 + 1)) + (1 + 87)) + 1)) + (((1 + (1 + 1)) + (1 + 87)) + 1)) + (((1 + (1 + 1)) + (1 + 87)) + 1)) + (((1 + (1 + 1)) + (1 + 87)) + 1))
      AfterSaveCursor AfterWalkNext5Bne extractLinkedCode
      (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next5 len5 : Word,
        (wn5OkConcrete txBase lenW typeW innerW endPtr next5 len5
          txBytes srcOff5 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h0 := extractType234ToWn0Ok_owned_of_decode spC s txBase lenW typeW innerW
    cursor endPtr toBuf isCreationPtr s7 txBytes srcOff0
    hcur hne0 hne1 hsalign hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
  have h1 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterWalkNext0Bne AfterWalkNext1Bne extractLinkedCode
        (fun h => ∃ next0 len0 : Word,
          (wn0OkConcrete txBase lenW typeW innerW endPtr next0 len0
            txBytes srcOff0 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next1 len1 : Word,
          (wn1OkConcrete txBase lenW typeW innerW endPtr next1 len1
            txBytes srcOff1 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next0 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len0 => ?_)
    exact extractWalkNext0to1Ok_owned_of_decode spC s txBase lenW typeW innerW endPtr
      next0 len0 toBuf isCreationPtr s7 txBytes srcOff0 srcOff1
      (hnext1 next0 len0) hsalign hoff1 hover1 hvalid1 hss1 hls1 hll1
      hdec1 hinb1
  have h2 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterWalkNext1Bne AfterWalkNext2Bne extractLinkedCode
        (fun h => ∃ next1 len1 : Word,
          (wn1OkConcrete txBase lenW typeW innerW endPtr next1 len1
            txBytes srcOff1 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next2 len2 : Word,
          (wn2OkConcrete txBase lenW typeW innerW endPtr next2 len2
            txBytes srcOff2 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next1 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len1 => ?_)
    exact extractWalkNext1to2Ok_owned_of_decode spC s txBase lenW typeW innerW endPtr
      next1 len1 toBuf isCreationPtr s7 txBytes srcOff1 srcOff2
      (hnext2 next1 len1) hsalign hoff2 hover2 hvalid2 hss2 hls2 hll2
      hdec2 hinb2
  have h3 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterWalkNext2Bne AfterWalkNext3Bne extractLinkedCode
        (fun h => ∃ next2 len2 : Word,
          (wn2OkConcrete txBase lenW typeW innerW endPtr next2 len2
            txBytes srcOff2 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next3 len3 : Word,
          (wn3OkConcrete txBase lenW typeW innerW endPtr next3 len3
            txBytes srcOff3 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next2 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len2 => ?_)
    exact extractWalkNext2to3Ok_owned_of_decode spC s txBase lenW typeW innerW endPtr
      next2 len2 toBuf isCreationPtr s7 txBytes srcOff2 srcOff3
      (hnext3 next2 len2) hsalign hoff3 hover3 hvalid3 hss3 hls3 hll3
      hdec3 hinb3
  have h4 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterWalkNext3Bne AfterWalkNext4Bne extractLinkedCode
        (fun h => ∃ next3 len3 : Word,
          (wn3OkConcrete txBase lenW typeW innerW endPtr next3 len3
            txBytes srcOff3 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next4 len4 : Word,
          (wn4OkConcrete txBase lenW typeW innerW endPtr next4 len4
            txBytes srcOff4 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next3 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len3 => ?_)
    exact extractWalkNext3to4Ok_owned_of_decode spC s txBase lenW typeW innerW endPtr
      next3 len3 toBuf isCreationPtr s7 txBytes srcOff3 srcOff4
      (hnext4 next3 len3) hsalign hoff4 hover4 hvalid4 hss4 hls4 hll4
      hdec4 hinb4
  have h5 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterWalkNext4Bne AfterWalkNext5Bne extractLinkedCode
        (fun h => ∃ next4 len4 : Word,
          (wn4OkConcrete txBase lenW typeW innerW endPtr next4 len4
            txBytes srcOff4 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next5 len5 : Word,
          (wn5OkConcrete txBase lenW typeW innerW endPtr next5 len5
            txBytes srcOff5 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next4 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len4 => ?_)
    exact extractWalkNext4to5Ok_owned_of_decode spC s txBase lenW typeW innerW endPtr
      next4 len4 toBuf isCreationPtr s7 txBytes srcOff4 srcOff5
      (hnext5 next4 len4) hsalign hoff5 hover5 hvalid5 hss5 hls5 hll5
      hdec5 hinb5
  have h01 := cpsTripleWithin_seq_same_cr h0 h1
  have h012 := cpsTripleWithin_seq_same_cr h01 h2
  have h0123 := cpsTripleWithin_seq_same_cr h012 h3
  have h01234 := cpsTripleWithin_seq_same_cr h0123 h4
  exact cpsTripleWithin_seq_same_cr h01234 h5

#print axioms extractType234ToWn0Ok_owned_of_decode
#print axioms extractWalkNext0to1Ok_owned_of_decode
#print axioms extractType234ToWn5Ok_owned_of_decode

end EvmAsm.Codegen.TxExtractToAddressSpec
