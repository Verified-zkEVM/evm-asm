/-
  Mid-seq chain: type234 AfterSave → AfterWalkNext0Bne under midOwned.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidSeq
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidSeqRest
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)

set_option maxRecDepth 8000 in
/-- type234 AfterSave → AfterWalkNext0Bne under midOwned.
    Requires cursor identity `cursor = txBase + srcOff0` and drop-fail `hok0`. -/
theorem extractType234ToWn0Ok_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat)
    (hcur : cursor = txBase + BitVec.ofNat 64 srcOff0)
    (hne0 : typeW ≠ 0) (hne1 : typeW ≠ 1)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff0 < txBytes.length)
    (hover : txBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff0) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff0]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff0]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < txBytes.length ∧ txBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff0]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff0]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((txBytes[srcOff0]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff0 + 1 +
          ((txBytes[srcOff0]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff0]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff0]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((txBytes[srcOff0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff0 + 1 +
          ((txBytes[srcOff0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hok0 : ∀ (h : PartialState),
      wn0OkFail txBase endPtr txBytes srcOff0 h →
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff0) endPtr txBytes srcOff0 h) :
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
  have hOk := extractWalkNext0CallOk_owned spC s txBase lenW typeW innerW endPtr
    toBuf isCreationPtr s7 txBytes srcOff0
    hsalign hoff hover hvalid hss hls hll hok0
  exact cpsTripleWithin_seq_same_cr hBr2 hOk

set_option maxRecDepth 8000 in
/-- AfterWalkNext0Bne → AfterWalkNext1Bne under midOwned via PrepCallOk.
    Needs `hnext : next0 = txBase + srcOff1` (cursor identity after wn0). -/
theorem extractWalkNext0to1Ok_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next0 len0 toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 srcOff1 : Nat)
    (hnext : next0 = txBase + BitVec.ofNat 64 srcOff1)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff1 < txBytes.length)
    (hover : txBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff1) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff1]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff1]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < txBytes.length ∧ txBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff1]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff1]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff1 + 1 +
          ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff1]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff1 + 1 +
          ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hok1 : ∀ (h : PartialState),
      wn0OkFail txBase endPtr txBytes srcOff1 h →
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff1) endPtr txBytes srcOff1 h) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterWalkNext0Bne AfterWalkNext1Bne extractLinkedCode
      (wn0OkConcrete txBase lenW typeW innerW endPtr next0 len0
          txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next1 len1 : Word,
        (wn1OkConcrete txBase lenW typeW innerW endPtr next1 len1
          txBytes srcOff1 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractWalkNext1PrepCallOk_owned spC s txBase lenW typeW innerW endPtr
    next0 len0 toBuf isCreationPtr s7 txBytes srcOff0 srcOff1
    hnext hsalign hoff hover hvalid hss hls hll hok1

set_option maxRecDepth 8000 in
/-- type234 AfterSave → AfterWalkNext1Bne under midOwned.
    Nested exists + pure cursor identity after wn0. -/
theorem extractType234ToWn1Ok_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 srcOff1 : Nat)
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
    (hok0 : ∀ (h : PartialState),
      wn0OkFail txBase endPtr txBytes srcOff0 h →
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff0) endPtr txBytes srcOff0 h)
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
    (hok1 : ∀ (h : PartialState),
      wn0OkFail txBase endPtr txBytes srcOff1 h →
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff1) endPtr txBytes srcOff1 h)
    (hnext1 : ∀ (next0 : Word) (_len0 : Word),
      next0 = txBase + BitVec.ofNat 64 srcOff1) :
    cpsTripleWithin
      ((((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1))
      AfterSaveCursor AfterWalkNext1Bne extractLinkedCode
      (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next1 len1 : Word,
        (wn1OkConcrete txBase lenW typeW innerW endPtr next1 len1
          txBytes srcOff1 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h0 := extractType234ToWn0Ok_owned spC s txBase lenW typeW innerW
    cursor endPtr toBuf isCreationPtr s7 txBytes srcOff0
    hcur hne0 hne1 hsalign hoff0 hover0 hvalid0 hss0 hls0 hll0 hok0
  -- second leg: ∃ next0 len0 pre → AfterWalkNext1
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
    exact extractWalkNext0to1Ok_owned spC s txBase lenW typeW innerW endPtr
      next0 len0 toBuf isCreationPtr s7 txBytes srcOff0 srcOff1
      (hnext1 next0 len0) hsalign hoff1 hover1 hvalid1 hss1 hls1 hll1 hok1
  exact cpsTripleWithin_seq_same_cr h0 h1

#print axioms extractType234ToWn0Ok_owned
#print axioms extractWalkNext0to1Ok_owned
#print axioms extractType234ToWn1Ok_owned

end EvmAsm.Codegen.TxExtractToAddressSpec
