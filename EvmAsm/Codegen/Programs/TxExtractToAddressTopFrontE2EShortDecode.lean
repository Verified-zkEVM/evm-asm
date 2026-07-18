/-
  Front E → AfterSave short walk_init → type234 creation → ret of_decode (no hdrop/hok).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontCreDecode
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontE2E
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNext0
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords nTypeSteps)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)

/-- Short-path E2E steps: walk_init uses 15 not 81. -/
def nFrontCreationStepsShort : Nat :=
  (((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8)) + ((1 + 15) + (1 + (1 + 1)))) +
    (((((((((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        ((1 + 1) + ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)))

set_option maxRecDepth 8000 in
/-- E → ret type234 creation short+of_decode. No hdrop. -/
theorem extractFrontCreation_then_epi_of_decode_short
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (txBytes : List (BitVec 8))
    (srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 srcOff5 : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidTx0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true)
    (hoff : (teerTxTypeDispatch txBytes).2.2.toNat < txBytes.length)
    (hinover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) = true)
    (hlistLen_ne : (lenW - (teerTxTypeDispatch txBytes).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_hi : BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true)
    (h_exact : (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
        (((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
          (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) =
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
        (lenW - (teerTxTypeDispatch txBytes).2.2))
    (hcur : ∀ (cursor _endPtr : Word), cursor = txBase + BitVec.ofNat 64 srcOff0)
    (hne0 : (teerTxTypeDispatch txBytes).2.1 ≠ 0)
    (hne1 : (teerTxTypeDispatch txBytes).2.1 ≠ 1)
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
    (hdec0 : ∀ (endPtr : Word), ∃ next0 len0 : Word,
      rlpItemDecode txBytes srcOff0 (txBase + BitVec.ofNat 64 srcOff0)
        endPtr next0 len0)
    (hinb0 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff0) endPtr = true)
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
    (hdec1 : ∀ (endPtr : Word), ∃ next1 len1 : Word,
      rlpItemDecode txBytes srcOff1 (txBase + BitVec.ofNat 64 srcOff1)
        endPtr next1 len1)
    (hinb1 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff1) endPtr = true)
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
    (hdec2 : ∀ (endPtr : Word), ∃ next2 len2 : Word,
      rlpItemDecode txBytes srcOff2 (txBase + BitVec.ofNat 64 srcOff2)
        endPtr next2 len2)
    (hinb2 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff2) endPtr = true)
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
    (hdec3 : ∀ (endPtr : Word), ∃ next3 len3 : Word,
      rlpItemDecode txBytes srcOff3 (txBase + BitVec.ofNat 64 srcOff3)
        endPtr next3 len3)
    (hinb3 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff3) endPtr = true)
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
    (hdec4 : ∀ (endPtr : Word), ∃ next4 len4 : Word,
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4)
        endPtr next4 len4)
    (hinb4 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff4) endPtr = true)
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
    (hdec5 : ∀ (endPtr : Word), ∃ next5 len5 : Word,
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5)
        endPtr next5 len5)
    (hinb5 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff5) endPtr = true)
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
    (hcre : ∀ (endPtr next5 len5 : Word),
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5)
        endPtr next5 len5 → len5 = (0 : Word)) :
    cpsTripleWithin nFrontCreationStepsShort
      E s.ra extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest txBase lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr **
        frontExtraAmbient txBase txBytes)
      (fun h => ∃ next5 : Word,
        ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
          stackFree sp0 nExtractStackDwords **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes **
          extractToBufOwn toBuf **
          (isCreationPtr ↦ₘ (1 : Word)) **
          (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
          (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
          (Reg.x23 ↦ᵣ s.s7) **
          (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          (.x31 ↦ᵣ (next5 - (0 : Word))) **
          creExtraTemps) h) := by
  have hF := extractFrontToAfterSave_short sp0 spC s txBase lenW toBuf isCreationPtr
    old5 old6 old7 old14 old15 old16 txBytes
    hspC htalign htover htvalid hlen hsuccess halign hover hvalidTx0
    hoff hinover hinvalid hlistLen_ne h_ge h_hi h_exact
  have hC := extractFrontAfterSaveCreation_then_epi_of_decode sp0 spC s
    txBase lenW toBuf isCreationPtr txBytes
    srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 srcOff5
    hspC hret hcur hne0 hne1 halign
    hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
    hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hnext1 hnext2 hnext3 hnext4 hnext5 hcre
  exact cpsTripleWithin_seq_same_cr hF hC

#print axioms extractFrontCreation_then_epi_of_decode_short

end EvmAsm.Codegen.TxExtractToAddressSpec
