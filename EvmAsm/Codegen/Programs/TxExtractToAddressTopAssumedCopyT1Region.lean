/-
  Assumed bare packaging for t1 short 20B copy region path.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumed
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressCopyFromRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontE2ECopyShortConcreteT1Region
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps nTypeSteps nExtractStackDwords extractToBufOwn teaScratchOwn
    fullCode extractLinked_mono)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)
open EvmAsm.Rv64.RLP (rlpItemDecode)

theorem nFrontCopyStepsShortT1Region_le_nExtract :
    nFrontCopyStepsShortT1Region ≤ nExtractSteps := by
  simp only [nFrontCopyStepsShortT1Region, nExtractSteps, nTypeSteps]
  omega

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_of_front_short_concrete_t1_region
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 q : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcur : shortWalkCursor txBase (teerTxTypeDispatch txBytes).2.2.toNat =
        txBase + BitVec.ofNat 64 srcOff0)
    (htype1 : (teerTxTypeDispatch txBytes).2.1 = (1 : Word))
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
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next0 len0)
    (hinb0 :
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff0)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) = true)
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
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next1 len1)
    (hinb1 :
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff1)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) = true)
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
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next2 len2)
    (hinb2 :
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff2)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) = true)
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
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next3 len3)
    (hinb3 :
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff3)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) = true)
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
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next4 len4)
    (hinb4 :
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff4)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) = true)

    (hnext1 : ∀ (next0 len0 : Word),
      rlpItemDecode txBytes srcOff0 (txBase + BitVec.ofNat 64 srcOff0)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next0 len0 →
      next0 = txBase + BitVec.ofNat 64 srcOff1)
    (hnext2 : ∀ (next1 len1 : Word),
      rlpItemDecode txBytes srcOff1 (txBase + BitVec.ofNat 64 srcOff1)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next1 len1 →
      next1 = txBase + BitVec.ofNat 64 srcOff2)
    (hnext3 : ∀ (next2 len2 : Word),
      rlpItemDecode txBytes srcOff2 (txBase + BitVec.ofNat 64 srcOff2)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next2 len2 →
      next2 = txBase + BitVec.ofNat 64 srcOff3)
    (hnext4 : ∀ (next3 len3 : Word),
      rlpItemDecode txBytes srcOff3 (txBase + BitVec.ofNat 64 srcOff3)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next3 len3 →
      next3 = txBase + BitVec.ofNat 64 srcOff4)
    (hlen20 : ∀ (next4 len4 : Word),
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next4 len4 → len4 = (20 : Word))
    (hnext_content : ∀ (next4 len4 : Word),
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next4 len4 →
        next4 = txBase + BitVec.ofNat 64 (8 * q) + (20 : Word))
    (hq : 8 * q + 16 < txBytes.length)
    (hcover : txBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (txBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
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
        (lenW - (teerTxTypeDispatch txBytes).2.2)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) := by
  let contentPtr := txBase + BitVec.ofNat 64 (8 * q)
  let w2 := (contentWordsAt txBytes q).2.2
  have hE2E : ∀ (old5 old6 old7 old14 old15 old16 : Word),
      cpsTripleWithin nFrontCopyStepsShortT1Region E s.ra extractLinkedCode
        (creationE2EPre sp0 spC s txBase lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 txBytes)
        (copyE2EPostRegion sp0 s txBase toBuf isCreationPtr contentPtr w2
          txBytes) := by
    intro old5 old6 old7 old14 old15 old16
    have h := extractFrontCopy_then_epi_of_decode_short_concrete_t1_region
      sp0 spC s txBase lenW toBuf isCreationPtr txBytes
      srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 q
      hspC hret hcur htype1 hsalign
      hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
      hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
      hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
      hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
      hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
      hnext1 hnext2 hnext3 hnext4 hlen20 hnext_content
      hq hcover hcvalid htalign htover htvalid
      hlen hsuccess hover hvalidTx0 hoff hinover hinvalid
      hlistLen_ne h_ge h_hi h_exact
      old5 old6 old7 old14 old15 old16
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [creationE2EPre] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp only [contentPtr, w2, copyE2EPostRegion] at hq ⊢
      xperm_hyp hq) h
  -- reuse type234 temps peel with mono from Legacy nSteps
  have htemps := extractAssumed_copy_temps_region sp0 spC s txBase lenW
    toBuf isCreationPtr contentPtr w2 txBytes hspC ?_
  · exact htemps
  · intro old5 old6 old7 old14 old15 old16
    have h0 := hE2E old5 old6 old7 old14 old15 old16
    -- need nFrontCopyStepsShortRegion not Legacy - use mono via le
    have hle : nFrontCopyStepsShortT1Region ≤ nFrontCopyStepsShortRegion := by
      simp only [nFrontCopyStepsShortT1Region, nFrontCopyStepsShortRegion, nTypeSteps]
      omega
    have h1 := cpsTripleWithin_mono_nSteps hle h0
    exact h1

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_fullCode_of_decode_short_concrete_t1_region
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 q : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcur : shortWalkCursor txBase (teerTxTypeDispatch txBytes).2.2.toNat =
        txBase + BitVec.ofNat 64 srcOff0)
    (htype1 : (teerTxTypeDispatch txBytes).2.1 = (1 : Word))
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
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next0 len0)
    (hinb0 :
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff0)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) = true)
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
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next1 len1)
    (hinb1 :
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff1)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) = true)
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
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next2 len2)
    (hinb2 :
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff2)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) = true)
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
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next3 len3)
    (hinb3 :
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff3)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) = true)
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
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next4 len4)
    (hinb4 :
      BitVec.ult (txBase + BitVec.ofNat 64 srcOff4)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) = true)

    (hnext1 : ∀ (next0 len0 : Word),
      rlpItemDecode txBytes srcOff0 (txBase + BitVec.ofNat 64 srcOff0)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next0 len0 →
      next0 = txBase + BitVec.ofNat 64 srcOff1)
    (hnext2 : ∀ (next1 len1 : Word),
      rlpItemDecode txBytes srcOff1 (txBase + BitVec.ofNat 64 srcOff1)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next1 len1 →
      next1 = txBase + BitVec.ofNat 64 srcOff2)
    (hnext3 : ∀ (next2 len2 : Word),
      rlpItemDecode txBytes srcOff2 (txBase + BitVec.ofNat 64 srcOff2)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next2 len2 →
      next2 = txBase + BitVec.ofNat 64 srcOff3)
    (hnext4 : ∀ (next3 len3 : Word),
      rlpItemDecode txBytes srcOff3 (txBase + BitVec.ofNat 64 srcOff3)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next3 len3 →
      next3 = txBase + BitVec.ofNat 64 srcOff4)
    (hlen20 : ∀ (next4 len4 : Word),
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next4 len4 → len4 = (20 : Word))
    (hnext_content : ∀ (next4 len4 : Word),
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4)
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next4 len4 →
        next4 = txBase + BitVec.ofNat 64 (8 * q) + (20 : Word))
    (hq : 8 * q + 16 < txBytes.length)
    (hcover : txBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (txBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
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
        (lenW - (teerTxTypeDispatch txBytes).2.2)) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_copy_of_front_short_concrete_t1_region sp0 spC s
      txBase lenW toBuf isCreationPtr txBytes
      srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 q
      hspC hret hcur htype1 hsalign
      hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
      hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
      hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
      hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
      hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
      hnext1 hnext2 hnext3 hnext4 hlen20 hnext_content
      hq hcover hcvalid htalign htover htvalid
      hlen hsuccess hover hvalidTx0 hoff hinover hinvalid
      hlistLen_ne h_ge h_hi h_exact)

#print axioms extractAssumed_copy_of_front_short_concrete_t1_region
#print axioms extractAssumed_copy_fullCode_of_decode_short_concrete_t1_region

end EvmAsm.Codegen.TxExtractToAddressSpec
