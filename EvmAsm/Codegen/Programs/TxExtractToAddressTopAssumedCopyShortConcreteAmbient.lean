/-
  Ambient dual: Assumed packaging under short concrete copy region of_decode
  (honesty residuals still free hyps).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontE2ECopyShortConcreteAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressCopyFromRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitShort
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps nTypeSteps nExtractStackDwords extractToBufOwn teaScratchOwn
    fullCode extractLinked_mono)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch txSlice ambientAbsOff)
open EvmAsm.Rv64.RLP (rlpWalkNextOk rlpItemDecode)

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_under_honesty_of_decode_short_concrete_region_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (absOff0 absOff1 absOff2 absOff3 absOff4 absOff5 q : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcur : shortWalkCursor regionBase
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) =
        regionBase + BitVec.ofNat 64 absOff0)
    (hne0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 ≠ 0)
    (hne1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 ≠ 1)
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff0 : absOff0 < bs.length)
    (hover0 : regionBase.toNat + absOff0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        absOff0 + 1 < bs.length ∧ regionBase.toNat + (absOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + k)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next0 len0)
    (hinb0 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff0)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff1 : absOff1 < bs.length)
    (hover1 : regionBase.toNat + absOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        absOff1 + 1 < bs.length ∧ regionBase.toNat + (absOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next1 len1)
    (hinb1 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff1)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff2 : absOff2 < bs.length)
    (hover2 : regionBase.toNat + absOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        absOff2 + 1 < bs.length ∧ regionBase.toNat + (absOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + k)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next2 len2)
    (hinb2 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff2)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff3 : absOff3 < bs.length)
    (hover3 : regionBase.toNat + absOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        absOff3 + 1 < bs.length ∧ regionBase.toNat + (absOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + k)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next3 len3)
    (hinb3 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff3)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff4 : absOff4 < bs.length)
    (hover4 : regionBase.toNat + absOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        absOff4 + 1 < bs.length ∧ regionBase.toNat + (absOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + k)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next4 len4)
    (hinb4 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff4)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff5 : absOff5 < bs.length)
    (hover5 : regionBase.toNat + absOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        absOff5 + 1 < bs.length ∧ regionBase.toNat + (absOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        absOff5 + 1 + ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff5 + 1 +
          ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        absOff5 + 1 + ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff5 + 1 +
          ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff5 + 1 + k)) = true)
    (hdec5 : ∃ next5 len5 : Word,
      rlpItemDecode bs absOff5 (regionBase + BitVec.ofNat 64 absOff5)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next5 len5)
    (hinb5 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff5)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hnext1 : ∀ (next0 len0 : Word),
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 absOff1)
    (hnext2 : ∀ (next1 len1 : Word),
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 absOff2)
    (hnext3 : ∀ (next2 len2 : Word),
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 absOff3)
    (hnext4 : ∀ (next3 len3 : Word),
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 absOff4)
    (hnext5 : ∀ (next4 len4 : Word),
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 absOff5)
    (hlen20 : ∀ (next5 len5 : Word),
      rlpItemDecode bs absOff5 (regionBase + BitVec.ofNat 64 absOff5)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next5 len5 →
        len5 = (20 : Word))
    (hnext_content : ∀ (next5 len5 : Word),
      rlpItemDecode bs absOff5 (regionBase + BitVec.ofNat 64 absOff5)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next5 len5 →
        next5 = regionBase + BitVec.ofNat 64 (8 * q) + (20 : Word))
    (hq : 8 * q + 16 < bs.length)
    (hcover : regionBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true) 
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidTx0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (hoff : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < bs.length)
    (hinover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hspan : regionBase.toNat +
        (off + (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) < 2 ^ 64)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hlistLen_ne : (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_hi : BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
        (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
            ).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) := by
  let contentPtr := regionBase + BitVec.ofNat 64 (8 * q)
  let w2 := (contentWordsAt bs q).2.2
  refine extractAssumed_copy_of_front_ambient sp0 spC s regionBase loadPtr
    lenW toBuf isCreationPtr contentPtr w2 bs off len hspC ?_
  intro old5 old6 old7 old14 old15 old16
  have hShort := extractFrontCopy_then_epi_of_decode_short_concrete_region_ambient
    sp0 spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len
    absOff0 absOff1 absOff2 absOff3 absOff4 absOff5 q
    hspC hret hcur hne0 hne1 hsalign
    hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
    hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hnext1 hnext2 hnext3 hnext4 hnext5 hlen20 hnext_content
    hq hcover hcvalid
    htalign htover htvalid hlen hsuccess hover hvalidTx0
    hoff hinover hinvalid hspan hptr hbound hlistLen_ne h_ge h_hi h_exact
    old5 old6 old7 old14 old15 old16
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    dsimp only [copyE2EPostAmbient, contentPtr, w2] at hq ⊢
    xperm_hyp hq) hShort

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_fullCode_of_decode_short_concrete_region_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (absOff0 absOff1 absOff2 absOff3 absOff4 absOff5 q : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcur : shortWalkCursor regionBase
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) =
        regionBase + BitVec.ofNat 64 absOff0)
    (hne0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 ≠ 0)
    (hne1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 ≠ 1)
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff0 : absOff0 < bs.length)
    (hover0 : regionBase.toNat + absOff0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        absOff0 + 1 < bs.length ∧ regionBase.toNat + (absOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + k)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next0 len0)
    (hinb0 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff0)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff1 : absOff1 < bs.length)
    (hover1 : regionBase.toNat + absOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        absOff1 + 1 < bs.length ∧ regionBase.toNat + (absOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next1 len1)
    (hinb1 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff1)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff2 : absOff2 < bs.length)
    (hover2 : regionBase.toNat + absOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        absOff2 + 1 < bs.length ∧ regionBase.toNat + (absOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + k)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next2 len2)
    (hinb2 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff2)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff3 : absOff3 < bs.length)
    (hover3 : regionBase.toNat + absOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        absOff3 + 1 < bs.length ∧ regionBase.toNat + (absOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + k)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next3 len3)
    (hinb3 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff3)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff4 : absOff4 < bs.length)
    (hover4 : regionBase.toNat + absOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        absOff4 + 1 < bs.length ∧ regionBase.toNat + (absOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + k)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next4 len4)
    (hinb4 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff4)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff5 : absOff5 < bs.length)
    (hover5 : regionBase.toNat + absOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        absOff5 + 1 < bs.length ∧ regionBase.toNat + (absOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        absOff5 + 1 + ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff5 + 1 +
          ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        absOff5 + 1 + ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff5 + 1 +
          ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff5 + 1 + k)) = true)
    (hdec5 : ∃ next5 len5 : Word,
      rlpItemDecode bs absOff5 (regionBase + BitVec.ofNat 64 absOff5)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next5 len5)
    (hinb5 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff5)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hnext1 : ∀ (next0 len0 : Word),
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 absOff1)
    (hnext2 : ∀ (next1 len1 : Word),
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 absOff2)
    (hnext3 : ∀ (next2 len2 : Word),
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 absOff3)
    (hnext4 : ∀ (next3 len3 : Word),
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 absOff4)
    (hnext5 : ∀ (next4 len4 : Word),
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 absOff5)
    (hlen20 : ∀ (next5 len5 : Word),
      rlpItemDecode bs absOff5 (regionBase + BitVec.ofNat 64 absOff5)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next5 len5 →
        len5 = (20 : Word))
    (hnext_content : ∀ (next5 len5 : Word),
      rlpItemDecode bs absOff5 (regionBase + BitVec.ofNat 64 absOff5)
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next5 len5 →
        next5 = regionBase + BitVec.ofNat 64 (8 * q) + (20 : Word))
    (hq : 8 * q + 16 < bs.length)
    (hcover : regionBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true) 
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidTx0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (hoff : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < bs.length)
    (hinover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hspan : regionBase.toNat +
        (off + (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) < 2 ^ 64)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hlistLen_ne : (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_hi : BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
        (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
            ).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_copy_under_honesty_of_decode_short_concrete_region_ambient
      sp0 spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len
      absOff0 absOff1 absOff2 absOff3 absOff4 absOff5 q
      hspC hret hcur hne0 hne1 hsalign
    hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
    hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hnext1 hnext2 hnext3 hnext4 hnext5 hlen20 hnext_content
    hq hcover hcvalid
    htalign htover htvalid hlen hsuccess hover hvalidTx0
    hoff hinover hinvalid hspan hptr hbound hlistLen_ne h_ge h_hi h_exact)

#print axioms extractAssumed_copy_under_honesty_of_decode_short_concrete_region_ambient
#print axioms extractAssumed_copy_fullCode_of_decode_short_concrete_region_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
