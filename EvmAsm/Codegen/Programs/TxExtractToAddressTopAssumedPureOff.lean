/-
  Assumed creation with pure hoff/hover discharged under shortListSrcOff.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedSrcOff
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps fullCode extractLinked_mono)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)
open EvmAsm.Codegen.TxExtractToAddressHonesty
open EvmAsm.Codegen.TxExtractToAddressModel
open EvmAsm.Rv64.RLP (rlpItemDecode)
open EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
/-- Assumed creation shortListSrcOff with hoff0..5 + hover0..5 pure-discharged. -/
theorem extractAssumed_creation_shortListSrcOff_pureOff
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
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
    (hcur : ∀ (cursor _endPtr : Word),
      cursor = txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0))
    (hne0 : (teerTxTypeDispatch txBytes).2.1 ≠ 0)
    (hne1 : (teerTxTypeDispatch txBytes).2.1 ≠ 1)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)) = true)
    (hss0 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1)) = true)
    (hls0 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 + kk)) = true)
    (hll0 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 + kk)) = true)
    (hdec0 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)) endPtr n l)
    (hinb0 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)) endPtr = true)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) = true)
    (hss1 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1)) = true)
    (hls1 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 + kk)) = true)
    (hll1 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 + kk)) = true)
    (hdec1 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) endPtr n l)
    (hinb1 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) endPtr = true)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) = true)
    (hss2 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1)) = true)
    (hls2 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 + kk)) = true)
    (hll2 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 + kk)) = true)
    (hdec2 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) endPtr n l)
    (hinb2 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) endPtr = true)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) = true)
    (hss3 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1)) = true)
    (hls3 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 + kk)) = true)
    (hll3 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 + kk)) = true)
    (hdec3 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) endPtr n l)
    (hinb3 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) endPtr = true)
    (hvalid4 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) = true)
    (hss4 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1)) = true)
    (hls4 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 + kk)) = true)
    (hll4 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 + kk)) = true)
    (hdec4 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) endPtr n l)
    (hinb4 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) endPtr = true)
    (hvalid5 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) = true)
    (hss5 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1)) = true)
    (hls5 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 + kk)) = true)
    (hll5 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 + kk)) = true)
    (hdec5 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) endPtr n l)
    (hinb5 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) endPtr = true) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) :=
  extractAssumed_creation_shortListSrcOff
    sp0 spC s txBase lenW toBuf isCreationPtr txBytes items
    hspC hret htalign htover htvalid hlen hsuccess hcreFlag hge hdecL hshort
    halign hover hvalidTx0 hoff hinover hinvalid hlistLen_ne h_ge h_hi h_exact
    hcur hne0 hne1
    (extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1 (extractSuccess_creation_type234_hover_srcOff txBytes txBase hsuccess hcreFlag hge items hdecL hshort hover).1 hvalid0 hss0 hls0 hll0 hdec0 hinb0
      (extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1 (extractSuccess_creation_type234_hover_srcOff txBytes txBase hsuccess hcreFlag hge items hdecL hshort hover).2.1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
      (extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1 (extractSuccess_creation_type234_hover_srcOff txBytes txBase hsuccess hcreFlag hge items hdecL hshort hover).2.2.1 hvalid2 hss2 hls2 hll2 hdec2 hinb2
      (extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1 (extractSuccess_creation_type234_hover_srcOff txBytes txBase hsuccess hcreFlag hge items hdecL hshort hover).2.2.2.1 hvalid3 hss3 hls3 hll3 hdec3 hinb3
      (extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1 (extractSuccess_creation_type234_hover_srcOff txBytes txBase hsuccess hcreFlag hge items hdecL hshort hover).2.2.2.2.1 hvalid4 hss4 hls4 hll4 hdec4 hinb4
      (extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2 (extractSuccess_creation_type234_hover_srcOff txBytes txBase hsuccess hcreFlag hge items hdecL hshort hover).2.2.2.2.2 hvalid5 hss5 hls5 hll5 hdec5 hinb5

set_option maxRecDepth 8000 in
/-- Same under intrinsic `fullCode`. -/
theorem extractAssumed_creation_shortListSrcOff_pureOff_fullCode
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
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
    (hcur : ∀ (cursor _endPtr : Word),
      cursor = txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0))
    (hne0 : (teerTxTypeDispatch txBytes).2.1 ≠ 0)
    (hne1 : (teerTxTypeDispatch txBytes).2.1 ≠ 1)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)) = true)
    (hss0 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1)) = true)
    (hls0 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 + kk)) = true)
    (hll0 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).1)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) + 1 + kk)) = true)
    (hdec0 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)) endPtr n l)
    (hinb0 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)) endPtr = true)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) = true)
    (hss1 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1)) = true)
    (hls1 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 + kk)) = true)
    (hll1 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.1)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) + 1 + kk)) = true)
    (hdec1 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) endPtr n l)
    (hinb1 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) endPtr = true)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) = true)
    (hss2 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1)) = true)
    (hls2 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 + kk)) = true)
    (hll2 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) + 1 + kk)) = true)
    (hdec2 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) endPtr n l)
    (hinb2 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) endPtr = true)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) = true)
    (hss3 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1)) = true)
    (hls3 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 + kk)) = true)
    (hll3 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) + 1 + kk)) = true)
    (hdec3 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) endPtr n l)
    (hinb3 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) endPtr = true)
    (hvalid4 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) = true)
    (hss4 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1)) = true)
    (hls4 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 + kk)) = true)
    (hll4 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.1)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) + 1 + kk)) = true)
    (hdec4 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) endPtr n l)
    (hinb4 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) endPtr = true)
    (hvalid5 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) = true)
    (hss5 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64) (0xb8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 < txBytes.length ∧ txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1)) = true)
    (hls5 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64) (0xc0 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 + kk)) = true)
    (hll5 : ¬ BitVec.ult ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64) (0xf8 : Word) = true →
        (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 + ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 +
          ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[(shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)]'((extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge items hdecL hshort).2.2.2.2.2)).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 ((shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) + 1 + kk)) = true)
    (hdec5 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) endPtr n l)
    (hinb5 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) endPtr = true) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_creation_shortListSrcOff_pureOff sp0 spC s txBase lenW toBuf
      isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag hge hdecL hshort
      halign hover hvalidTx0 hoff hinover hinvalid hlistLen_ne h_ge h_hi h_exact
      hcur hne0 hne1
      hvalid0 hss0 hls0 hll0 hdec0 hinb0 hvalid1 hss1 hls1 hll1 hdec1 hinb1 hvalid2 hss2 hls2 hll2 hdec2 hinb2 hvalid3 hss3 hls3 hll3 hdec3 hinb3 hvalid4 hss4 hls4 hll4 hdec4 hinb4 hvalid5 hss5 hls5 hll5 hdec5 hinb5)

#print axioms extractAssumed_creation_shortListSrcOff_pureOff
#print axioms extractAssumed_creation_shortListSrcOff_pureOff_fullCode

end EvmAsm.Codegen.TxExtractToAddressSpec
