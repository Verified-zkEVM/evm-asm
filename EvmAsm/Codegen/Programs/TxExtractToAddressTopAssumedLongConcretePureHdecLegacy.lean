/-
  Discharge packaging hdec0..3 via unified long-list rlpItemDecode (legacy).
  Residual: hvalid*/hvalid1_*/hlover/hlvalid (RAM).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedLongConcretePureLegacy
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitLong

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps fullCode extractLinked_mono)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)
open EvmAsm.Codegen.TxExtractToAddressHonesty
open EvmAsm.Codegen.TxExtractToAddressModel
open EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_longConcrete_pureHdec_legacy
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
    (htype0 : (teerTxTypeDispatch txBytes).2.1 = (0 : Word))
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hlong : 55 < (encode.encodeItems items).length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidTx0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true)
    (hinover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) = true)
    (hlover : txBase.toNat + ((teerTxTypeDispatch txBytes).2.2.toNat + 1 +
      longListLol items) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < longListLol items →
      isValidByteAccess (txBase + BitVec.ofNat 64
        ((teerTxTypeDispatch txBytes).2.2.toNat + 1 + k)) = true)
    (hitem0 : (encode (items[0]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0)) = true)
    (hvalid1_0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0 + 1)) = true)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1)) = true)
    (hvalid1_1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1 + 1)) = true)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2)) = true)
    (hvalid1_2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2 + 1)) = true)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3)) = true)
    (hvalid1_3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3 + 1)) = true)
    (hge5 : 5 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) := by
  let listOff := (teerTxTypeDispatch txBytes).2.2.toNat
  have hlenW : lenW.toNat = txBytes.length := by
    have hspan : txBytes.length < 2 ^ 64 := by omega
    rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspan]
  have hencInner :
      txBytes.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ hdecL
  have hlenItems :=
    extractSuccess_creation_legacy_items_length_long txBytes hsuccess hcreFlag htype0
      items hdecL hlong
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hhoff :=
    extractSuccess_creation_legacy_hoff_srcOff_long txBytes hsuccess hcreFlag htype0
      items hdecL hlong
  have hendEq :
      longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2) listOff =
        longListEndPtr txBase listOff items := by
    simpa [longWalkEnd, listOff] using
      (longWalkEnd_eq_longListEndPtr txBase lenW txBytes items hsuccess hlenW
        hdecL hlong hover)
  have hoverEnd : txBase.toNat +
      (listOff + 1 + longListLol items + (encode.encodeItems items).length) < 2 ^ 64 := by
    have hdrop : (txBytes.drop listOff).length = txBytes.length - listOff := by
      simp [List.length_drop]
    have hencLen := encode_list_long_length items hlong
    have hdropEq : (txBytes.drop listOff).length = (encode (.list items)).length := by
      rw [hencInner]
    have hpay : longListPayloadLen items = (encode.encodeItems items).length := rfl
    omega
  have hdec0 :=
    hdec_long_list_end txBytes txBase listOff items 0 hencInner hlong hn0 hitem0
      hhoff.1 hoverEnd _ hendEq
  have hdec1 :=
    hdec_long_list_end txBytes txBase listOff items 1 hencInner hlong hn1 hitem1
      hhoff.2.1 hoverEnd _ hendEq
  have hdec2 :=
    hdec_long_list_end txBytes txBase listOff items 2 hencInner hlong hn2 hitem2
      hhoff.2.2.1 hoverEnd _ hendEq
  have hdec3 :=
    hdec_long_list_end txBytes txBase listOff items 3 hencInner hlong hn3 hitem3
      hhoff.2.2.2 hoverEnd _ hendEq
  exact extractAssumed_creation_longConcrete_pure_legacy
    sp0 spC s txBase lenW toBuf isCreationPtr txBytes items
    hspC hret htalign htover htvalid hlen hsuccess hcreFlag htype0 hdecL hlong
    halign hover hvalidTx0 hinover hinvalid hlover hlvalid
    hitem0 hvalid0 hvalid1_0 hdec0
    hitem1 hvalid1 hvalid1_1 hdec1
    hitem2 hvalid2 hvalid1_2 hdec2
    hitem3 hvalid3 hvalid1_3 hdec3
    hge5

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_longConcrete_pureHdec_legacy_fullCode
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
    (htype0 : (teerTxTypeDispatch txBytes).2.1 = (0 : Word))
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hlong : 55 < (encode.encodeItems items).length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidTx0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true)
    (hinover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) = true)
    (hlover : txBase.toNat + ((teerTxTypeDispatch txBytes).2.2.toNat + 1 +
      longListLol items) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < longListLol items →
      isValidByteAccess (txBase + BitVec.ofNat 64
        ((teerTxTypeDispatch txBytes).2.2.toNat + 1 + k)) = true)
    (hitem0 : (encode (items[0]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0)) = true)
    (hvalid1_0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0 + 1)) = true)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1)) = true)
    (hvalid1_1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1 + 1)) = true)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2)) = true)
    (hvalid1_2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2 + 1)) = true)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3)) = true)
    (hvalid1_3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3 + 1)) = true)
    (hge5 : 5 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_creation_longConcrete_pureHdec_legacy sp0 spC s
      txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag htype0 hdecL hlong
      halign hover hvalidTx0 hinover hinvalid hlover hlvalid
      hitem0 hvalid0 hvalid1_0
      hitem1 hvalid1 hvalid1_1
      hitem2 hvalid2 hvalid1_2
      hitem3 hvalid3 hvalid1_3
      hge5)

#print axioms extractAssumed_creation_longConcrete_pureHdec_legacy
#print axioms extractAssumed_creation_longConcrete_pureHdec_legacy_fullCode

end EvmAsm.Codegen.TxExtractToAddressSpec
