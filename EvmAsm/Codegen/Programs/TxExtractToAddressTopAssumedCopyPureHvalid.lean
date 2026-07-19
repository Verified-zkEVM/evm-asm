/-
  Copy Assumed short concrete: discharge hdec* + hvalid* via pure + validByteRange.
  Residual path: copy/type234/short/hdecL/hge7 + content statics.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPure
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitShort
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidJoin

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
/-- Short concrete Assumed copy; hdec* + hvalid* discharged.
    Residual: content statics + path flags. -/
theorem extractAssumed_copy_shortConcrete_pureHvalid
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr contentPtr w0 w1 w2 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hcalign : contentPtr.toNat % 8 = 0)
    (hcover : contentPtr.toNat + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess (contentPtr + (16 : Word)) = true)
    (hcontent : contentPtr =
      txBase + BitVec.ofNat 64
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5) +
        (1 : Word))
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : extractSuccess txBytes)
    (hcopyFlag : (teerExtractToAddress txBytes).2.2 = (0 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes **
        contentDwords contentPtr w0 w1 w2)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes **
        contentDwords contentPtr w0 w1 w2) := by
  let listOff := (teerTxTypeDispatch txBytes).2.2.toNat
  have hlenW : lenW.toNat = txBytes.length := by
    have hspan : txBytes.length < 2 ^ 64 := by omega
    rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspan]
  have hencInner :
      txBytes.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ hdecL
  have hlenItems :=
    extractSuccess_copy_type234_items_length txBytes hsuccess hcopyFlag hge
      items hdecL hshort
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hn4 : (4 : Nat) < items.length := by omega
  have hn5 : (5 : Nat) < items.length := by omega
  have hhoff :=
    extractSuccess_copy_type234_hoff_srcOff txBytes hsuccess hcopyFlag hge
      items hdecL hshort
  have hendEq :
      shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2) listOff =
        shortListEndPtr txBase listOff items := by
    simpa [shortWalkEnd, listOff] using
      (shortWalkEnd_eq_shortListEndPtr txBase lenW txBytes items hsuccess hlenW
        hdecL hshort hover)
  have hoverEnd : txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64 := by
    have hdrop : (txBytes.drop listOff).length = txBytes.length - listOff := by
      simp [List.length_drop]
    have hencLen := encode_list_short_length items hshort
    have hdropEq : (txBytes.drop listOff).length = (encode (.list items)).length := by
      rw [hencInner]
    omega
  have hdec0 :=
    hdec_short_list_end txBytes txBase listOff items 0 hencInner hshort hn0
      hhoff.1 hoverEnd _ hendEq
  have hdec1 :=
    hdec_short_list_end txBytes txBase listOff items 1 hencInner hshort hn1
      hhoff.2.1 hoverEnd _ hendEq
  have hdec2 :=
    hdec_short_list_end txBytes txBase listOff items 2 hencInner hshort hn2
      hhoff.2.2.1 hoverEnd _ hendEq
  have hdec3 :=
    hdec_short_list_end txBytes txBase listOff items 3 hencInner hshort hn3
      hhoff.2.2.2.1 hoverEnd _ hendEq
  have hdec4 :=
    hdec_short_list_end txBytes txBase listOff items 4 hencInner hshort hn4
      hhoff.2.2.2.2.1 hoverEnd _ hendEq
  have hdec5 :=
    hdec_short_list_end txBytes txBase listOff items 5 hencInner hshort hn5
      hhoff.2.2.2.2.2 hoverEnd _ hendEq
  have htx := extractSuccess_hvalid_tx0_inner txBytes txBase hsuccess hvalidBuf
  have hinover := extractSuccess_hinover txBytes txBase hsuccess hover
  have hv :=
    extractSuccess_copy_type234_hvalid_srcOff txBytes txBase hsuccess
      hcopyFlag hge items hdecL hshort hvalidBuf
  exact extractAssumed_copy_shortConcrete_pure
    sp0 spC s txBase lenW toBuf isCreationPtr contentPtr w0 w1 w2 txBytes items
    hspC hret htalign htover htvalid hcalign hcover hcvalid hcontent
    hlen hsuccess hcopyFlag hge hdecL hshort
    halign hover htx.1 hinover htx.2
    hv.1 hv.2.1 hdec0
    hv.2.2.1 hv.2.2.2.1 hdec1
    hv.2.2.2.2.1 hv.2.2.2.2.2.1 hdec2
    hv.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2.1 hdec3
    hv.2.2.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2.2.2.1 hdec4
    hv.2.2.2.2.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2.2.2.2.2 hdec5
    hge7

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_shortConcrete_pureHvalid_fullCode
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr contentPtr w0 w1 w2 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hcalign : contentPtr.toNat % 8 = 0)
    (hcover : contentPtr.toNat + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess (contentPtr + (16 : Word)) = true)
    (hcontent : contentPtr =
      txBase + BitVec.ofNat 64
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5) +
        (1 : Word))
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : extractSuccess txBytes)
    (hcopyFlag : (teerExtractToAddress txBytes).2.2 = (0 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes **
        contentDwords contentPtr w0 w1 w2)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes **
        contentDwords contentPtr w0 w1 w2) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_copy_shortConcrete_pureHvalid
      sp0 spC s txBase lenW toBuf isCreationPtr contentPtr w0 w1 w2 txBytes items
      hspC hret htalign htover htvalid hcalign hcover hcvalid hcontent
      hlen hsuccess hcopyFlag hge hdecL hshort
      halign hover hvalidBuf hge7)

#print axioms extractAssumed_copy_shortConcrete_pureHvalid
#print axioms extractAssumed_copy_shortConcrete_pureHvalid_fullCode

end EvmAsm.Codegen.TxExtractToAddressSpec
