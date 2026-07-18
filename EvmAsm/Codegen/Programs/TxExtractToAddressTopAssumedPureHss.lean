/-
  Assumed creation: discharge hss under short-list encode (room+hover pure;
  hvalid1 at srcOff+1 residual; field5 needs not-last-or-ge2).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedPureHlsHll
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

private abbrev listOff (txBytes : List (BitVec 8)) : Nat :=
  (teerTxTypeDispatch txBytes).2.2.toNat

private abbrev srcOff (txBytes : List (BitVec 8)) (items : List EL.RLP.RLPItem) (k : Nat) : Nat :=
  shortListSrcOff (listOff txBytes) items k

set_option maxRecDepth 8000 in
/-- Assumed creation with pure hss (hvalid1_* residual at srcOff+1). -/
theorem extractAssumed_creation_shortListSrcOff_pureHss
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
    (hvalid1_0 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0 + 1)) = true)
    (hdec0 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)) endPtr n l)
    (hinb0 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)) endPtr = true)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) = true)
    (hvalid1_1 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1 + 1)) = true)
    (hdec1 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) endPtr n l)
    (hinb1 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) endPtr = true)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) = true)
    (hvalid1_2 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2 + 1)) = true)
    (hdec2 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) endPtr n l)
    (hinb2 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) endPtr = true)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) = true)
    (hvalid1_3 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3 + 1)) = true)
    (hdec3 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) endPtr n l)
    (hinb3 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) endPtr = true)
    (hvalid4 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) = true)
    (hvalid1_4 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4 + 1)) = true)
    (hdec4 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) endPtr n l)
    (hinb4 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) endPtr = true)
    (hvalid5 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) = true)
    (hvalid1_5 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5 + 1)) = true)
    (hdec5 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) endPtr n l)
    (hinb5 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) endPtr = true)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) := by
  have hencInner :
      txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat =
        encode (.list items) :=
    decodeListItems_eq_encode _ _ hdecL
  have hlenItems :=
    extractSuccess_creation_type234_items_length txBytes hsuccess hcreFlag hge
      items hdecL hshort
  have hn0 : (0 : Nat) < items.length := by have := hlenItems; omega
  have hn1 : (1 : Nat) < items.length := by have := hlenItems; omega
  have hn2 : (2 : Nat) < items.length := by have := hlenItems; omega
  have hn3 : (3 : Nat) < items.length := by have := hlenItems; omega
  have hn4 : (4 : Nat) < items.length := by have := hlenItems; omega
  have hn5 : (5 : Nat) < items.length := by have := hlenItems; omega
  have hfields04 :=
    extractSuccess_creation_type234_hnext_fields04 txBytes hsuccess hcreFlag hge
      items hdecL hshort
  have hhoff :=
    extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge
      items hdecL hshort
  -- Build hss0..5 via pure room + residual hvalid1_*
  exact extractAssumed_creation_shortListSrcOff_pureHlsHll
    sp0 spC s txBase lenW toBuf isCreationPtr txBytes items
    hspC hret htalign htover htvalid hlen hsuccess hcreFlag hge hdecL hshort
    halign hover hvalidTx0 hoff hinover hinvalid hlistLen_ne h_ge h_hi h_exact
    hcur hne0 hne1
    hvalid0
    (hss_of_short_list_item txBytes txBase
      (teerTxTypeDispatch txBytes).2.2.toNat items 0
      hencInner hshort hn0 hhoff.1 hover
      (Or.inl hfields04.1) hvalid1_0)
    hdec0 hinb0
    hvalid1
    (hss_of_short_list_item txBytes txBase
      (teerTxTypeDispatch txBytes).2.2.toNat items 1
      hencInner hshort hn1 hhoff.2.1 hover
      (Or.inl hfields04.2.1) hvalid1_1)
    hdec1 hinb1
    hvalid2
    (hss_of_short_list_item txBytes txBase
      (teerTxTypeDispatch txBytes).2.2.toNat items 2
      hencInner hshort hn2 hhoff.2.2.1 hover
      (Or.inl hfields04.2.2.1) hvalid1_2)
    hdec2 hinb2
    hvalid3
    (hss_of_short_list_item txBytes txBase
      (teerTxTypeDispatch txBytes).2.2.toNat items 3
      hencInner hshort hn3 hhoff.2.2.2.1 hover
      (Or.inl hfields04.2.2.2.1) hvalid1_3)
    hdec3 hinb3
    hvalid4
    (hss_of_short_list_item txBytes txBase
      (teerTxTypeDispatch txBytes).2.2.toNat items 4
      hencInner hshort hn4 hhoff.2.2.2.2.1 hover
      (Or.inl hfields04.2.2.2.2) hvalid1_4)
    hdec4 hinb4
    hvalid5
    (hss_of_short_list_item txBytes txBase
      (teerTxTypeDispatch txBytes).2.2.toNat items 5
      hencInner hshort hn5 hhoff.2.2.2.2.2 hover
      (Or.inl (by have := hge7; omega)) hvalid1_5)
    hdec5 hinb5

set_option maxRecDepth 8000 in
/-- Same under intrinsic `fullCode`. -/
theorem extractAssumed_creation_shortListSrcOff_pureHss_fullCode
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
    (hvalid1_0 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0 + 1)) = true)
    (hdec0 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)) endPtr n l)
    (hinb0 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 0)) endPtr = true)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) = true)
    (hvalid1_1 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1 + 1)) = true)
    (hdec1 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) endPtr n l)
    (hinb1 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 1)) endPtr = true)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) = true)
    (hvalid1_2 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2 + 1)) = true)
    (hdec2 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) endPtr n l)
    (hinb2 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 2)) endPtr = true)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) = true)
    (hvalid1_3 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3 + 1)) = true)
    (hdec3 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) endPtr n l)
    (hinb3 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 3)) endPtr = true)
    (hvalid4 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) = true)
    (hvalid1_4 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4 + 1)) = true)
    (hdec4 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) endPtr n l)
    (hinb4 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 4)) endPtr = true)
    (hvalid5 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) = true)
    (hvalid1_5 : isValidByteAccess (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5 + 1)) = true)
    (hdec5 : ∀ (endPtr : Word), ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5) (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) endPtr n l)
    (hinb5 : ∀ (endPtr : Word),
      BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff ((teerTxTypeDispatch txBytes).2.2.toNat) items 5)) endPtr = true)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) := by
  exact cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_creation_shortListSrcOff_pureHss
      sp0 spC s txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag hge hdecL hshort
      halign hover hvalidTx0 hoff hinover hinvalid hlistLen_ne h_ge h_hi h_exact
      hcur hne0 hne1
      hvalid0 hvalid1_0 hdec0 hinb0
      hvalid1 hvalid1_1 hdec1 hinb1
      hvalid2 hvalid1_2 hdec2 hinb2
      hvalid3 hvalid1_3 hdec3 hinb3
      hvalid4 hvalid1_4 hdec4 hinb4
      hvalid5 hvalid1_5 hdec5 hinb5
      hge7)

#print axioms extractAssumed_creation_shortListSrcOff_pureHss
#print axioms extractAssumed_creation_shortListSrcOff_pureHss_fullCode

end EvmAsm.Codegen.TxExtractToAddressSpec
