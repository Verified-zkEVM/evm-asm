/-
  Wire pure honesty into short concrete Assumed creation:
  shortListSrcOff + hcur/hnext/hcre/hinb/hoff/hover/hls/hll/hne + short walk guards.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedShortConcrete
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitShort

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
/-- Short concrete Assumed creation with pure-discharged hcur/hnext/hcre/hinb/hoff/hover/hls/hll/hne
    and short walk guards. Residual: hvalid*/hvalid1_*/hdec*/hss wired via hvalid1. -/
theorem extractAssumed_creation_shortConcrete_pure
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
    (hinover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) = true)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0)) = true)
    (hvalid1_0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0 + 1)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next0 len0)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1)) = true)
    (hvalid1_1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1 + 1)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next1 len1)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2)) = true)
    (hvalid1_2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2 + 1)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next2 len2)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3)) = true)
    (hvalid1_3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3 + 1)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next3 len3)
    (hvalid4 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4)) = true)
    (hvalid1_4 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4 + 1)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next4 len4)
    (hvalid5 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5)) = true)
    (hvalid1_5 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5 + 1)) = true)
    (hdec5 : ∃ next5 len5 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next5 len5)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) := by
  let listOff := (teerTxTypeDispatch txBytes).2.2.toNat
  let srcOff0 := shortListSrcOff listOff items 0
  let srcOff1 := shortListSrcOff listOff items 1
  let srcOff2 := shortListSrcOff listOff items 2
  let srcOff3 := shortListSrcOff listOff items 3
  let srcOff4 := shortListSrcOff listOff items 4
  let srcOff5 := shortListSrcOff listOff items 5
  let endW := shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2) listOff
  have hty0 := extractSuccess_type_ok txBytes hsuccess
  have hlenW : lenW.toNat = txBytes.length := by
    have hspan : txBytes.length < 2 ^ 64 := by omega
    rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspan]
  have hoffInner : listOff < txBytes.length := extractSuccess_inner_lt txBytes hsuccess
  have hwalk :=
    extractSuccess_short_front_walkInit_hyps txBase lenW txBytes hsuccess hlenW
      items hdecL hshort
  have hlistLen_ne := hwalk.1
  have h_ge := hwalk.2.1
  have h_hi := hwalk.2.2.1
  have h_exact := hwalk.2.2.2
  have hne0 : (teerTxTypeDispatch txBytes).2.1 ≠ 0 := by
    intro hz
    have : (teerTxTypeDispatch txBytes).2.1.toNat = 0 := by simp [hz]
    omega
  have hne1 : (teerTxTypeDispatch txBytes).2.1 ≠ 1 := by
    intro hz
    have : (teerTxTypeDispatch txBytes).2.1.toNat = 1 := by simp [hz]
    omega
  have hhoff :=
    extractSuccess_creation_type234_hoff_srcOff txBytes hsuccess hcreFlag hge
      items hdecL hshort
  have hhover :=
    extractSuccess_creation_type234_hover_srcOff txBytes txBase hsuccess hcreFlag hge
      items hdecL hshort hover
  have hlenItems :=
    extractSuccess_creation_type234_items_length txBytes hsuccess hcreFlag hge
      items hdecL hshort
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hn4 : (4 : Nat) < items.length := by omega
  have hn5 : (5 : Nat) < items.length := by omega
  have hfields04 :=
    extractSuccess_creation_type234_hnext_fields04 txBytes hsuccess hcreFlag hge
      items hdecL hshort
  have hencInner :
      txBytes.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ hdecL
  have hendEq :
      endW = shortListEndPtr txBase listOff items := by
    change shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2) listOff =
      shortListEndPtr txBase listOff items
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
  have hcur :
      shortWalkCursor txBase listOff = txBase + BitVec.ofNat 64 srcOff0 := by
    have hoverC : txBase.toNat + (listOff + 1) < 2 ^ 64 := by omega
    simpa [shortWalkCursor, srcOff0, listOff] using
      shortWalkCursor_eq_srcOff0 txBase listOff items hoverC
  have hhnext :=
    extractSuccess_creation_type234_hnext_hcre_srcOff txBytes txBase hsuccess
      hcreFlag hge items hdecL hshort
      hhover.1 hhover.2.1 hhover.2.2.1 hhover.2.2.2.1 hhover.2.2.2.2.1 hhover.2.2.2.2.2
  have hnext1 : ∀ (next0 len0 : Word),
      rlpItemDecode txBytes srcOff0 (txBase + BitVec.ofNat 64 srcOff0) endW next0 len0 →
      next0 = txBase + BitVec.ofNat 64 srcOff1 :=
    fun n l hd => hhnext.1 endW n l hd
  have hnext2 : ∀ (next1 len1 : Word),
      rlpItemDecode txBytes srcOff1 (txBase + BitVec.ofNat 64 srcOff1) endW next1 len1 →
      next1 = txBase + BitVec.ofNat 64 srcOff2 :=
    fun n l hd => hhnext.2.1 endW n l hd
  have hnext3 : ∀ (next2 len2 : Word),
      rlpItemDecode txBytes srcOff2 (txBase + BitVec.ofNat 64 srcOff2) endW next2 len2 →
      next2 = txBase + BitVec.ofNat 64 srcOff3 :=
    fun n l hd => hhnext.2.2.1 endW n l hd
  have hnext4 : ∀ (next3 len3 : Word),
      rlpItemDecode txBytes srcOff3 (txBase + BitVec.ofNat 64 srcOff3) endW next3 len3 →
      next3 = txBase + BitVec.ofNat 64 srcOff4 :=
    fun n l hd => hhnext.2.2.2.1 endW n l hd
  have hnext5 : ∀ (next4 len4 : Word),
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4) endW next4 len4 →
      next4 = txBase + BitVec.ofNat 64 srcOff5 :=
    fun n l hd => hhnext.2.2.2.2.1 endW n l hd
  have hcre : ∀ (next5 len5 : Word),
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5) endW next5 len5 →
      len5 = (0 : Word) :=
    fun n l hd => hhnext.2.2.2.2.2 endW n l hd
  have hinb0 :=
    hinb_short_list_end txBase listOff items 0 hn0 hoverEnd endW hendEq
  have hinb1 :=
    hinb_short_list_end txBase listOff items 1 hn1 hoverEnd endW hendEq
  have hinb2 :=
    hinb_short_list_end txBase listOff items 2 hn2 hoverEnd endW hendEq
  have hinb3 :=
    hinb_short_list_end txBase listOff items 3 hn3 hoverEnd endW hendEq
  have hinb4 :=
    hinb_short_list_end txBase listOff items 4 hn4 hoverEnd endW hendEq
  have hinb5 :=
    hinb_short_list_end txBase listOff items 5 hn5 hoverEnd endW hendEq
  have hss0 :=
    hss_of_short_list_item txBytes txBase listOff items 0 hencInner hshort hn0
      hhoff.1 hover (Or.inl hfields04.1) hvalid1_0
  have hss1 :=
    hss_of_short_list_item txBytes txBase listOff items 1 hencInner hshort hn1
      hhoff.2.1 hover (Or.inl hfields04.2.1) hvalid1_1
  have hss2 :=
    hss_of_short_list_item txBytes txBase listOff items 2 hencInner hshort hn2
      hhoff.2.2.1 hover (Or.inl hfields04.2.2.1) hvalid1_2
  have hss3 :=
    hss_of_short_list_item txBytes txBase listOff items 3 hencInner hshort hn3
      hhoff.2.2.2.1 hover (Or.inl hfields04.2.2.2.1) hvalid1_3
  have hss4 :=
    hss_of_short_list_item txBytes txBase listOff items 4 hencInner hshort hn4
      hhoff.2.2.2.2.1 hover (Or.inl hfields04.2.2.2.2) hvalid1_4
  have hss5 :=
    hss_of_short_list_item txBytes txBase listOff items 5 hencInner hshort hn5
      hhoff.2.2.2.2.2 hover (Or.inl (by omega)) hvalid1_5
  have hoff := hoffInner
  exact extractAssumed_creation_under_honesty_of_decode_short_concrete
    sp0 spC s txBase lenW toBuf isCreationPtr txBytes
    srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 srcOff5
    hspC hret hcur hne0 hne1 halign
    hhoff.1 hhover.1 hvalid0 hss0
    (hls_vacuous_of_short_list_item txBytes listOff items 0 hencInner hshort hn0 hhoff.1)
    (hll_vacuous_of_short_list_item txBytes listOff items 0 hencInner hshort hn0 hhoff.1)
    hdec0 hinb0
    hhoff.2.1 hhover.2.1 hvalid1 hss1
    (hls_vacuous_of_short_list_item txBytes listOff items 1 hencInner hshort hn1 hhoff.2.1)
    (hll_vacuous_of_short_list_item txBytes listOff items 1 hencInner hshort hn1 hhoff.2.1)
    hdec1 hinb1
    hhoff.2.2.1 hhover.2.2.1 hvalid2 hss2
    (hls_vacuous_of_short_list_item txBytes listOff items 2 hencInner hshort hn2 hhoff.2.2.1)
    (hll_vacuous_of_short_list_item txBytes listOff items 2 hencInner hshort hn2 hhoff.2.2.1)
    hdec2 hinb2
    hhoff.2.2.2.1 hhover.2.2.2.1 hvalid3 hss3
    (hls_vacuous_of_short_list_item txBytes listOff items 3 hencInner hshort hn3 hhoff.2.2.2.1)
    (hll_vacuous_of_short_list_item txBytes listOff items 3 hencInner hshort hn3 hhoff.2.2.2.1)
    hdec3 hinb3
    hhoff.2.2.2.2.1 hhover.2.2.2.2.1 hvalid4 hss4
    (hls_vacuous_of_short_list_item txBytes listOff items 4 hencInner hshort hn4 hhoff.2.2.2.2.1)
    (hll_vacuous_of_short_list_item txBytes listOff items 4 hencInner hshort hn4 hhoff.2.2.2.2.1)
    hdec4 hinb4
    hhoff.2.2.2.2.2 hhover.2.2.2.2.2 hvalid5 hss5
    (hls_vacuous_of_short_list_item txBytes listOff items 5 hencInner hshort hn5 hhoff.2.2.2.2.2)
    (hll_vacuous_of_short_list_item txBytes listOff items 5 hencInner hshort hn5 hhoff.2.2.2.2.2)
    hdec5 hinb5
    hnext1 hnext2 hnext3 hnext4 hnext5 hcre
    htalign htover htvalid hlen hty0 hover hvalidTx0
    hoff hinover hinvalid hlistLen_ne h_ge h_hi h_exact

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_shortConcrete_pure_fullCode
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
    (hinover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) = true)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0)) = true)
    (hvalid1_0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0 + 1)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next0 len0)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1)) = true)
    (hvalid1_1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1 + 1)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next1 len1)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2)) = true)
    (hvalid1_2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2 + 1)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next2 len2)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3)) = true)
    (hvalid1_3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3 + 1)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next3 len3)
    (hvalid4 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4)) = true)
    (hvalid1_4 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4 + 1)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next4 len4)
    (hvalid5 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5)) = true)
    (hvalid1_5 : isValidByteAccess (txBase + BitVec.ofNat 64
      (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5 + 1)) = true)
    (hdec5 : ∃ next5 len5 : Word,
      rlpItemDecode txBytes
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5)
        (txBase + BitVec.ofNat 64
          (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5))
        (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next5 len5)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_creation_shortConcrete_pure sp0 spC s
      txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag hge hdecL hshort
      halign hover hvalidTx0 hinover hinvalid
      hvalid0 hvalid1_0 hdec0
      hvalid1 hvalid1_1 hdec1
      hvalid2 hvalid1_2 hdec2
      hvalid3 hvalid1_3 hdec3
      hvalid4 hvalid1_4 hdec4
      hvalid5 hvalid1_5 hdec5
      hge7)

#print axioms extractAssumed_creation_shortConcrete_pure
#print axioms extractAssumed_creation_shortConcrete_pure_fullCode

end EvmAsm.Codegen.TxExtractToAddressSpec
