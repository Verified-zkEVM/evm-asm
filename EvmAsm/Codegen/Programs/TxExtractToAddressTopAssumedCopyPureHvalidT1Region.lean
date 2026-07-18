/-
  Wire pure honesty into short concrete bare Assumed t1 copy path (region).
  Gates content dword-alignment: shortListSrcOff 4 + 1 = 8*q.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyT1Region
import EvmAsm.Codegen.Programs.TxExtractToAddressCopyFromRegion
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
open EvmAsm.Rv64.RLP (rlpItemDecode)
open EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_shortConcrete_pureHvalid_t1_region
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hq_align : shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4 + 1 = 8 * q)
    (hq : 8 * q + 16 < txBytes.length)
    (hcover : txBase.toNat + (8 * q + 16) < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (txBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : extractSuccess txBytes)
    (hcopyFlag : (teerExtractToAddress txBytes).2.2 = (0 : Word))
    (htype1 : (teerTxTypeDispatch txBytes).2.1 = (1 : Word))
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (hge6 : 6 ≤ items.length) :
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
  let endW := shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2) listOff
  let contentPtr := txBase + BitVec.ofNat 64 (8 * q)
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
  have hhoff :=
    extractSuccess_copy_t1_hoff_srcOff txBytes hsuccess hcopyFlag htype1
      items hdecL hshort
  have hhover :=
    extractSuccess_copy_t1_hover_srcOff txBytes txBase hsuccess hcopyFlag htype1
      items hdecL hshort hover
  have hlenItems :=
    extractSuccess_copy_t1_items_length txBytes hsuccess hcopyFlag htype1
      items hdecL hshort
  have hhnext :=
    extractSuccess_copy_t1_hnext_hlen20_srcOff txBytes txBase hsuccess
      hcopyFlag htype1 items hdecL hshort
      hhover.1 hhover.2.1 hhover.2.2.1 hhover.2.2.2.1 hhover.2.2.2.2
  have hv :=
    extractSuccess_copy_t1_hvalid_srcOff txBytes txBase hsuccess
      hcopyFlag htype1 items hdecL hshort hge6 hvalidBuf
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hn4 : (4 : Nat) < items.length := by omega
  have hfields :=
    extractSuccess_copy_t1_hnext_fields03 txBytes hsuccess hcopyFlag htype1
      items hdecL hshort hge6
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
  have hlen20 : ∀ (next4 len4 : Word),
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4) endW next4 len4 →
      len4 = (20 : Word) :=
    fun n l hd => hhnext.2.2.2.2 endW n l hd
  have hcontentPtr : contentPtr = txBase + BitVec.ofNat 64 srcOff4 + (1 : Word) := by
    have hsrc : srcOff4 + 1 = 8 * q := by
      simpa [srcOff4, listOff] using hq_align
    have hbase : txBase.toNat + (srcOff4 + 1) < 2 ^ 64 := by
      have : srcOff4 + 1 ≤ 8 * q + 16 := by omega
      omega
    have h1 : BitVec.ofNat 64 (srcOff4 + 1) = BitVec.ofNat 64 srcOff4 + (1 : Word) := by
      have hs : srcOff4 < 2 ^ 64 := by omega
      have hs1 : srcOff4 + 1 < 2 ^ 64 := by omega
      apply BitVec.eq_of_toNat_eq
      change (srcOff4 + 1) % 2 ^ 64 = (BitVec.ofNat 64 srcOff4 + (1 : Word)).toNat
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
        show (1 : Word).toNat = 1 by decide, Nat.mod_eq_of_lt hs1]
    simpa [contentPtr, ← hsrc, h1] using
      (BitVec.add_assoc txBase (BitVec.ofNat 64 srcOff4) (1 : Word)).symm
  have hnext_content : ∀ (next4 len4 : Word),
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4) endW next4 len4 →
      next4 = txBase + BitVec.ofNat 64 (8 * q) + (20 : Word) := by
    intro n l hd
    have hc := extractSuccess_copy_t1_hnext_content txBytes txBase contentPtr srcOff4
      hsuccess hcopyFlag htype1 items hdecL hshort rfl hcontentPtr endW n l hd
    simpa [contentPtr] using hc
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
  have hss0 :=
    hss_of_short_list_item txBytes txBase listOff items 0 hencInner hshort hn0
      hhoff.1 hover (Or.inl hfields.1) hv.2.1
  have hss1 :=
    hss_of_short_list_item txBytes txBase listOff items 1 hencInner hshort hn1
      hhoff.2.1 hover (Or.inl hfields.2.1) hv.2.2.2.1
  have hss2 :=
    hss_of_short_list_item txBytes txBase listOff items 2 hencInner hshort hn2
      hhoff.2.2.1 hover (Or.inl hfields.2.2.1) hv.2.2.2.2.2.1
  have hss3 :=
    hss_of_short_list_item txBytes txBase listOff items 3 hencInner hshort hn3
      hhoff.2.2.2.1 hover (Or.inl hfields.2.2.2) hv.2.2.2.2.2.2.2.1
  have hss4 :=
    hss_of_short_list_item txBytes txBase listOff items 4 hencInner hshort hn4
      hhoff.2.2.2.2 hover (Or.inl (by omega)) hv.2.2.2.2.2.2.2.2.2
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
      hhoff.2.2.2.2 hoverEnd _ hendEq
  have hoff := hoffInner
  have htx := extractSuccess_hvalid_tx0_inner txBytes txBase hsuccess hvalidBuf
  have hinover' := extractSuccess_hinover txBytes txBase hsuccess hover
  exact extractAssumed_copy_of_front_short_concrete_t1_region
    sp0 spC s txBase lenW toBuf isCreationPtr txBytes
    srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 q
    hspC hret hcur htype1 halign
    hhoff.1 hhover.1 hv.1 hss0
    (hls_vacuous_of_short_list_item txBytes listOff items 0 hencInner hshort hn0 hhoff.1)
    (hll_vacuous_of_short_list_item txBytes listOff items 0 hencInner hshort hn0 hhoff.1)
    hdec0 hinb0
    hhoff.2.1 hhover.2.1 hv.2.2.1 hss1
    (hls_vacuous_of_short_list_item txBytes listOff items 1 hencInner hshort hn1 hhoff.2.1)
    (hll_vacuous_of_short_list_item txBytes listOff items 1 hencInner hshort hn1 hhoff.2.1)
    hdec1 hinb1
    hhoff.2.2.1 hhover.2.2.1 hv.2.2.2.2.1 hss2
    (hls_vacuous_of_short_list_item txBytes listOff items 2 hencInner hshort hn2 hhoff.2.2.1)
    (hll_vacuous_of_short_list_item txBytes listOff items 2 hencInner hshort hn2 hhoff.2.2.1)
    hdec2 hinb2
    hhoff.2.2.2.1 hhover.2.2.2.1 hv.2.2.2.2.2.2.1 hss3
    (hls_vacuous_of_short_list_item txBytes listOff items 3 hencInner hshort hn3 hhoff.2.2.2.1)
    (hll_vacuous_of_short_list_item txBytes listOff items 3 hencInner hshort hn3 hhoff.2.2.2.1)
    hdec3 hinb3
    hhoff.2.2.2.2 hhover.2.2.2.2 hv.2.2.2.2.2.2.2.2.1 hss4
    (hls_vacuous_of_short_list_item txBytes listOff items 4 hencInner hshort hn4 hhoff.2.2.2.2)
    (hll_vacuous_of_short_list_item txBytes listOff items 4 hencInner hshort hn4 hhoff.2.2.2.2)
    hdec4 hinb4
    hnext1 hnext2 hnext3 hnext4 hlen20 hnext_content
    hq hcover hcvalid htalign htover htvalid hlen hty0 hover
    htx.1 hoff hinover' htx.2 hlistLen_ne h_ge h_hi h_exact

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_shortConcrete_pureHvalid_t1_region_fullCode
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hq_align : shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4 + 1 = 8 * q)
    (hq : 8 * q + 16 < txBytes.length)
    (hcover : txBase.toNat + (8 * q + 16) < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (txBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : extractSuccess txBytes)
    (hcopyFlag : (teerExtractToAddress txBytes).2.2 = (0 : Word))
    (htype1 : (teerTxTypeDispatch txBytes).2.1 = (1 : Word))
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (hge6 : 6 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_copy_shortConcrete_pureHvalid_t1_region
      sp0 spC s txBase lenW toBuf isCreationPtr txBytes items q
      hspC hret htalign htover htvalid hq_align hq hcover hcvalid
      hlen hsuccess hcopyFlag htype1 hdecL hshort
      halign hover hvalidBuf hge6)

#print axioms extractAssumed_copy_shortConcrete_pureHvalid_t1_region
#print axioms extractAssumed_copy_shortConcrete_pureHvalid_t1_region_fullCode

end EvmAsm.Codegen.TxExtractToAddressSpec
