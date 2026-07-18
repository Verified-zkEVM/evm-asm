/-
  Wire pure honesty into long concrete bare Assumed copy path (region).
  Gates content dword-alignment: longListSrcOff 5 + 1 = 8*q.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyLongRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressCopyFromRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitLong
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
/-- Bare Assumed long type234 copy under pure honesty + dword-aligned content.
    `hq_align : longListSrcOff listOff items 5 + 1 = 8 * q`. classical-3. -/
theorem extractAssumed_copy_longConcrete_pureHvalid_region
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
    (hq_align : longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5 + 1 = 8 * q)
    (hq : 8 * q + 16 < txBytes.length)
    (hcover : txBase.toNat + (8 * q + 16) < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (txBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : extractSuccess txBytes)
    (hcopyFlag : (teerExtractToAddress txBytes).2.2 = (0 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hlong : 55 < (encode.encodeItems items).length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (hitem0 : (encode (items[0]'(by
        have := extractSuccess_copy_type234_items_length_long txBytes hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_copy_type234_items_length_long txBytes hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_copy_type234_items_length_long txBytes hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_copy_type234_items_length_long txBytes hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by
        have := extractSuccess_copy_type234_items_length_long txBytes hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) := by
  let listOff := (teerTxTypeDispatch txBytes).2.2.toNat
  let srcOff0 := longListSrcOff listOff items 0
  let srcOff1 := longListSrcOff listOff items 1
  let srcOff2 := longListSrcOff listOff items 2
  let srcOff3 := longListSrcOff listOff items 3
  let srcOff4 := longListSrcOff listOff items 4
  let srcOff5 := longListSrcOff listOff items 5
  let endW := longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2) listOff
  let contentPtr := txBase + BitVec.ofNat 64 (8 * q)
  have hty0 := extractSuccess_type_ok txBytes hsuccess
  have hlenW : lenW.toNat = txBytes.length := by
    have hspan : txBytes.length < 2 ^ 64 := by omega
    rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspan]
  have hbuf : txBytes.length < 2 ^ 64 := by omega
  have hoffInner : listOff < txBytes.length := extractSuccess_inner_lt txBytes hsuccess
  have hencInner :
      txBytes.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ hdecL
  have hbound : (encode.encodeItems items).length < 256 ^ 8 := by
    have hbsLt : (txBytes.drop listOff).length < 2 ^ 64 := by
      have hle : (txBytes.drop listOff).length ≤ txBytes.length := by
        simp only [List.length_drop]; omega
      exact Nat.lt_of_le_of_lt hle hbuf
    exact encodeItems_lt_256pow8_of_buf_lt (txBytes.drop listOff) items hencInner hlong hbsLt
  have htx := extractSuccess_hvalid_tx0_inner txBytes txBase hsuccess hvalidBuf
  have hinover' := extractSuccess_hinover txBytes txBase hsuccess hover
  have hptr : (txBase + BitVec.ofNat 64 listOff).toNat = txBase.toNat + listOff :=
    toNat_add_ofNat_lt txBase listOff hinover'
  have hend : (txBase + BitVec.ofNat 64 listOff).toNat +
      (lenW - (teerTxTypeDispatch txBytes).2.2).toNat < 2 ^ 64 := by
    rw [hptr]
    have hlistLen := listLen_word_eq_drop txBytes lenW
      (teerTxTypeDispatch txBytes).2.2 hoffInner hlenW
    have hdrop : (txBytes.drop listOff).length = txBytes.length - listOff := by
      simp only [List.length_drop]
    have hencLen := encode_list_long_length items hlong
    have hdropEq : (txBytes.drop listOff).length = (encode (.list items)).length := by
      rw [hencInner]
    have hlistLen' : (lenW - (teerTxTypeDispatch txBytes).2.2).toNat =
        (txBytes.drop listOff).length := by
      simpa [listOff] using hlistLen
    have hsum :
        txBase.toNat + listOff + (lenW - (teerTxTypeDispatch txBytes).2.2).toNat =
          txBase.toNat + txBytes.length := by
      have : listOff + (txBytes.drop listOff).length = txBytes.length := by
        have hle : listOff ≤ txBytes.length := Nat.le_of_lt hoffInner
        omega
      omega
    omega
  have hleaf :=
    extractSuccess_long_walkInit_leaf_hyps txBase lenW txBytes hsuccess hlenW
      items hdecL hlong hbuf hptr hend
  obtain ⟨hoff, hwi_off1, hlistLen_ne, h_ge, h_ge_f8, hllen, h_fits, h_llz, h_min, h_match⟩ :=
    hleaf
  have hlolEq : ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat =
      longListLol items := by
    have hpfx := long_list_pfx_at txBytes listOff items hencInner hlong hoff
    rw [hpfx]; exact pfx_sub_F7_eq_lol items hlong hbound
  have hll :=
    extractSuccess_long_hlover_hlvalid txBytes txBase hsuccess items hdecL hlong
      hover hvalidBuf
  have hlover' : txBase.toNat + (listOff + 1 +
      ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 := by
    rw [hlolEq]
    simpa [listOff] using hll.1
  have hlvalid' : ∀ k, k < ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (txBase + BitVec.ofNat 64 (listOff + 1 + k)) = true := by
    intro k hk
    have hk' : k < longListLol items := by rwa [hlolEq] at hk
    simpa [listOff] using hll.2 k hk'
  have hlol : ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
    have : longListLol items ≤ 8 :=
      Nat.toBytesBE_length_le (encode.encodeItems items).length 8 hbound
    exact hlolEq.symm ▸ this
  have hne0 : (teerTxTypeDispatch txBytes).2.1 ≠ 0 := by
    intro hz
    have : (teerTxTypeDispatch txBytes).2.1.toNat = 0 := by simp [hz]
    omega
  have hne1 : (teerTxTypeDispatch txBytes).2.1 ≠ 1 := by
    intro hz
    have : (teerTxTypeDispatch txBytes).2.1.toNat = 1 := by simp [hz]
    omega
  have hhoff :=
    extractSuccess_copy_type234_hoff_srcOff_long txBytes hsuccess hcopyFlag hge
      items hdecL hlong
  have hhover :=
    extractSuccess_copy_type234_hover_srcOff_long txBytes txBase hsuccess hcopyFlag hge
      items hdecL hlong hover
  have hlenItems :=
    extractSuccess_copy_type234_items_length_long txBytes hsuccess hcopyFlag hge
      items hdecL hlong
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hn4 : (4 : Nat) < items.length := by omega
  have hn5 : (5 : Nat) < items.length := by omega
  have hitem5 :
      (encode (items[5]'hn5)).length ≤ 55 :=
    extractSuccess_copy_type234_field5_encode_le55_long txBytes hsuccess hcopyFlag hge
      items hdecL hlong
  have hfields04 :=
    extractSuccess_copy_type234_hnext_fields04_long txBytes hsuccess hcopyFlag hge
      items hdecL hlong
  have hendEq :
      endW = longListEndPtr txBase listOff items := by
    change longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2) listOff =
      longListEndPtr txBase listOff items
    simpa [longWalkEnd, listOff] using
      (longWalkEnd_eq_longListEndPtr txBase lenW txBytes items hsuccess hlenW
        hdecL hlong hover)
  have hoverEnd : txBase.toNat +
      (listOff + 1 + longListLol items + (encode.encodeItems items).length) < 2 ^ 64 := by
    have hdrop : (txBytes.drop listOff).length = txBytes.length - listOff := by
      simp only [List.length_drop]
    have hencLen := encode_list_long_length items hlong
    have hdropEq : (txBytes.drop listOff).length = (encode (.list items)).length := by
      rw [hencInner]
    change txBase.toNat +
        (listOff + 1 + longListLol items + longListPayloadLen items) < 2 ^ 64
    have hsum : listOff + (1 + longListLol items + longListPayloadLen items) =
        txBytes.length := by
      have : listOff + (txBytes.drop listOff).length = txBytes.length := by
        have hle : listOff ≤ txBytes.length := Nat.le_of_lt hoffInner
        omega
      calc
        listOff + (1 + longListLol items + longListPayloadLen items)
            = listOff + (encode (.list items)).length := by rw [← hencLen]
        _ = listOff + (txBytes.drop listOff).length := by rw [← hdropEq]
        _ = txBytes.length := this
    omega
  have hcur :
      longWalkCursor txBase txBytes listOff hoff =
        txBase + BitVec.ofNat 64 srcOff0 := by
    have hoverC : txBase.toNat + (listOff + 1 + longListLol items) < 2 ^ 64 := by
      have : longListLol items ≤ 8 :=
        Nat.toBytesBE_length_le (encode.encodeItems items).length 8 hbound
      omega
    simpa [longWalkCursor, srcOff0, listOff] using
      longWalkCursor_eq_srcOff0 txBytes txBase listOff items hencInner hlong hbound
        hoff hoverC
  have hhnext :=
    extractSuccess_copy_type234_hnext_hlen20_srcOff_long txBytes txBase hsuccess
      hcopyFlag hge items hdecL hlong
      hitem0 hitem1 hitem2 hitem3 hitem4
      hhover.1 hhover.2.1 hhover.2.2.1 hhover.2.2.2.1 hhover.2.2.2.2.1
      hhover.2.1 hhover.2.2.1 hhover.2.2.2.1 hhover.2.2.2.2.1 hhover.2.2.2.2.2
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
  have hlen20 : ∀ (next5 len5 : Word),
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5) endW next5 len5 →
      len5 = (20 : Word) :=
    fun n l hd => hhnext.2.2.2.2.2 endW n l hd
  have hcontentPtr : contentPtr = txBase + BitVec.ofNat 64 srcOff5 + (1 : Word) := by
    have hsrc : srcOff5 + 1 = 8 * q := by
      simpa [srcOff5, listOff] using hq_align
    have hbase : txBase.toNat + (srcOff5 + 1) < 2 ^ 64 := by
      have : srcOff5 + 1 ≤ 8 * q + 16 := by omega
      omega
    have h1 : BitVec.ofNat 64 (srcOff5 + 1) = BitVec.ofNat 64 srcOff5 + (1 : Word) := by
      have hs : srcOff5 < 2 ^ 64 := by omega
      have hs1 : srcOff5 + 1 < 2 ^ 64 := by omega
      apply BitVec.eq_of_toNat_eq
      change (srcOff5 + 1) % 2 ^ 64 = (BitVec.ofNat 64 srcOff5 + (1 : Word)).toNat
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
        show (1 : Word).toNat = 1 by decide, Nat.mod_eq_of_lt hs1]
    simpa [contentPtr, ← hsrc, h1] using
      (BitVec.add_assoc txBase (BitVec.ofNat 64 srcOff5) (1 : Word)).symm
  have hnext_content : ∀ (next5 len5 : Word),
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5) endW next5 len5 →
      next5 = txBase + BitVec.ofNat 64 (8 * q) + (20 : Word) := by
    intro n l hd
    have hc := extractSuccess_copy_type234_hnext_content_long txBytes txBase contentPtr
      srcOff5 hsuccess hcopyFlag hge items hdecL hlong rfl hcontentPtr endW n l hd
    simpa [contentPtr] using hc
  have hinb0 :=
    hinb_long_list_end txBase listOff items 0 hn0 hoverEnd endW hendEq
  have hinb1 :=
    hinb_long_list_end txBase listOff items 1 hn1 hoverEnd endW hendEq
  have hinb2 :=
    hinb_long_list_end txBase listOff items 2 hn2 hoverEnd endW hendEq
  have hinb3 :=
    hinb_long_list_end txBase listOff items 3 hn3 hoverEnd endW hendEq
  have hinb4 :=
    hinb_long_list_end txBase listOff items 4 hn4 hoverEnd endW hendEq
  have hinb5 :=
    hinb_long_list_end txBase listOff items 5 hn5 hoverEnd endW hendEq
  have hv :=
    extractSuccess_copy_type234_hvalid_srcOff_long txBytes txBase hsuccess
      hcopyFlag hge items hdecL hlong hge7 hvalidBuf
  have hss0 :=
    hss_of_long_list_item txBytes txBase listOff items 0 hencInner hlong hn0 hitem0
      hhoff.1 hover (Or.inl hfields04.1) hv.2.1
  have hss1 :=
    hss_of_long_list_item txBytes txBase listOff items 1 hencInner hlong hn1 hitem1
      hhoff.2.1 hover (Or.inl hfields04.2.1) hv.2.2.2.1
  have hss2 :=
    hss_of_long_list_item txBytes txBase listOff items 2 hencInner hlong hn2 hitem2
      hhoff.2.2.1 hover (Or.inl hfields04.2.2.1) hv.2.2.2.2.2.1
  have hss3 :=
    hss_of_long_list_item txBytes txBase listOff items 3 hencInner hlong hn3 hitem3
      hhoff.2.2.2.1 hover (Or.inl hfields04.2.2.2.1) hv.2.2.2.2.2.2.2.1
  have hss4 :=
    hss_of_long_list_item txBytes txBase listOff items 4 hencInner hlong hn4 hitem4
      hhoff.2.2.2.2.1 hover (Or.inl hfields04.2.2.2.2) hv.2.2.2.2.2.2.2.2.2.1
  have hss5 :=
    hss_of_long_list_item txBytes txBase listOff items 5 hencInner hlong hn5 hitem5
      hhoff.2.2.2.2.2 hover (Or.inl (by omega)) hv.2.2.2.2.2.2.2.2.2.2.2
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
      hhoff.2.2.2.1 hoverEnd _ hendEq
  have hdec4 :=
    hdec_long_list_end txBytes txBase listOff items 4 hencInner hlong hn4 hitem4
      hhoff.2.2.2.2.1 hoverEnd _ hendEq
  have hdec5 :=
    hdec_long_list_end txBytes txBase listOff items 5 hencInner hlong hn5 hitem5
      hhoff.2.2.2.2.2 hoverEnd _ hendEq
  exact extractAssumed_copy_of_front_long_concrete_region
    sp0 spC s txBase lenW toBuf isCreationPtr txBytes
    srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 srcOff5 q
    hspC hret hoff hcur hne0 hne1 halign
    hhoff.1 hhover.1 hv.1 hss0
    (hls_vacuous_of_long_list_item txBytes listOff items 0 hencInner hlong hn0 hitem0 hhoff.1)
    (hll_vacuous_of_long_list_item txBytes listOff items 0 hencInner hlong hn0 hitem0 hhoff.1)
    hdec0 hinb0
    hhoff.2.1 hhover.2.1 hv.2.2.1 hss1
    (hls_vacuous_of_long_list_item txBytes listOff items 1 hencInner hlong hn1 hitem1 hhoff.2.1)
    (hll_vacuous_of_long_list_item txBytes listOff items 1 hencInner hlong hn1 hitem1 hhoff.2.1)
    hdec1 hinb1
    hhoff.2.2.1 hhover.2.2.1 hv.2.2.2.2.1 hss2
    (hls_vacuous_of_long_list_item txBytes listOff items 2 hencInner hlong hn2 hitem2 hhoff.2.2.1)
    (hll_vacuous_of_long_list_item txBytes listOff items 2 hencInner hlong hn2 hitem2 hhoff.2.2.1)
    hdec2 hinb2
    hhoff.2.2.2.1 hhover.2.2.2.1 hv.2.2.2.2.2.2.1 hss3
    (hls_vacuous_of_long_list_item txBytes listOff items 3 hencInner hlong hn3 hitem3 hhoff.2.2.2.1)
    (hll_vacuous_of_long_list_item txBytes listOff items 3 hencInner hlong hn3 hitem3 hhoff.2.2.2.1)
    hdec3 hinb3
    hhoff.2.2.2.2.1 hhover.2.2.2.2.1 hv.2.2.2.2.2.2.2.2.1 hss4
    (hls_vacuous_of_long_list_item txBytes listOff items 4 hencInner hlong hn4 hitem4 hhoff.2.2.2.2.1)
    (hll_vacuous_of_long_list_item txBytes listOff items 4 hencInner hlong hn4 hitem4 hhoff.2.2.2.2.1)
    hdec4 hinb4
    hhoff.2.2.2.2.2 hhover.2.2.2.2.2 hv.2.2.2.2.2.2.2.2.2.2.1 hss5
    (hls_vacuous_of_long_list_item txBytes listOff items 5 hencInner hlong hn5 hitem5 hhoff.2.2.2.2.2)
    (hll_vacuous_of_long_list_item txBytes listOff items 5 hencInner hlong hn5 hitem5 hhoff.2.2.2.2.2)
    hdec5 hinb5
    hnext1 hnext2 hnext3 hnext4 hnext5 hlen20 hnext_content
    hq hcover hcvalid htalign htover htvalid hlen hty0 hover
    htx.1 hoff hinover' htx.2 hlistLen_ne h_ge h_ge_f8 hllen hlover' hlvalid'
    hwi_off1 h_fits h_llz h_min h_match hlol

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_longConcrete_pureHvalid_region_fullCode
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
    (hq_align : longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5 + 1 = 8 * q)
    (hq : 8 * q + 16 < txBytes.length)
    (hcover : txBase.toNat + (8 * q + 16) < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (txBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : extractSuccess txBytes)
    (hcopyFlag : (teerExtractToAddress txBytes).2.2 = (0 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hlong : 55 < (encode.encodeItems items).length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (hitem0 : (encode (items[0]'(by
        have := extractSuccess_copy_type234_items_length_long txBytes hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_copy_type234_items_length_long txBytes hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_copy_type234_items_length_long txBytes hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_copy_type234_items_length_long txBytes hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by
        have := extractSuccess_copy_type234_items_length_long txBytes hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_copy_longConcrete_pureHvalid_region
      sp0 spC s txBase lenW toBuf isCreationPtr txBytes items q
      hspC hret htalign htover htvalid hq_align hq hcover hcvalid
      hlen hsuccess hcopyFlag hge hdecL hlong
      halign hover hvalidBuf
      hitem0 hitem1 hitem2 hitem3 hitem4 hge7)

#print axioms extractAssumed_copy_longConcrete_pureHvalid_region
#print axioms extractAssumed_copy_longConcrete_pureHvalid_region_fullCode

/-- Path refinements for long type234 copy + dword-aligned content. -/
def extractCopyType234LongPathRegion
    (txBytes : List (BitVec 8)) (items : List EL.RLP.RLPItem) (q : Nat) : Prop :=
  extractSuccess txBytes ∧
    (teerExtractToAddress txBytes).2.2 = (0 : Word) ∧
    2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat ∧
    decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items ∧
    55 < (encode.encodeItems items).length ∧
    7 ≤ items.length ∧
    longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5 + 1 = 8 * q ∧
    8 * q + 16 < txBytes.length

set_option maxRecDepth 8000 in
/-- Bare Assumed footprint under long type234 copy + aligned content. classical-3. -/
theorem extractAssumed_success_flat_copy_type234_long
    (ret spVal txBase lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hcover : txBase.toNat + (8 * q + 16) < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (txBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (hpath : extractCopyType234LongPathRegion txBytes items q)
    (hitem0 : (encode (items[0]'(by
        have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by
        have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by
        have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by
        have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by
        have := hpath.2.2.2.2.2.1; omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨hsuccess, hcopyFlag, hge, hdecL, hlong, hge7, hq_align, hq⟩ := hpath
  let s : ExtractSaved :=
    { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3
      s4 := s4, s5 := s5, s6 := s6, s7 := s7 }
  let spC : Word := spVal + signExtend12 (-80 : BitVec 12)
  have hspC : spC = spVal + signExtend12 (-80 : BitVec 12) := rfl
  have hsra : s.ra = ret := rfl
  have hs0 : s.s0 = s0 := rfl
  have hs1 : s.s1 = s1 := rfl
  have hs2 : s.s2 = s2 := rfl
  have hs3 : s.s3 = s3 := rfl
  have hs4 : s.s4 = s4 := rfl
  have hs5 : s.s5 = s5 := rfl
  have hs6 : s.s6 = s6 := rfl
  have hs7 : s.s7 = s7 := rfl
  simpa only [hsra, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] using
    extractAssumed_copy_longConcrete_pureHvalid_region_fullCode
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items q
      hspC hret htalign htover htvalid hq_align hq hcover hcvalid
      hlen hsuccess hcopyFlag hge hdecL hlong
      halign hover hvalidBuf
      hitem0 hitem1 hitem2 hitem3 hitem4 hge7

#print axioms extractAssumed_success_flat_copy_type234_long


end EvmAsm.Codegen.TxExtractToAddressSpec
