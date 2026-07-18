/-
  Wire pure honesty into long concrete Assumed creation:
  longListSrcOff + hcur/hnext/hcre/hinb/hoff/hover/hls/hll + long walk guards.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedLongConcrete
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
open EvmAsm.Rv64.RLP (rlpItemDecode)
open EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
/-- Long concrete Assumed creation with pure-discharged hcur/hnext/hcre/hinb/hoff/hover/hls/hll
    and long walk guards. Residual: hvalid*/hvalid1_*/hdec*/hlover/hlvalid RAM. -/
theorem extractAssumed_creation_longConcrete_pure
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
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0)) = true)
    (hvalid1_0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0 + 1)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next0 len0)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1)) = true)
    (hvalid1_1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1 + 1)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next1 len1)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2)) = true)
    (hvalid1_2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2 + 1)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next2 len2)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3)) = true)
    (hvalid1_3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3 + 1)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next3 len3)
    (hitem4 : (encode (items[4]'(by
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid4 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4)) = true)
    (hvalid1_4 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4 + 1)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next4 len4)
    (hitem5 : (encode (items[5]'(by
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid5 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5)) = true)
    (hvalid1_5 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5 + 1)) = true)
    (hdec5 : ∃ next5 len5 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next5 len5)
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
  have hptr : (txBase + BitVec.ofNat 64 listOff).toNat = txBase.toNat + listOff :=
    toNat_add_ofNat_lt txBase listOff hinover
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
  have hlover' : txBase.toNat + (listOff + 1 +
      ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 := by
    rw [hlolEq]
    simpa [listOff] using hlover
  have hlvalid' : ∀ k, k < ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (txBase + BitVec.ofNat 64 (listOff + 1 + k)) = true := by
    intro k hk
    have hk' : k < longListLol items := by rwa [hlolEq] at hk
    simpa [listOff] using hlvalid k hk'
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
    extractSuccess_creation_type234_hoff_srcOff_long txBytes hsuccess hcreFlag hge
      items hdecL hlong
  have hhover :=
    extractSuccess_creation_type234_hover_srcOff_long txBytes txBase hsuccess hcreFlag hge
      items hdecL hlong hover
  have hlenItems :=
    extractSuccess_creation_type234_items_length_long txBytes hsuccess hcreFlag hge
      items hdecL hlong
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hn4 : (4 : Nat) < items.length := by omega
  have hn5 : (5 : Nat) < items.length := by omega
  have hfields04 :=
    extractSuccess_creation_type234_hnext_fields04_long txBytes hsuccess hcreFlag hge
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
    extractSuccess_creation_type234_hnext_hcre_srcOff_long txBytes txBase hsuccess
      hcreFlag hge items hdecL hlong
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
  have hcre : ∀ (next5 len5 : Word),
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5) endW next5 len5 →
      len5 = (0 : Word) :=
    fun n l hd => hhnext.2.2.2.2.2 endW n l hd
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
  have hss0 :=
    hss_of_long_list_item txBytes txBase listOff items 0 hencInner hlong hn0 hitem0
      hhoff.1 hover (Or.inl hfields04.1) hvalid1_0
  have hss1 :=
    hss_of_long_list_item txBytes txBase listOff items 1 hencInner hlong hn1 hitem1
      hhoff.2.1 hover (Or.inl hfields04.2.1) hvalid1_1
  have hss2 :=
    hss_of_long_list_item txBytes txBase listOff items 2 hencInner hlong hn2 hitem2
      hhoff.2.2.1 hover (Or.inl hfields04.2.2.1) hvalid1_2
  have hss3 :=
    hss_of_long_list_item txBytes txBase listOff items 3 hencInner hlong hn3 hitem3
      hhoff.2.2.2.1 hover (Or.inl hfields04.2.2.2.1) hvalid1_3
  have hss4 :=
    hss_of_long_list_item txBytes txBase listOff items 4 hencInner hlong hn4 hitem4
      hhoff.2.2.2.2.1 hover (Or.inl hfields04.2.2.2.2) hvalid1_4
  have hss5 :=
    hss_of_long_list_item txBytes txBase listOff items 5 hencInner hlong hn5 hitem5
      hhoff.2.2.2.2.2 hover (Or.inl (by omega)) hvalid1_5
  exact extractAssumed_creation_under_honesty_of_decode_long_concrete
    sp0 spC s txBase lenW toBuf isCreationPtr txBytes
    srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 srcOff5
    hspC hret hne0 hne1 halign
    hhoff.1 hhover.1 hvalid0 hss0
    (hls_vacuous_of_long_list_item txBytes listOff items 0 hencInner hlong hn0 hitem0 hhoff.1)
    (hll_vacuous_of_long_list_item txBytes listOff items 0 hencInner hlong hn0 hitem0 hhoff.1)
    hdec0 hinb0
    hhoff.2.1 hhover.2.1 hvalid1 hss1
    (hls_vacuous_of_long_list_item txBytes listOff items 1 hencInner hlong hn1 hitem1 hhoff.2.1)
    (hll_vacuous_of_long_list_item txBytes listOff items 1 hencInner hlong hn1 hitem1 hhoff.2.1)
    hdec1 hinb1
    hhoff.2.2.1 hhover.2.2.1 hvalid2 hss2
    (hls_vacuous_of_long_list_item txBytes listOff items 2 hencInner hlong hn2 hitem2 hhoff.2.2.1)
    (hll_vacuous_of_long_list_item txBytes listOff items 2 hencInner hlong hn2 hitem2 hhoff.2.2.1)
    hdec2 hinb2
    hhoff.2.2.2.1 hhover.2.2.2.1 hvalid3 hss3
    (hls_vacuous_of_long_list_item txBytes listOff items 3 hencInner hlong hn3 hitem3 hhoff.2.2.2.1)
    (hll_vacuous_of_long_list_item txBytes listOff items 3 hencInner hlong hn3 hitem3 hhoff.2.2.2.1)
    hdec3 hinb3
    hhoff.2.2.2.2.1 hhover.2.2.2.2.1 hvalid4 hss4
    (hls_vacuous_of_long_list_item txBytes listOff items 4 hencInner hlong hn4 hitem4 hhoff.2.2.2.2.1)
    (hll_vacuous_of_long_list_item txBytes listOff items 4 hencInner hlong hn4 hitem4 hhoff.2.2.2.2.1)
    hdec4 hinb4
    hhoff.2.2.2.2.2 hhover.2.2.2.2.2 hvalid5 hss5
    (hls_vacuous_of_long_list_item txBytes listOff items 5 hencInner hlong hn5 hitem5 hhoff.2.2.2.2.2)
    (hll_vacuous_of_long_list_item txBytes listOff items 5 hencInner hlong hn5 hitem5 hhoff.2.2.2.2.2)
    hdec5 hinb5
    hnext1 hnext2 hnext3 hnext4 hnext5 hcre
    htalign htover htvalid hlen hty0 hover hvalidTx0
    hoff hcur hinover hinvalid hlistLen_ne h_ge h_ge_f8 hllen hlover' hlvalid' hwi_off1
    h_fits h_llz h_min h_match hlol

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_longConcrete_pure_fullCode
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
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0)) = true)
    (hvalid1_0 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0 + 1)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next0 len0)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1)) = true)
    (hvalid1_1 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1 + 1)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next1 len1)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2)) = true)
    (hvalid1_2 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2 + 1)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next2 len2)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3)) = true)
    (hvalid1_3 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3 + 1)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next3 len3)
    (hitem4 : (encode (items[4]'(by
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid4 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4)) = true)
    (hvalid1_4 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4 + 1)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next4 len4)
    (hitem5 : (encode (items[5]'(by
        have := extractSuccess_creation_type234_items_length_long txBytes hsuccess
          hcreFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hvalid5 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5)) = true)
    (hvalid1_5 : isValidByteAccess (txBase + BitVec.ofNat 64
      (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5 + 1)) = true)
    (hdec5 : ∃ next5 len5 : Word,
      rlpItemDecode txBytes
        (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5)
        (txBase + BitVec.ofNat 64
          (longListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5))
        (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) next5 len5)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_creation_longConcrete_pure sp0 spC s
      txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag hge hdecL hlong
      halign hover hvalidTx0 hinover hinvalid hlover hlvalid
      hitem0 hvalid0 hvalid1_0 hdec0
      hitem1 hvalid1 hvalid1_1 hdec1
      hitem2 hvalid2 hvalid1_2 hdec2
      hitem3 hvalid3 hvalid1_3 hdec3
      hitem4 hvalid4 hvalid1_4 hdec4
      hitem5 hvalid5 hvalid1_5 hdec5
      hge7)

#print axioms extractAssumed_creation_longConcrete_pure
#print axioms extractAssumed_creation_longConcrete_pure_fullCode

end EvmAsm.Codegen.TxExtractToAddressSpec
