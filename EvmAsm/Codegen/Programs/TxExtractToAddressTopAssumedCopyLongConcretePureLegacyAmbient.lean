/-
  Ambient dual: long legacy copy pure honesty (typeW=0, fields 0..3, content@3).
  Pure on txSlice+loadPtr; bridge to regionBase/bs abs offsets.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressAmbientPureBridge
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyLongLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitLong
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitLongAmbient

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps fullCode extractLinked_mono)
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch txSlice ambientAbsOff loadPtr_add_rel_eq txSlice_length)
open EvmAsm.Codegen.TxExtractToAddressHonesty
open EvmAsm.Codegen.TxExtractToAddressModel
open EvmAsm.Rv64.RLP (rlpItemDecode)
open EvmAsm.EL.RLP

private theorem loadPtr_toNat_eq
    (regionBase loadPtr : Word) (off : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hover : regionBase.toNat + off < 2 ^ 64) :
    loadPtr.toNat = regionBase.toNat + off := by
  have hoffN : off < 2 ^ 64 := by omega
  rw [hptr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffN,
    Nat.mod_eq_of_lt hover]

set_option maxRecDepth 8000 in
/-- Ambient long concrete Assumed copy with pure-discharged hcur/hnext/hlen20/hnext_content/hinb/
    hoff/hover/hls/hll and long walk guards. Residual: hvalid*/hvalid1_*/hdec*/hlover/hlvalid (legacy 0..3). -/
theorem extractAssumed_copy_longConcrete_pure_legacy_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hq_align : ambientAbsOff off
        (longListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length)
    (hcover : regionBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdecL : decodeListItems
        ((txSlice bs off len).drop (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) =
      some items)
    (hlong : 55 < (encode.encodeItems items).length)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidTx0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (hinover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hlover : regionBase.toNat +
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
          longListLol items) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < longListLol items →
      isValidByteAccess (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 + k)) = true)
    (hitem0 : (encode (items[0]'(by
        have := extractSuccess_copy_legacy_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0))) = true)
    (hvalid1_0 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0) + 1)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (longListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0)))
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next0 len0)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_copy_legacy_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1))) = true)
    (hvalid1_1 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1) + 1)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (longListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1)))
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next1 len1)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_copy_legacy_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2))) = true)
    (hvalid1_2 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2) + 1)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (longListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2)))
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next2 len2)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_copy_legacy_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3))) = true)
    (hvalid1_3 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (longListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3)))
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next3 len3)
    :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) := by
  set slice := txSlice bs off len with hslice
  set listOff := (teerTxTypeDispatch slice).2.2.toNat
  set srcOff0 := longListSrcOff listOff items 0
  set srcOff1 := longListSrcOff listOff items 1
  set srcOff2 := longListSrcOff listOff items 2
  set srcOff3 := longListSrcOff listOff items 3
  set absOff0 := ambientAbsOff off srcOff0
  set absOff1 := ambientAbsOff off srcOff1
  set absOff2 := ambientAbsOff off srcOff2
  set absOff3 := ambientAbsOff off srcOff3
  set absListOff := ambientAbsOff off listOff
  set endW := longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch slice).2.2) absListOff
  have hty0 := extractSuccess_type_ok slice hsuccess
  have hlen_sl := txSlice_length bs off len hbound
  have hlenW : lenW.toNat = slice.length := by
    have hspan : len < 2 ^ 64 := by omega
    rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspan, hlen_sl]
  have hbuf : slice.length < 2 ^ 64 := by omega
  have hoffInner : listOff < slice.length := extractSuccess_inner_lt slice hsuccess
  have hencInner : slice.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ hdecL
  have hlp : loadPtr.toNat = regionBase.toNat + off :=
    loadPtr_toNat_eq regionBase loadPtr off hptr (by omega)
  have hover_sl : loadPtr.toNat + slice.length < 2 ^ 64 := by
    rw [hlp, hlen_sl]; omega
  have hbound_enc : (encode.encodeItems items).length < 256 ^ 8 := by
    have hbsLt : (slice.drop listOff).length < 2 ^ 64 := by
      have hle : (slice.drop listOff).length ≤ slice.length := by
        simp only [List.length_drop]; omega
      exact Nat.lt_of_le_of_lt hle hbuf
    exact encodeItems_lt_256pow8_of_buf_lt (slice.drop listOff) items hencInner hlong hbsLt
  have hspan_list : regionBase.toNat + (off + listOff) < 2 ^ 64 := by
    simpa [absListOff, ambientAbsOff] using hinover
  have hptr_sl : (loadPtr + BitVec.ofNat 64 listOff).toNat = loadPtr.toNat + listOff := by
    have hoverL : loadPtr.toNat + listOff < 2 ^ 64 := by omega
    exact toNat_add_ofNat_lt loadPtr listOff hoverL
  have hend_sl : (loadPtr + BitVec.ofNat 64 listOff).toNat +
      (lenW - (teerTxTypeDispatch slice).2.2).toNat < 2 ^ 64 := by
    rw [hptr_sl]
    have hlistLen := listLen_word_eq_drop slice lenW
      (teerTxTypeDispatch slice).2.2 hoffInner hlenW
    have hdrop : (slice.drop listOff).length = slice.length - listOff := by
      simp only [List.length_drop]
    have hencLen := encode_list_long_length items hlong
    have hdropEq : (slice.drop listOff).length = (encode (.list items)).length := by
      rw [hencInner]
    have hlistLen' : (lenW - (teerTxTypeDispatch slice).2.2).toNat =
        (slice.drop listOff).length := by
      simpa [listOff] using hlistLen
    omega
  have hleaf :=
    extractSuccess_long_walkInit_leaf_hyps loadPtr lenW slice hsuccess hlenW
      items hdecL hlong hbuf hptr_sl hend_sl
  obtain ⟨hoff_sl_list, hwi_off1_sl, hlistLen_ne, h_ge_sl, h_ge_f8_sl, hllen_sl,
      h_fits_sl, h_llz_sl, h_min_sl, h_match_sl⟩ := hleaf
  have hlolEq_sl : ((slice[listOff]'hoff_sl_list).zeroExtend 64 - (0xf7 : Word)).toNat =
      longListLol items := by
    have hpfx := long_list_pfx_at slice listOff items hencInner hlong hoff_sl_list
    rw [hpfx]; exact pfx_sub_F7_eq_lol items hlong hbound_enc
  have hlol : longListLol items ≤ 8 :=
    Nat.toBytesBE_length_le (encode.encodeItems items).length 8 hbound_enc
  have hoff_list : absListOff < bs.length := by
    have hrel : listOff < len := by
      have : listOff < slice.length := hoffInner
      rwa [hlen_sl] at this
    simpa [absListOff, ambientAbsOff] using absOff_lt_bs bs off len listOff hbound hrel
  have heq_list :
      bs[absListOff]'hoff_list = slice[listOff]'hoff_sl_list := by
    simp only [absListOff, ambientAbsOff]
    have hrel : listOff < len := by
      have : listOff < slice.length := hoffInner
      rwa [hlen_sl] at this
    exact (txSlice_getElem_eq bs off len listOff hbound hrel hoff_sl_list hoff_list).symm
  have h_ge : ¬ BitVec.ult ((bs[absListOff]'hoff_list).zeroExtend 64)
      (0xc0 : Word) = true := by
    have h := h_ge_sl; rw [← heq_list] at h; exact h
  have h_ge_f8 : ¬ BitVec.ult ((bs[absListOff]'hoff_list).zeroExtend 64)
      (0xf8 : Word) = true := by
    have h := h_ge_f8_sl; rw [← heq_list] at h; exact h
  have hllen : absListOff + 1 +
      ((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)).toNat ≤ bs.length := by
    have h : listOff + 1 +
        ((slice[listOff]'hoff_sl_list).zeroExtend 64 - (0xf7 : Word)).toNat ≤
          slice.length := hllen_sl
    have h' : listOff + 1 +
        ((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)).toNat ≤ len := by
      rw [← heq_list, hlen_sl] at h; exact h
    simp only [absListOff, ambientAbsOff] at h' ⊢
    omega
  have hwi_off1 : absListOff + 1 < bs.length := by
    have hrel : listOff + 1 < len := by
      have : listOff + 1 < slice.length := hwi_off1_sl
      rwa [hlen_sl] at this
    simp only [absListOff, ambientAbsOff]; omega
  have heq_list1 :
      bs[absListOff + 1]'hwi_off1 = slice[listOff + 1]'hwi_off1_sl := by
    have hrel : listOff + 1 < len := by
      have : listOff + 1 < slice.length := hwi_off1_sl
      rwa [hlen_sl] at this
    have hoff_bs1 : off + (listOff + 1) < bs.length := by
      simp only [absListOff, ambientAbsOff] at hwi_off1; omega
    have h := txSlice_getElem_eq bs off len (listOff + 1) hbound hrel hwi_off1_sl hoff_bs1
    simp only [absListOff, ambientAbsOff]
    have habs : off + listOff + 1 = off + (listOff + 1) := by omega
    simpa [habs] using h.symm
  have h_llz : (bs[absListOff + 1]'hwi_off1).zeroExtend 64 ≠ (0 : Word) := by
    have h := h_llz_sl; rw [← heq_list1] at h; exact h
  have hlolEq : ((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)).toNat =
      longListLol items := by rw [heq_list]; exact hlolEq_sl
  have hlover' : regionBase.toNat + (absListOff + 1 +
      ((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 := by
    rw [hlolEq]; simpa [absListOff, ambientAbsOff, listOff] using hlover
  have hlvalid' : ∀ k, k <
      ((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)).toNat →
    isValidByteAccess (regionBase + BitVec.ofNat 64 (absListOff + 1 + k)) = true := by
    intro k hk
    have hk' : k < longListLol items := by rwa [hlolEq] at hk
    simpa [absListOff, ambientAbsOff, listOff] using hlvalid k hk'
  have hlol_byte : ((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
    exact hlolEq.symm ▸ hlol
  have hcur_base :
      loadPtr + BitVec.ofNat 64 listOff =
        regionBase + BitVec.ofNat 64 absListOff := by
    simpa [absListOff, ambientAbsOff] using
      loadPtr_add_rel_eq regionBase loadPtr off listOff hptr hspan_list
  have h_fits : ¬ BitVec.ult
      ((regionBase + BitVec.ofNat 64 absListOff) +
        (lenW - (teerTxTypeDispatch slice).2.2))
      ((regionBase + BitVec.ofNat 64 absListOff) +
        (((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true := by
    have h := h_fits_sl
    rw [← heq_list, hcur_base] at h
    exact h
  have hdrop_take :
      ((bs.drop (absListOff + 1)).take
        ((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)).toNat) =
      ((slice.drop (listOff + 1)).take
        ((slice[listOff]'hoff_sl_list).zeroExtend 64 - (0xf7 : Word)).toNat) := by
    have hroom : listOff + 1 + longListLol items ≤ len := by
      have : listOff + 1 + longListLol items ≤ slice.length := by
        have h := hllen_sl; rw [hlolEq_sl] at h; exact h
      rwa [hlen_sl] at this
    have hdt := txSlice_drop_take bs off len (listOff + 1) (longListLol items) (by omega)
    -- hdt: (slice.drop (listOff+1)).take lol = (bs.drop (off+(listOff+1))).take lol
    have hassoc : absListOff + 1 = off + (listOff + 1) := by
      simp only [absListOff, ambientAbsOff]; omega
    have hb : (bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word) =
        (slice[listOff]'hoff_sl_list).zeroExtend 64 - (0xf7 : Word) := by
      rw [heq_list]
    have hlolN :
        ((slice[listOff]'hoff_sl_list).zeroExtend 64 - (0xf7 : Word)).toNat =
          longListLol items := hlolEq_sl
    calc
      (bs.drop (absListOff + 1)).take
          ((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)).toNat
          = (bs.drop (off + (listOff + 1))).take
              ((slice[listOff]'hoff_sl_list).zeroExtend 64 - (0xf7 : Word)).toNat := by
            rw [hassoc, hb]
      _ = (bs.drop (off + (listOff + 1))).take (longListLol items) := by rw [hlolN]
      _ = (slice.drop (listOff + 1)).take (longListLol items) := hdt.symm
      _ = (slice.drop (listOff + 1)).take
            ((slice[listOff]'hoff_sl_list).zeroExtend 64 - (0xf7 : Word)).toNat := by
          rw [hlolN]
  have h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
      ((bs.drop (absListOff + 1)).take
        ((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)).toNat)))
      (56 : Word) = true := by
    rw [hdrop_take]
    exact h_min_sl
  have h_match :
      ((regionBase + BitVec.ofNat 64 absListOff) +
          (((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE
          ((bs.drop (absListOff + 1)).take
            ((bs[absListOff]'hoff_list).zeroExtend 64 - (0xf7 : Word)).toNat))
      = (regionBase + BitVec.ofNat 64 absListOff) +
          (lenW - (teerTxTypeDispatch slice).2.2) := by
    have h := h_match_sl
    have hlo : (teerTxTypeDispatch slice).2.2.toNat = listOff := rfl
    simp only [hlo] at h
    rw [hcur_base] at h
    -- Rewrite goal bs-bytes to slice-bytes to match h
    simp only [heq_list]
    have hdt :
        (bs.drop (absListOff + 1)).take
          ((slice[listOff]'hoff_sl_list).zeroExtend 64 - (0xf7 : Word)).toNat =
        (slice.drop (listOff + 1)).take
          ((slice[listOff]'hoff_sl_list).zeroExtend 64 - (0xf7 : Word)).toNat := by
      have hroom : listOff + 1 + longListLol items ≤ len := by
        have : listOff + 1 + longListLol items ≤ slice.length := by
          have hh := hllen_sl; rw [hlolEq_sl] at hh; exact hh
        rwa [hlen_sl] at this
      have hdt0 := txSlice_drop_take bs off len (listOff + 1) (longListLol items) (by omega)
      have hassoc : absListOff + 1 = off + (listOff + 1) := by
        simp only [absListOff, ambientAbsOff]; omega
      calc
        (bs.drop (absListOff + 1)).take
            ((slice[listOff]'hoff_sl_list).zeroExtend 64 - (0xf7 : Word)).toNat
            = (bs.drop (off + (listOff + 1))).take (longListLol items) := by
              rw [hassoc, hlolEq_sl]
        _ = (slice.drop (listOff + 1)).take (longListLol items) := hdt0.symm
        _ = (slice.drop (listOff + 1)).take
              ((slice[listOff]'hoff_sl_list).zeroExtend 64 - (0xf7 : Word)).toNat := by
            rw [hlolEq_sl]
    rw [hdt]
    exact h
  have hhoff :=
    extractSuccess_copy_legacy_hoff_srcOff_long slice hsuccess hcopyFlag htype0
      items hdecL hlong
  have hhover :=
    extractSuccess_copy_legacy_hover_srcOff_long slice loadPtr hsuccess hcopyFlag htype0
      items hdecL hlong hover_sl
  have hlenItems :=
    extractSuccess_copy_legacy_items_length_long slice hsuccess hcopyFlag htype0
      items hdecL hlong
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hfields02 :=
    extractSuccess_copy_legacy_hnext_fields02_long slice hsuccess hcopyFlag htype0
      items hdecL hlong
  have hoverEnd :
      regionBase.toNat +
        (off + (listOff + 1 + longListLol items +
          (encode.encodeItems items).length)) < 2 ^ 64 := by
    have hdrop : (slice.drop listOff).length = slice.length - listOff := by
      simp only [List.length_drop]
    have hencLen := encode_list_long_length items hlong
    have hdropEq : (slice.drop listOff).length = (encode (.list items)).length := by
      rw [hencInner]
    have hpay : longListPayloadLen items = (encode.encodeItems items).length := rfl
    have hsum : listOff + (1 + longListLol items + (encode.encodeItems items).length) =
        slice.length := by
      have : listOff + (slice.drop listOff).length = slice.length := by
        have hle : listOff ≤ slice.length := Nat.le_of_lt hoffInner
        omega
      calc
        listOff + (1 + longListLol items + (encode.encodeItems items).length)
            = listOff + (1 + longListLol items + longListPayloadLen items) := by
              rw [hpay]
        _ = listOff + (encode (.list items)).length := by rw [← hencLen]
        _ = listOff + (slice.drop listOff).length := by rw [← hdropEq]
        _ = slice.length := this
    have hover' : regionBase.toNat + off + slice.length < 2 ^ 64 := by
      rw [hlp] at hover_sl; omega
    have : regionBase.toNat +
        (off + (listOff + 1 + longListLol items +
          (encode.encodeItems items).length)) =
        regionBase.toNat + off + slice.length := by
      omega
    omega
  have hend_sl_eq :
      longWalkEndAmbient loadPtr (lenW - (teerTxTypeDispatch slice).2.2) listOff =
        longListEndPtr loadPtr listOff items := by
    simpa [longWalkEndAmbient, longListEndPtr, listOff] using
      (longWalkEnd_eq_longListEndPtr loadPtr lenW slice items hsuccess hlenW
        hdecL hlong hover_sl)
  have hendEq :
      endW = regionBase + BitVec.ofNat 64
        (ambientAbsOff off (listOff + 1 + longListLol items +
          (encode.encodeItems items).length)) := by
    have hend_bridge :=
      longWalkEnd_loadPtr_eq regionBase loadPtr
        (lenW - (teerTxTypeDispatch slice).2.2) off listOff hptr hspan_list
    have hptr_end :=
      loadPtr_add_rel_eq regionBase loadPtr off
        (listOff + 1 + longListLol items + (encode.encodeItems items).length)
        hptr hoverEnd
    simp only [endW, absListOff, longListEndPtr] at hend_sl_eq hend_bridge ⊢
    calc
      longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch slice).2.2)
          (ambientAbsOff off listOff)
          = longWalkEndAmbient loadPtr (lenW - (teerTxTypeDispatch slice).2.2) listOff :=
            hend_bridge.symm
      _ = loadPtr + BitVec.ofNat 64
            (listOff + 1 + longListLol items + (encode.encodeItems items).length) :=
            hend_sl_eq
      _ = regionBase + BitVec.ofNat 64
            (ambientAbsOff off
              (listOff + 1 + longListLol items +
                (encode.encodeItems items).length)) := by
          simpa [ambientAbsOff] using hptr_end
  have hspan_src0 : regionBase.toNat +
      (off + (listOff + 1 + longListLol items)) < 2 ^ 64 := by
    have h0 := hhover.1
    simp only [longListSrcOff_zero] at h0
    omega
  have hcur :
      longWalkCursorAmbient regionBase bs absListOff hoff_list =
        regionBase + BitVec.ofNat 64 absOff0 := by
    simpa [absListOff, absOff0, srcOff0, listOff] using
      hcur_ambient_long_srcOff0 regionBase loadPtr bs off len listOff items
        hptr hbound hencInner hlong hbound_enc hoff_sl_list hoff_list
        hspan_list hspan_src0
  have hhnext :=
    extractSuccess_copy_legacy_hnext_hlen20_srcOff_long slice loadPtr hsuccess
      hcopyFlag htype0 items hdecL hlong
      hitem0 hitem1 hitem2
      hhover.1 hhover.2.1 hhover.2.2.1
      hhover.2.1 hhover.2.2.1 hhover.2.2.2
  have hoff0_sl : srcOff0 < slice.length := hhoff.1
  have hoff1_sl : srcOff1 < slice.length := hhoff.2.1
  have hoff2_sl : srcOff2 < slice.length := hhoff.2.2.1
  have hoff3_sl : srcOff3 < slice.length := hhoff.2.2.2
  have hspan0a : regionBase.toNat + (off + srcOff0) < 2 ^ 64 := by
    have hs := hhover.1; omega
  have hspan1a : regionBase.toNat + (off + srcOff1) < 2 ^ 64 := by
    have hs := hhover.2.1; omega
  have hspan2a : regionBase.toNat + (off + srcOff2) < 2 ^ 64 := by
    have hs := hhover.2.2.1; omega
  have hspan3a : regionBase.toNat + (off + srcOff3) < 2 ^ 64 := by
    have hs := hhover.2.2.2; omega
  have hroom0 : srcOff0 + 1 < slice.length :=
    longListSrcOff_succ_room slice listOff items 0 hencInner hlong (by omega)
  have hroom1 : srcOff1 + 1 < slice.length :=
    longListSrcOff_succ_room slice listOff items 1 hencInner hlong (by omega)
  have hroom2 : srcOff2 + 1 < slice.length :=
    longListSrcOff_succ_room slice listOff items 2 hencInner hlong (by omega)
  have hge2_3 : 2 ≤ (encode (items[3]'hn3)).length :=
    extractSuccess_copy_legacy_field3_encode_ge_two_long slice hsuccess hcopyFlag htype0
      items hdecL hlong hn3
  have hroom3 : srcOff3 + 1 < slice.length :=
    hss_room_of_encode_ge_two_long slice listOff items 3 hencInner hlong hn3 hge2_3
  have hnext1 : ∀ (next0 len0 : Word),
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0) endW
        next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 absOff1 := by
    simpa [absOff0, absOff1, srcOff0, srcOff1, listOff, endW, absListOff] using
      packaging_hnext_ambient_field_long regionBase loadPtr bs off len listOff items 0 1
        endW hptr hbound hencInner hlong hn0 hitem0 hoff0_sl hspan0a hspan1a hroom0
        (fun n l hd => hhnext.1 endW n l hd)
  have hnext2 : ∀ (next1 len1 : Word),
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1) endW
        next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 absOff2 := by
    simpa [absOff1, absOff2, srcOff1, srcOff2, listOff, endW, absListOff] using
      packaging_hnext_ambient_field_long regionBase loadPtr bs off len listOff items 1 2
        endW hptr hbound hencInner hlong hn1 hitem1 hoff1_sl hspan1a hspan2a hroom1
        (fun n l hd => hhnext.2.1 endW n l hd)
  have hnext3 : ∀ (next2 len2 : Word),
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2) endW
        next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 absOff3 := by
    simpa [absOff2, absOff3, srcOff2, srcOff3, listOff, endW, absListOff] using
      packaging_hnext_ambient_field_long regionBase loadPtr bs off len listOff items 2 3
        endW hptr hbound hencInner hlong hn2 hitem2 hoff2_sl hspan2a hspan3a hroom2
        (fun n l hd => hhnext.2.2.1 endW n l hd)
  have hlen20 : ∀ (next3 len3 : Word),
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3) endW
        next3 len3 →
      len3 = (20 : Word) := by
    simpa [absOff3, srcOff3, listOff, endW, absListOff] using
      hlen20_ambient_of_slice_long regionBase loadPtr bs off len listOff items 3 endW
        hptr hbound hencInner hlong hn3 hitem3 hoff3_sl hspan3a hroom3
        (fun n l hd => hhnext.2.2.2 endW n l hd)
  have hq_abs : ambientAbsOff off srcOff3 + 1 = 8 * q := by
    simpa [srcOff3, listOff, ambientAbsOff] using hq_align
  have hnext_sl_content : ∀ (next3 len3 : Word),
      rlpItemDecode slice srcOff3 (loadPtr + BitVec.ofNat 64 srcOff3) endW
        next3 len3 →
      next3 = loadPtr + BitVec.ofNat 64 srcOff3 + (1 : Word) + (20 : Word) := by
    intro n l hd
    let contentPtrSl := loadPtr + BitVec.ofNat 64 srcOff3 + (1 : Word)
    have hcontentPtr : contentPtrSl =
        loadPtr + BitVec.ofNat 64 srcOff3 + (1 : Word) := rfl
    have hsrc : srcOff3 = longListSrcOff listOff items 3 := rfl
    have hc := extractSuccess_copy_legacy_hnext_content_long slice loadPtr contentPtrSl
      srcOff3 hsuccess hcopyFlag htype0 items hdecL hlong hsrc hcontentPtr
    simpa [contentPtrSl, BitVec.add_assoc] using hc endW n l hd
  have hcover20 : regionBase.toNat + 8 * q + 20 < 2 ^ 64 := by omega
  have hnext_content : ∀ (next3 len3 : Word),
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3) endW
        next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 (8 * q) + (20 : Word) := by
    simpa [absOff3, srcOff3, listOff, endW, absListOff] using
      hnext_content_ambient_of_slice_long regionBase loadPtr bs off len listOff items 3 q endW
        hptr hbound hencInner hlong hn3 hitem3 hoff3_sl hspan3a hroom3 hq_abs hcover20
        hnext_sl_content
  have hinb0 :=
    hinb_ambient_long_list_end regionBase off listOff items 0 hn0 hoverEnd endW hendEq
  have hinb1 :=
    hinb_ambient_long_list_end regionBase off listOff items 1 hn1 hoverEnd endW hendEq
  have hinb2 :=
    hinb_ambient_long_list_end regionBase off listOff items 2 hn2 hoverEnd endW hendEq
  have hinb3 :=
    hinb_ambient_long_list_end regionBase off listOff items 3 hn3 hoverEnd endW hendEq
  have hoff0 : absOff0 < bs.length := by
    have hrel : srcOff0 < len := by
      have : srcOff0 < slice.length := hhoff.1
      rwa [hlen_sl] at this
    simpa [absOff0, srcOff0] using absOff_lt_bs bs off len srcOff0 hbound hrel
  have hover0 : regionBase.toNat + absOff0 < 2 ^ 64 := by
    simpa [absOff0, ambientAbsOff, srcOff0] using hspan0a
  have hoff1 : absOff1 < bs.length := by
    have hrel : srcOff1 < len := by
      have : srcOff1 < slice.length := hhoff.2.1
      rwa [hlen_sl] at this
    simpa [absOff1, srcOff1] using absOff_lt_bs bs off len srcOff1 hbound hrel
  have hover1 : regionBase.toNat + absOff1 < 2 ^ 64 := by
    simpa [absOff1, ambientAbsOff, srcOff1] using hspan1a
  have hoff2 : absOff2 < bs.length := by
    have hrel : srcOff2 < len := by
      have : srcOff2 < slice.length := hhoff.2.2.1
      rwa [hlen_sl] at this
    simpa [absOff2, srcOff2] using absOff_lt_bs bs off len srcOff2 hbound hrel
  have hover2 : regionBase.toNat + absOff2 < 2 ^ 64 := by
    simpa [absOff2, ambientAbsOff, srcOff2] using hspan2a
  have hoff3 : absOff3 < bs.length := by
    have hrel : srcOff3 < len := by
      have : srcOff3 < slice.length := hhoff.2.2.2
      rwa [hlen_sl] at this
    simpa [absOff3, srcOff3] using absOff_lt_bs bs off len srcOff3 hbound hrel
  have hover3 : regionBase.toNat + absOff3 < 2 ^ 64 := by
    simpa [absOff3, ambientAbsOff, srcOff3] using hspan3a
  have hss0 :=
    hss_ambient_of_long_list_field regionBase loadPtr bs off len listOff items 0
      hptr hbound hencInner hlong hn0 hitem0 hoff0_sl hover (Or.inl hfields02.1)
      hvalid1_0 hoff0
  have hss1 :=
    hss_ambient_of_long_list_field regionBase loadPtr bs off len listOff items 1
      hptr hbound hencInner hlong hn1 hitem1 hoff1_sl hover (Or.inl hfields02.2.1)
      hvalid1_1 hoff1
  have hss2 :=
    hss_ambient_of_long_list_field regionBase loadPtr bs off len listOff items 2
      hptr hbound hencInner hlong hn2 hitem2 hoff2_sl hover (Or.inl hfields02.2.2)
      hvalid1_2 hoff2
  have hss3 :=
    hss_ambient_of_long_list_field regionBase loadPtr bs off len listOff items 3
      hptr hbound hencInner hlong hn3 hitem3 hoff3_sl hover (Or.inr hge2_3)
      hvalid1_3 hoff3
  have hls0 :
      ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + j)) = true := by
    intro hlo hhi
    have heq : bs[absOff0]'hoff0 = slice[srcOff0]'hoff0_sl := by
      simp only [absOff0, ambientAbsOff, srcOff0]
      have hrel : srcOff0 < len := by
        have : srcOff0 < slice.length := hoff0_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff0 hbound hrel hoff0_sl hoff0).symm
    have hlo' := hlo; rw [heq] at hlo'
    have hhi' := hhi; rw [heq] at hhi'
    exact hls_vacuous_of_long_list_item slice listOff items 0
      hencInner hlong hn0 hitem0 hoff0_sl hlo' hhi'
  have hll0 :
      ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + j)) = true := by
    intro hgeF8
    have heq : bs[absOff0]'hoff0 = slice[srcOff0]'hoff0_sl := by
      simp only [absOff0, ambientAbsOff, srcOff0]
      have hrel : srcOff0 < len := by
        have : srcOff0 < slice.length := hoff0_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff0 hbound hrel hoff0_sl hoff0).symm
    have h' := hgeF8; rw [heq] at h'
    exact hll_vacuous_of_long_list_item slice listOff items 0
      hencInner hlong hn0 hitem0 hoff0_sl h'
  have hls1 :
      ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + j)) = true := by
    intro hlo hhi
    have heq : bs[absOff1]'hoff1 = slice[srcOff1]'hoff1_sl := by
      simp only [absOff1, ambientAbsOff, srcOff1]
      have hrel : srcOff1 < len := by
        have : srcOff1 < slice.length := hoff1_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff1 hbound hrel hoff1_sl hoff1).symm
    have hlo' := hlo; rw [heq] at hlo'
    have hhi' := hhi; rw [heq] at hhi'
    exact hls_vacuous_of_long_list_item slice listOff items 1
      hencInner hlong hn1 hitem1 hoff1_sl hlo' hhi'
  have hll1 :
      ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + j)) = true := by
    intro hgeF8
    have heq : bs[absOff1]'hoff1 = slice[srcOff1]'hoff1_sl := by
      simp only [absOff1, ambientAbsOff, srcOff1]
      have hrel : srcOff1 < len := by
        have : srcOff1 < slice.length := hoff1_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff1 hbound hrel hoff1_sl hoff1).symm
    have h' := hgeF8; rw [heq] at h'
    exact hll_vacuous_of_long_list_item slice listOff items 1
      hencInner hlong hn1 hitem1 hoff1_sl h'
  have hls2 :
      ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + j)) = true := by
    intro hlo hhi
    have heq : bs[absOff2]'hoff2 = slice[srcOff2]'hoff2_sl := by
      simp only [absOff2, ambientAbsOff, srcOff2]
      have hrel : srcOff2 < len := by
        have : srcOff2 < slice.length := hoff2_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff2 hbound hrel hoff2_sl hoff2).symm
    have hlo' := hlo; rw [heq] at hlo'
    have hhi' := hhi; rw [heq] at hhi'
    exact hls_vacuous_of_long_list_item slice listOff items 2
      hencInner hlong hn2 hitem2 hoff2_sl hlo' hhi'
  have hll2 :
      ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + j)) = true := by
    intro hgeF8
    have heq : bs[absOff2]'hoff2 = slice[srcOff2]'hoff2_sl := by
      simp only [absOff2, ambientAbsOff, srcOff2]
      have hrel : srcOff2 < len := by
        have : srcOff2 < slice.length := hoff2_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff2 hbound hrel hoff2_sl hoff2).symm
    have h' := hgeF8; rw [heq] at h'
    exact hll_vacuous_of_long_list_item slice listOff items 2
      hencInner hlong hn2 hitem2 hoff2_sl h'
  have hls3 :
      ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + j)) = true := by
    intro hlo hhi
    have heq : bs[absOff3]'hoff3 = slice[srcOff3]'hoff3_sl := by
      simp only [absOff3, ambientAbsOff, srcOff3]
      have hrel : srcOff3 < len := by
        have : srcOff3 < slice.length := hoff3_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff3 hbound hrel hoff3_sl hoff3).symm
    have hlo' := hlo; rw [heq] at hlo'
    have hhi' := hhi; rw [heq] at hhi'
    exact hls_vacuous_of_long_list_item slice listOff items 3
      hencInner hlong hn3 hitem3 hoff3_sl hlo' hhi'
  have hll3 :
      ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + j)) = true := by
    intro hgeF8
    have heq : bs[absOff3]'hoff3 = slice[srcOff3]'hoff3_sl := by
      simp only [absOff3, ambientAbsOff, srcOff3]
      have hrel : srcOff3 < len := by
        have : srcOff3 < slice.length := hoff3_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff3 hbound hrel hoff3_sl hoff3).symm
    have h' := hgeF8; rw [heq] at h'
    exact hll_vacuous_of_long_list_item slice listOff items 3
      hencInner hlong hn3 hitem3 hoff3_sl h'
  have hoff := hoff_list
  have hspan : regionBase.toNat + (off + listOff) < 2 ^ 64 := hspan_list
  exact extractAssumed_copy_of_front_long_concrete_legacy_region_ambient
    sp0 spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len
    absOff0 absOff1 absOff2 absOff3 q
    hspC hret hoff hcur htype0 hsalign
    hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
    hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    hnext1 hnext2 hnext3 hlen20 hnext_content
    hq hcover hcvalid
    htalign htover htvalid hlen hty0 hover hvalidTx0
    hptr hbound hspan hoff hinover hinvalid hlistLen_ne h_ge h_ge_f8 hllen hlover'
    hlvalid' hwi_off1 h_fits h_llz h_min h_match hlol_byte

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_longConcrete_pure_legacy_ambient_fullCode
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hq_align : ambientAbsOff off
        (longListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length)
    (hcover : regionBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdecL : decodeListItems
        ((txSlice bs off len).drop (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) =
      some items)
    (hlong : 55 < (encode.encodeItems items).length)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidTx0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (hinover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hlover : regionBase.toNat +
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
          longListLol items) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < longListLol items →
      isValidByteAccess (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 + k)) = true)
    (hitem0 : (encode (items[0]'(by
        have := extractSuccess_copy_legacy_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0))) = true)
    (hvalid1_0 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0) + 1)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (longListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0)))
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next0 len0)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_copy_legacy_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1))) = true)
    (hvalid1_1 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1) + 1)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (longListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1)))
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next1 len1)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_copy_legacy_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2))) = true)
    (hvalid1_2 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2) + 1)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (longListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2)))
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next2 len2)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_copy_legacy_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3))) = true)
    (hvalid1_3 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (longListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (longListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3)))
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next3 len3)
    :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_copy_longConcrete_pure_legacy_ambient sp0 spC s
      regionBase loadPtr lenW toBuf isCreationPtr bs off len items q
      hq_align hq hcover hcvalid
      hspC hret htalign htover htvalid hlen hptr hbound hsuccess hcopyFlag htype0 hdecL hlong
      hsalign hover hvalidTx0 hinover hinvalid hlover hlvalid
      hitem0 hvalid0 hvalid1_0 hdec0
      hitem1 hvalid1 hvalid1_1 hdec1
      hitem2 hvalid2 hvalid1_2 hdec2
      hitem3 hvalid3 hvalid1_3 hdec3
     )

#print axioms extractAssumed_copy_longConcrete_pure_legacy_ambient
#print axioms extractAssumed_copy_longConcrete_pure_legacy_ambient_fullCode

end EvmAsm.Codegen.TxExtractToAddressSpec
