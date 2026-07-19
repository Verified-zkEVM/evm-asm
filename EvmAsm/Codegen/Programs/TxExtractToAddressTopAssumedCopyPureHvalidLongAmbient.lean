/-
  Ambient long type234 copy: discharge hdec*/hvalid*/hlover/hlvalid via slice pure +
  bridges + validByteRange on regionBase. Residual path flags + hitem0..4 + hq_align.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressAmbientPureBridge
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyLongConcretePureAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitLongAmbient

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.DualReadByteScan (validByteRange isValidByteAccess_of_validByteRange)
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

/-- Lift slice hdec at longListSrcOff to abs decode at regionBase (item short-encode). -/
private theorem hdec_ambient_field_long'
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (k : Nat) (endW : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hlong : 55 < (encode.encodeItems items).length)
    (hn : k < items.length)
    (hitemLe : (encode (items[k]'hn)).length ≤ 55)
    (hoff_sl : longListSrcOff listOff items k < (txSlice bs off len).length)
    (hspan_src : regionBase.toNat +
      ambientAbsOff off (longListSrcOff listOff items k) < 2 ^ 64)
    (hoverEnd_sl : loadPtr.toNat +
      (listOff + 1 + longListLol items + (encode.encodeItems items).length) < 2 ^ 64)
    (hoverEnd_abs : regionBase.toNat +
      ambientAbsOff off (listOff + 1 + longListLol items +
        (encode.encodeItems items).length) < 2 ^ 64)
    (hend : endW =
      regionBase + BitVec.ofNat 64
        (ambientAbsOff off (listOff + 1 + longListLol items +
          (encode.encodeItems items).length))) :
    ∃ n l : Word,
      rlpItemDecode bs (ambientAbsOff off (longListSrcOff listOff items k))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff listOff items k)))
        endW n l := by
  set slice := txSlice bs off len
  set srcOff := longListSrcOff listOff items k
  set absOff := ambientAbsOff off srcOff
  set endSl := longListEndPtr loadPtr listOff items
  have hlen_sl := txSlice_length bs off len hbound
  have hrel : srcOff < len := by
    have : srcOff < slice.length := hoff_sl
    rwa [hlen_sl] at this
  have hdec_sl :=
    hdec_long_list_end slice loadPtr listOff items k henc hlong hn hitemLe hoff_sl
      hoverEnd_sl endSl rfl
  obtain ⟨n, l, hd⟩ := hdec_sl
  have hshort_form :=
    hshort_abs_at_long_list_field bs off len listOff items k hbound henc hlong hn
      hitemLe hoff_sl
  have hshort_sl :
      ¬ (∃ b, slice[srcOff]? = some b ∧
        ((¬ BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
            BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true) ∨
          ¬ BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true)) := by
    intro ⟨b, hb, hlongF⟩
    have hb' : bs[off + srcOff]? = some b := by
      rw [← txSlice_getElem? bs off len srcOff hbound hrel]; exact hb
    exact hshort_form ⟨b, by simpa [ambientAbsOff] using hb', hlongF⟩
  have hd_abs :
      rlpItemDecode bs absOff
        (loadPtr + BitVec.ofNat 64 srcOff) endSl n l := by
    simpa [absOff, srcOff, slice] using
      rlpItemDecode_txSlice_to_abs_short bs off len srcOff
        (loadPtr + BitVec.ofNat 64 srcOff) endSl n l hbound hrel hd hshort_sl
  have hcur_eq :
      loadPtr + BitVec.ofNat 64 srcOff =
        regionBase + BitVec.ofNat 64 absOff := by
    simpa [absOff, ambientAbsOff, srcOff] using
      loadPtr_add_rel_eq regionBase loadPtr off srcOff hptr (by
        simpa [absOff, ambientAbsOff, srcOff] using hspan_src)
  have hend_eq : endSl = endW := by
    simp only [endSl, longListEndPtr, hend, ambientAbsOff]
    exact loadPtr_add_rel_eq regionBase loadPtr off
      (listOff + 1 + longListLol items + (encode.encodeItems items).length)
      hptr hoverEnd_abs
  refine ⟨n, l, ?_⟩
  rw [← hcur_eq, ← hend_eq]
  exact hd_abs

set_option maxRecDepth 8000 in
/-- Ambient long concrete Assumed copy; hdec+hvalid+hlover/hlvalid from pure+validByteRange.
    Residual path: copy/type234/long/hq_align + hitem0..5. -/
theorem extractAssumed_copy_longConcrete_pureHvalid_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hq_align : ambientAbsOff off
        (longListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1 =
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
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdecL : decodeListItems
        ((txSlice bs off len).drop (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) =
      some items)
    (hlong : 55 < (encode.encodeItems items).length)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hitem0 : (encode (items[0]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem5 : (encode (items[5]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
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
  set srcOff4 := longListSrcOff listOff items 4
  set srcOff5 := longListSrcOff listOff items 5
  set absOff0 := ambientAbsOff off srcOff0
  set absOff1 := ambientAbsOff off srcOff1
  set absOff2 := ambientAbsOff off srcOff2
  set absOff3 := ambientAbsOff off srcOff3
  set absOff4 := ambientAbsOff off srcOff4
  set absOff5 := ambientAbsOff off srcOff5
  set absListOff := ambientAbsOff off listOff
  set endW := longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch slice).2.2) absListOff
  have hlen_sl := txSlice_length bs off len hbound
  have hlenW : lenW.toNat = slice.length := by
    have hspan : len < 2 ^ 64 := by omega
    rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspan, hlen_sl]
  have hoffInner : listOff < slice.length := extractSuccess_inner_lt slice hsuccess
  have hencInner : slice.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ hdecL
  have hlp : loadPtr.toNat = regionBase.toNat + off :=
    loadPtr_toNat_eq regionBase loadPtr off hptr (by omega)
  have hover_sl : loadPtr.toNat + slice.length < 2 ^ 64 := by
    rw [hlp, hlen_sl]; omega
  have hhoff :=
    extractSuccess_copy_type234_hoff_srcOff_long slice hsuccess hcopyFlag hge
      items hdecL hlong
  have hhover :=
    extractSuccess_copy_type234_hover_srcOff_long slice loadPtr hsuccess hcopyFlag hge
      items hdecL hlong hover_sl
  have hlenItems :=
    extractSuccess_copy_type234_items_length_long slice hsuccess hcopyFlag hge
      items hdecL hlong
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hn4 : (4 : Nat) < items.length := by omega
  have hn5 : (5 : Nat) < items.length := by omega
  have hoverEnd_sl : loadPtr.toNat +
      (listOff + 1 + longListLol items + (encode.encodeItems items).length) < 2 ^ 64 := by
    have hdrop : (slice.drop listOff).length = slice.length - listOff := by
      simp [List.length_drop]
    have hencLen := encode_list_long_length items hlong
    have hdropEq : (slice.drop listOff).length = (encode (.list items)).length := by
      rw [hencInner]
    have hpay : longListPayloadLen items = (encode.encodeItems items).length := rfl
    omega
  have hoverEnd_abs : regionBase.toNat +
      ambientAbsOff off (listOff + 1 + longListLol items +
        (encode.encodeItems items).length) < 2 ^ 64 := by
    simp only [ambientAbsOff]; omega
  have hendEq :
      endW = regionBase + BitVec.ofNat 64
        (ambientAbsOff off (listOff + 1 + longListLol items +
          (encode.encodeItems items).length)) := by
    have hspan_list : regionBase.toNat + (off + listOff) < 2 ^ 64 := by
      simp only [ambientAbsOff] at hoverEnd_abs ⊢
      omega
    have hend_sl_eq :
        longWalkEndAmbient loadPtr (lenW - (teerTxTypeDispatch slice).2.2) listOff =
          longListEndPtr loadPtr listOff items := by
      simpa [longWalkEndAmbient, longListEndPtr, listOff] using
        (longWalkEnd_eq_longListEndPtr loadPtr lenW slice items hsuccess hlenW
          hdecL hlong hover_sl)
    have hend_bridge :=
      longWalkEnd_loadPtr_eq regionBase loadPtr
        (lenW - (teerTxTypeDispatch slice).2.2) off listOff hptr hspan_list
    have hptr_end :=
      loadPtr_add_rel_eq regionBase loadPtr off
        (listOff + 1 + longListLol items + (encode.encodeItems items).length)
        hptr hoverEnd_abs
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
  -- hvalid at abs offs from validByteRange
  have hoff0 : absOff0 < bs.length := by
    have hrel : srcOff0 < len := by
      have : srcOff0 < slice.length := hhoff.1
      rwa [hlen_sl] at this
    simpa [absOff0, srcOff0] using absOff_lt_bs bs off len srcOff0 hbound hrel
  have hoff1 : absOff1 < bs.length := by
    have hrel : srcOff1 < len := by
      have : srcOff1 < slice.length := hhoff.2.1
      rwa [hlen_sl] at this
    simpa [absOff1, srcOff1] using absOff_lt_bs bs off len srcOff1 hbound hrel
  have hoff2 : absOff2 < bs.length := by
    have hrel : srcOff2 < len := by
      have : srcOff2 < slice.length := hhoff.2.2.1
      rwa [hlen_sl] at this
    simpa [absOff2, srcOff2] using absOff_lt_bs bs off len srcOff2 hbound hrel
  have hoff3 : absOff3 < bs.length := by
    have hrel : srcOff3 < len := by
      have : srcOff3 < slice.length := hhoff.2.2.2.1
      rwa [hlen_sl] at this
    simpa [absOff3, srcOff3] using absOff_lt_bs bs off len srcOff3 hbound hrel
  have hoff4 : absOff4 < bs.length := by
    have hrel : srcOff4 < len := by
      have : srcOff4 < slice.length := hhoff.2.2.2.2.1
      rwa [hlen_sl] at this
    simpa [absOff4, srcOff4] using absOff_lt_bs bs off len srcOff4 hbound hrel
  have hoff5 : absOff5 < bs.length := by
    have hrel : srcOff5 < len := by
      have : srcOff5 < slice.length := hhoff.2.2.2.2.2
      rwa [hlen_sl] at this
    simpa [absOff5, srcOff5] using absOff_lt_bs bs off len srcOff5 hbound hrel
  have hroom0 : srcOff0 + 1 < slice.length :=
    longListSrcOff_succ_room slice listOff items 0 hencInner hlong (by omega)
  have hroom1 : srcOff1 + 1 < slice.length :=
    longListSrcOff_succ_room slice listOff items 1 hencInner hlong (by omega)
  have hroom2 : srcOff2 + 1 < slice.length :=
    longListSrcOff_succ_room slice listOff items 2 hencInner hlong (by omega)
  have hroom3 : srcOff3 + 1 < slice.length :=
    longListSrcOff_succ_room slice listOff items 3 hencInner hlong (by omega)
  have hroom4 : srcOff4 + 1 < slice.length :=
    longListSrcOff_succ_room slice listOff items 4 hencInner hlong (by omega)
  have hge2_5 : 2 ≤ (encode (items[5]'hn5)).length :=
    extractSuccess_copy_type234_field5_encode_ge_two_long slice hsuccess hcopyFlag hge
      items hdecL hlong hn5
  have hroom5 : srcOff5 + 1 < slice.length :=
    hss_room_of_encode_ge_two_long slice listOff items 5 hencInner hlong hn5 hge2_5
  have hoff1_0 : absOff0 + 1 < bs.length := by
    have hrel : srcOff0 + 1 < len := by
      have : srcOff0 + 1 < slice.length := hroom0
      rwa [hlen_sl] at this
    simp only [absOff0, ambientAbsOff, srcOff0]; omega
  have hoff1_1 : absOff1 + 1 < bs.length := by
    have hrel : srcOff1 + 1 < len := by
      have : srcOff1 + 1 < slice.length := hroom1
      rwa [hlen_sl] at this
    simp only [absOff1, ambientAbsOff, srcOff1]; omega
  have hoff1_2 : absOff2 + 1 < bs.length := by
    have hrel : srcOff2 + 1 < len := by
      have : srcOff2 + 1 < slice.length := hroom2
      rwa [hlen_sl] at this
    simp only [absOff2, ambientAbsOff, srcOff2]; omega
  have hoff1_3 : absOff3 + 1 < bs.length := by
    have hrel : srcOff3 + 1 < len := by
      have : srcOff3 + 1 < slice.length := hroom3
      rwa [hlen_sl] at this
    simp only [absOff3, ambientAbsOff, srcOff3]; omega
  have hoff1_4 : absOff4 + 1 < bs.length := by
    have hrel : srcOff4 + 1 < len := by
      have : srcOff4 + 1 < slice.length := hroom4
      rwa [hlen_sl] at this
    simp only [absOff4, ambientAbsOff, srcOff4]; omega
  have hoff1_5 : absOff5 + 1 < bs.length := by
    have hrel : srcOff5 + 1 < len := by
      have : srcOff5 + 1 < slice.length := hroom5
      rwa [hlen_sl] at this
    simp only [absOff5, ambientAbsOff, srcOff5]; omega
  have hvalid0 := isValidByteAccess_of_validByteRange regionBase _ absOff0 hvalidBuf hoff0
  have hvalid1_0 :=
    isValidByteAccess_of_validByteRange regionBase _ (absOff0 + 1) hvalidBuf hoff1_0
  have hvalid1 := isValidByteAccess_of_validByteRange regionBase _ absOff1 hvalidBuf hoff1
  have hvalid1_1 :=
    isValidByteAccess_of_validByteRange regionBase _ (absOff1 + 1) hvalidBuf hoff1_1
  have hvalid2 := isValidByteAccess_of_validByteRange regionBase _ absOff2 hvalidBuf hoff2
  have hvalid1_2 :=
    isValidByteAccess_of_validByteRange regionBase _ (absOff2 + 1) hvalidBuf hoff1_2
  have hvalid3 := isValidByteAccess_of_validByteRange regionBase _ absOff3 hvalidBuf hoff3
  have hvalid1_3 :=
    isValidByteAccess_of_validByteRange regionBase _ (absOff3 + 1) hvalidBuf hoff1_3
  have hvalid4 := isValidByteAccess_of_validByteRange regionBase _ absOff4 hvalidBuf hoff4
  have hvalid1_4 :=
    isValidByteAccess_of_validByteRange regionBase _ (absOff4 + 1) hvalidBuf hoff1_4
  have hvalid5 := isValidByteAccess_of_validByteRange regionBase _ absOff5 hvalidBuf hoff5
  have hvalid1_5 :=
    isValidByteAccess_of_validByteRange regionBase _ (absOff5 + 1) hvalidBuf hoff1_5
  have hoff_tx : off < bs.length := by
    have hpos : 0 < len := by
      have h1 : listOff < slice.length := hoffInner
      have h2 : slice.length = len := hlen_sl
      omega
    omega
  have hvalidTx0 :=
    isValidByteAccess_of_validByteRange regionBase _ off hvalidBuf hoff_tx
  have hoff_list : absListOff < bs.length := by
    have hrel : listOff < len := by
      have : listOff < slice.length := hoffInner
      rwa [hlen_sl] at this
    simpa [absListOff, ambientAbsOff] using absOff_lt_bs bs off len listOff hbound hrel
  have hinvalid :=
    isValidByteAccess_of_validByteRange regionBase _ absListOff hvalidBuf hoff_list
  have hinover : regionBase.toNat + absListOff < 2 ^ 64 := by
    simp only [absListOff, ambientAbsOff]; omega
  have hspan0 : regionBase.toNat + absOff0 < 2 ^ 64 := by
    simp only [absOff0, ambientAbsOff, srcOff0]; have := hhover.1; omega
  have hspan1 : regionBase.toNat + absOff1 < 2 ^ 64 := by
    simp only [absOff1, ambientAbsOff, srcOff1]; have := hhover.2.1; omega
  have hspan2 : regionBase.toNat + absOff2 < 2 ^ 64 := by
    simp only [absOff2, ambientAbsOff, srcOff2]; have := hhover.2.2.1; omega
  have hspan3 : regionBase.toNat + absOff3 < 2 ^ 64 := by
    simp only [absOff3, ambientAbsOff, srcOff3]; have := hhover.2.2.2.1; omega
  have hspan4 : regionBase.toNat + absOff4 < 2 ^ 64 := by
    simp only [absOff4, ambientAbsOff, srcOff4]; have := hhover.2.2.2.2.1; omega
  have hspan5 : regionBase.toNat + absOff5 < 2 ^ 64 := by
    simp only [absOff5, ambientAbsOff, srcOff5]; have := hhover.2.2.2.2.2; omega
  have hdec0 :=
    hdec_ambient_field_long' regionBase loadPtr bs off len listOff items 0 endW
      hptr hbound hencInner hlong hn0 hitem0 hhoff.1 hspan0 hoverEnd_sl hoverEnd_abs hendEq
  have hdec1 :=
    hdec_ambient_field_long' regionBase loadPtr bs off len listOff items 1 endW
      hptr hbound hencInner hlong hn1 hitem1 hhoff.2.1 hspan1 hoverEnd_sl hoverEnd_abs hendEq
  have hdec2 :=
    hdec_ambient_field_long' regionBase loadPtr bs off len listOff items 2 endW
      hptr hbound hencInner hlong hn2 hitem2 hhoff.2.2.1 hspan2 hoverEnd_sl hoverEnd_abs hendEq
  have hdec3 :=
    hdec_ambient_field_long' regionBase loadPtr bs off len listOff items 3 endW
      hptr hbound hencInner hlong hn3 hitem3 hhoff.2.2.2.1 hspan3 hoverEnd_sl hoverEnd_abs hendEq
  have hdec4 :=
    hdec_ambient_field_long' regionBase loadPtr bs off len listOff items 4 endW
      hptr hbound hencInner hlong hn4 hitem4 hhoff.2.2.2.2.1 hspan4 hoverEnd_sl hoverEnd_abs hendEq
  have hdec5 :=
    hdec_ambient_field_long' regionBase loadPtr bs off len listOff items 5 endW
      hptr hbound hencInner hlong hn5 hitem5 hhoff.2.2.2.2.2 hspan5 hoverEnd_sl hoverEnd_abs hendEq
  -- hlover / hlvalid from validByteRange on lol window
  have hbound_enc : (encode.encodeItems items).length < 256 ^ 8 := by
    have hbsLt : (slice.drop listOff).length < 2 ^ 64 := by
      have hle : (slice.drop listOff).length ≤ slice.length := by
        simp only [List.length_drop]; omega
      have hbuf : slice.length < 2 ^ 64 := by omega
      exact Nat.lt_of_le_of_lt hle hbuf
    exact encodeItems_lt_256pow8_of_buf_lt (slice.drop listOff) items hencInner hlong hbsLt
  have hlol_le : longListLol items ≤ 8 :=
    Nat.toBytesBE_length_le (encode.encodeItems items).length 8 hbound_enc
  have hlover : regionBase.toNat + (absListOff + 1 + longListLol items) ≤ 2 ^ 64 := by
    simp only [absListOff, ambientAbsOff]
    have : listOff + 1 + longListLol items ≤ slice.length := by
      -- from encode length
      have hencLen := encode_list_long_length items hlong
      have hdropEq : (slice.drop listOff).length = (encode (.list items)).length := by
        rw [hencInner]
      have hdrop : (slice.drop listOff).length = slice.length - listOff := by
        simp [List.length_drop]
      omega
    have : listOff + 1 + longListLol items ≤ len := by rwa [hlen_sl] at this
    omega
  have hlvalid : ∀ k, k < longListLol items →
      isValidByteAccess (regionBase + BitVec.ofNat 64 (absListOff + 1 + k)) = true := by
    intro k hk
    have hk_bs : absListOff + 1 + k < bs.length := by
      simp only [absListOff, ambientAbsOff]
      have : listOff + 1 + longListLol items ≤ slice.length := by
        have hencLen := encode_list_long_length items hlong
        have hdropEq : (slice.drop listOff).length = (encode (.list items)).length := by
          rw [hencInner]
        have hdrop : (slice.drop listOff).length = slice.length - listOff := by
          simp [List.length_drop]
        omega
      have : listOff + 1 + longListLol items ≤ len := by rwa [hlen_sl] at this
      omega
    exact isValidByteAccess_of_validByteRange regionBase _ (absListOff + 1 + k)
      hvalidBuf hk_bs
  simpa [absOff0, absOff1, absOff2, absOff3, absOff4, absOff5, absListOff,
    srcOff0, srcOff1, srcOff2, srcOff3, srcOff4, srcOff5, listOff, slice] using
    extractAssumed_copy_longConcrete_pure_ambient
      sp0 spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len items q
      hq_align hq hcover hcvalid
      hspC hret htalign htover htvalid hlen hptr hbound hsuccess hcopyFlag hge hdecL hlong
      hsalign hover hvalidTx0 hinover hinvalid hlover hlvalid
      hitem0 hvalid0 hvalid1_0 hdec0
      hitem1 hvalid1 hvalid1_1 hdec1
      hitem2 hvalid2 hvalid1_2 hdec2
      hitem3 hvalid3 hvalid1_3 hdec3
      hitem4 hvalid4 hvalid1_4 hdec4
      hitem5 hvalid5 hvalid1_5 hdec5
     

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_longConcrete_pureHvalid_ambient_fullCode
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hq_align : ambientAbsOff off
        (longListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1 =
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
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdecL : decodeListItems
        ((txSlice bs off len).drop (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) =
      some items)
    (hlong : 55 < (encode.encodeItems items).length)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hitem0 : (encode (items[0]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    (hitem5 : (encode (items[5]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len) hsuccess
          hcopyFlag hge items hdecL hlong; omega))).length ≤ 55)
    :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_copy_longConcrete_pureHvalid_ambient
      sp0 spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len items q
      hq_align hq hcover hcvalid
      hspC hret htalign htover htvalid hlen hptr hbound hsuccess hcopyFlag hge hdecL hlong
      hsalign hover hvalidBuf
      hitem0 hitem1 hitem2 hitem3 hitem4 hitem5)

/-- Path refinements for ambient long type234 copy arm. -/
def extractCopyType234LongPathAmbient
    (bs : List (BitVec 8)) (off len : Nat) (items : List EL.RLP.RLPItem) (q : Nat) : Prop :=
  extractSuccess (txSlice bs off len) ∧
    (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word) ∧
    2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat ∧
    decodeListItems
        ((txSlice bs off len).drop (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) =
      some items ∧
    55 < (encode.encodeItems items).length ∧
    ambientAbsOff off
        (longListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1 =
      8 * q ∧
    8 * q + 16 < bs.length

set_option maxRecDepth 8000 in
/-- Ambient Assumed footprint under long type234 copy path (statics + path + hitem).
    classical-3. Residual: other extractSuccess arms (creation/legacy/t1). -/
theorem extractAssumed_success_flat_copy_type234_long_ambient
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hcover : regionBase.toNat + (8 * q + 16) < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (hpath : extractCopyType234LongPathAmbient bs off len items q)
    (hitem0 : (encode (items[0]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len)
          hpath.1 hpath.2.1 hpath.2.2.1 items hpath.2.2.2.1 hpath.2.2.2.2.1; omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len)
          hpath.1 hpath.2.1 hpath.2.2.1 items hpath.2.2.2.1 hpath.2.2.2.2.1; omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len)
          hpath.1 hpath.2.1 hpath.2.2.1 items hpath.2.2.2.1 hpath.2.2.2.2.1; omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len)
          hpath.1 hpath.2.1 hpath.2.2.1 items hpath.2.2.2.1 hpath.2.2.2.2.1; omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by
        have := extractSuccess_copy_type234_items_length_long (txSlice bs off len)
          hpath.1 hpath.2.1 hpath.2.2.1 items hpath.2.2.2.1 hpath.2.2.2.2.1; omega))).length ≤ 55)
    :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  obtain ⟨hsuccess, hcopyFlag, hge, hdecL, hlong, hq_align, hq⟩ := hpath
  have hlen_items :=
    extractSuccess_copy_type234_items_length_long (txSlice bs off len)
      hsuccess hcopyFlag hge items hdecL hlong
  have hitem5 :
      (encode (items[5]'(by omega))).length ≤ 55 :=
    extractSuccess_copy_type234_field5_encode_le55_long (txSlice bs off len)
      hsuccess hcopyFlag hge items hdecL hlong
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
    extractAssumed_copy_longConcrete_pureHvalid_ambient_fullCode
      spVal spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len items q
      hq_align hq hcover hcvalid
      hspC hret htalign htover htvalid hlen hptr hbound hsuccess hcopyFlag hge hdecL hlong
      hsalign hover hvalidBuf
      hitem0 hitem1 hitem2 hitem3 hitem4 hitem5

#print axioms extractAssumed_copy_longConcrete_pureHvalid_ambient
#print axioms extractAssumed_copy_longConcrete_pureHvalid_ambient_fullCode
#print axioms extractAssumed_success_flat_copy_type234_long_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
