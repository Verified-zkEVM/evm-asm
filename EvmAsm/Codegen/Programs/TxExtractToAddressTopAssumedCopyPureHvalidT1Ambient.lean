/-
  Ambient short t1 copy: discharge hdec*/hvalid* via slice pure + bridges +
  validByteRange on regionBase. Residual path flags (copy/t1/short/hq_align).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressAmbientPureBridge
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyShortConcretePureT1Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitShort

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

/-- Lift slice hdec at shortListSrcOff to abs decode at regionBase. -/
private theorem hdec_ambient_field'
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (k : Nat) (endW : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : k < items.length)
    (hoff_sl : shortListSrcOff listOff items k < (txSlice bs off len).length)
    (hspan_src : regionBase.toNat +
      ambientAbsOff off (shortListSrcOff listOff items k) < 2 ^ 64)
    (hoverEnd_sl : loadPtr.toNat +
      (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64)
    (hoverEnd_abs : regionBase.toNat +
      ambientAbsOff off (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64)
    (hend : endW =
      regionBase + BitVec.ofNat 64
        (ambientAbsOff off (listOff + 1 + (encode.encodeItems items).length))) :
    ∃ n l : Word,
      rlpItemDecode bs (ambientAbsOff off (shortListSrcOff listOff items k))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff listOff items k)))
        endW n l := by
  set slice := txSlice bs off len
  set srcOff := shortListSrcOff listOff items k
  set absOff := ambientAbsOff off srcOff
  set endSl := shortListEndPtr loadPtr listOff items
  have hlen_sl := txSlice_length bs off len hbound
  have hrel : srcOff < len := by
    have : srcOff < slice.length := hoff_sl
    rwa [hlen_sl] at this
  have hdec_sl :=
    hdec_short_list_end slice loadPtr listOff items k henc hshort hn hoff_sl
      hoverEnd_sl endSl rfl
  obtain ⟨n, l, hd⟩ := hdec_sl
  have hshort_form :=
    hshort_abs_at_short_list_field bs off len listOff items k hbound henc hshort hn
      hoff_sl
  -- Convert hshort_abs (on bs) to slice form for transfer
  have hshort_sl :
      ¬ (∃ b, slice[srcOff]? = some b ∧
        ((¬ BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
            BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true) ∨
          ¬ BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true)) := by
    intro ⟨b, hb, hlong⟩
    have hrel' : srcOff < len := hrel
    have hb' : bs[off + srcOff]? = some b := by
      rw [← txSlice_getElem? bs off len srcOff hbound hrel']; exact hb
    exact hshort_form ⟨b, by simpa [ambientAbsOff] using hb', hlong⟩
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
    simp only [endSl, shortListEndPtr, hend, ambientAbsOff]
    exact loadPtr_add_rel_eq regionBase loadPtr off
      (listOff + 1 + (encode.encodeItems items).length) hptr hoverEnd_abs
  refine ⟨n, l, ?_⟩
  rw [← hcur_eq, ← hend_eq]
  exact hd_abs

set_option maxRecDepth 8000 in
/-- Ambient short concrete Assumed copy; hdec+hvalid from pure+validByteRange.
    Residual path: copy/t1/short/hdecL. -/
theorem extractAssumed_copy_shortConcrete_pureHvalid_t1_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4) + 1 =
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
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdecL : decodeListItems
        ((txSlice bs off len).drop (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) := by
  set slice := txSlice bs off len with hslice
  set listOff := (teerTxTypeDispatch slice).2.2.toNat
  set srcOff0 := shortListSrcOff listOff items 0
  set srcOff1 := shortListSrcOff listOff items 1
  set srcOff2 := shortListSrcOff listOff items 2
  set srcOff3 := shortListSrcOff listOff items 3
  set srcOff4 := shortListSrcOff listOff items 4
  set absOff0 := ambientAbsOff off srcOff0
  set absOff1 := ambientAbsOff off srcOff1
  set absOff2 := ambientAbsOff off srcOff2
  set absOff3 := ambientAbsOff off srcOff3
  set absOff4 := ambientAbsOff off srcOff4
  set absListOff := ambientAbsOff off listOff
  set endW := shortWalkEnd regionBase (lenW - (teerTxTypeDispatch slice).2.2) absListOff
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
    extractSuccess_copy_t1_hoff_srcOff slice hsuccess hcopyFlag htype1
      items hdecL hshort
  have hhover :=
    extractSuccess_copy_t1_hover_srcOff slice loadPtr hsuccess hcopyFlag htype1
      items hdecL hshort hover_sl
  have hlenItems :=
    extractSuccess_copy_t1_items_length slice hsuccess hcopyFlag htype1
      items hdecL hshort
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hn4 : (4 : Nat) < items.length := by omega
  have hoverEnd_sl : loadPtr.toNat +
      (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64 := by
    have hencLen := encode_list_short_length items hshort
    have hdropEq : (slice.drop listOff).length = (encode (.list items)).length := by
      rw [hencInner]
    have hdrop : (slice.drop listOff).length = slice.length - listOff := by
      simp [List.length_drop]
    omega
  have hoverEnd_abs : regionBase.toNat +
      ambientAbsOff off (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64 := by
    simp only [ambientAbsOff]; omega
  have hendEq :
      endW = regionBase + BitVec.ofNat 64
        (ambientAbsOff off (listOff + 1 + (encode.encodeItems items).length)) := by
    have hspan_list : regionBase.toNat + (off + listOff) < 2 ^ 64 := by
      simp only [ambientAbsOff] at hoverEnd_abs ⊢
      omega
    have hend_sl_eq :
        shortWalkEnd loadPtr (lenW - (teerTxTypeDispatch slice).2.2) listOff =
          shortListEndPtr loadPtr listOff items :=
      shortWalkEnd_eq_shortListEndPtr loadPtr lenW slice items hsuccess hlenW
        hdecL hshort hover_sl
    have hend_bridge :=
      shortWalkEnd_loadPtr_eq regionBase loadPtr
        (lenW - (teerTxTypeDispatch slice).2.2) off listOff hptr hspan_list
    have hptr_end :=
      loadPtr_add_rel_eq regionBase loadPtr off
        (listOff + 1 + (encode.encodeItems items).length) hptr hoverEnd_abs
    simp only [endW, absListOff, shortListEndPtr] at hend_sl_eq hend_bridge ⊢
    calc
      shortWalkEnd regionBase (lenW - (teerTxTypeDispatch slice).2.2)
          (ambientAbsOff off listOff)
          = shortWalkEnd loadPtr (lenW - (teerTxTypeDispatch slice).2.2) listOff :=
            hend_bridge.symm
      _ = loadPtr + BitVec.ofNat 64
            (listOff + 1 + (encode.encodeItems items).length) := hend_sl_eq
      _ = regionBase + BitVec.ofNat 64
            (ambientAbsOff off
              (listOff + 1 + (encode.encodeItems items).length)) := by
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
      have : srcOff4 < slice.length := hhoff.2.2.2.2
      rwa [hlen_sl] at this
    simpa [absOff4, srcOff4] using absOff_lt_bs bs off len srcOff4 hbound hrel
  have hroom0 : srcOff0 + 1 < slice.length :=
    shortListSrcOff_succ_room slice listOff items 0 hencInner hshort (by omega)
  have hroom1 : srcOff1 + 1 < slice.length :=
    shortListSrcOff_succ_room slice listOff items 1 hencInner hshort (by omega)
  have hroom2 : srcOff2 + 1 < slice.length :=
    shortListSrcOff_succ_room slice listOff items 2 hencInner hshort (by omega)
  have hroom3 : srcOff3 + 1 < slice.length :=
    shortListSrcOff_succ_room slice listOff items 3 hencInner hshort (by omega)
  have hn4 : (4 : Nat) < items.length := by
    have := extractSuccess_copy_t1_items_length slice hsuccess hcopyFlag htype1
      items hdecL hshort
    omega
  have hge2_4 : 2 ≤ (encode (items[4]'hn4)).length :=
    extractSuccess_copy_t1_field4_encode_ge_two slice hsuccess hcopyFlag htype1
      items hdecL hshort hn4
  have hroom4 : srcOff4 + 1 < slice.length :=
    hss_room_of_encode_ge_two slice listOff items 4 hencInner hshort hn4 hge2_4
  have hoff1_0 : absOff0 + 1 < bs.length := by
    have hrel : srcOff0 + 1 < len := by
      have : srcOff0 + 1 < slice.length := hroom0
      rwa [hlen_sl] at this
    simp only [absOff0, ambientAbsOff, srcOff0]
    omega
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
  -- hvalidTx0 / hinvalid / hinover
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
  -- hdec ambient
  have hspan0 : regionBase.toNat + absOff0 < 2 ^ 64 := by
    simp only [absOff0, ambientAbsOff, srcOff0]; have := hhover.1; omega
  have hspan1 : regionBase.toNat + absOff1 < 2 ^ 64 := by
    simp only [absOff1, ambientAbsOff, srcOff1]; have := hhover.2.1; omega
  have hspan2 : regionBase.toNat + absOff2 < 2 ^ 64 := by
    simp only [absOff2, ambientAbsOff, srcOff2]; have := hhover.2.2.1; omega
  have hspan3 : regionBase.toNat + absOff3 < 2 ^ 64 := by
    simp only [absOff3, ambientAbsOff, srcOff3]; have := hhover.2.2.2.1; omega
  have hspan4 : regionBase.toNat + absOff4 < 2 ^ 64 := by
    simp only [absOff4, ambientAbsOff, srcOff4]; have := hhover.2.2.2.2; omega
  have hdec0 :=
    hdec_ambient_field' regionBase loadPtr bs off len listOff items 0 endW
      hptr hbound hencInner hshort hn0 hhoff.1 hspan0 hoverEnd_sl hoverEnd_abs hendEq
  have hdec1 :=
    hdec_ambient_field' regionBase loadPtr bs off len listOff items 1 endW
      hptr hbound hencInner hshort hn1 hhoff.2.1 hspan1 hoverEnd_sl hoverEnd_abs hendEq
  have hdec2 :=
    hdec_ambient_field' regionBase loadPtr bs off len listOff items 2 endW
      hptr hbound hencInner hshort hn2 hhoff.2.2.1 hspan2 hoverEnd_sl hoverEnd_abs hendEq
  have hdec3 :=
    hdec_ambient_field' regionBase loadPtr bs off len listOff items 3 endW
      hptr hbound hencInner hshort hn3 hhoff.2.2.2.1 hspan3 hoverEnd_sl hoverEnd_abs hendEq
  have hdec4 :=
    hdec_ambient_field' regionBase loadPtr bs off len listOff items 4 endW
      hptr hbound hencInner hshort hn4 hhoff.2.2.2.2 hspan4 hoverEnd_sl hoverEnd_abs hendEq
  -- rewrite absOff names for pure_ambient call
  simpa [absOff0, absOff1, absOff2, absOff3, absListOff,
    srcOff0, srcOff1, srcOff2, srcOff3, listOff, slice] using
    extractAssumed_copy_shortConcrete_pure_t1_region_ambient
      sp0 spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len items q
      hq_align hq hcover hcvalid
      hspC hret htalign htover htvalid hlen hptr hbound hsuccess hcopyFlag htype1 hdecL hshort
      hsalign hover hvalidTx0 hinover hinvalid
      hvalid0 hvalid1_0 hdec0
      hvalid1 hvalid1_1 hdec1
      hvalid2 hvalid1_2 hdec2
      hvalid3 hvalid1_3 hdec3
      hvalid4 hvalid1_4 hdec4

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_shortConcrete_pureHvalid_t1_ambient_fullCode
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4) + 1 =
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
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdecL : decodeListItems
        ((txSlice bs off len).drop (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_copy_shortConcrete_pureHvalid_t1_ambient
      sp0 spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len items q
      hq_align hq hcover hcvalid
      hspC hret htalign htover htvalid hlen hptr hbound hsuccess hcopyFlag htype1 hdecL hshort
      hsalign hover hvalidBuf)

/-- Path refinements for ambient short t1 copy arm. -/
def extractCopyT1ShortPathAmbient
    (bs : List (BitVec 8)) (off len : Nat) (items : List EL.RLP.RLPItem) (q : Nat) : Prop :=
  extractSuccess (txSlice bs off len) ∧
    (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word) ∧
    (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word) ∧
    decodeListItems
        ((txSlice bs off len).drop (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) =
      some items ∧
    (encode.encodeItems items).length ≤ 55 ∧
    ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4) + 1 =
      8 * q ∧
    8 * q + 16 < bs.length

set_option maxRecDepth 8000 in
/-- Ambient Assumed footprint under short t1 copy path (statics + path).
    classical-3. Residual: other extractSuccess arms (creation/t1/long). -/
theorem extractAssumed_success_flat_copy_t1_short_ambient
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (items : List EL.RLP.RLPItem) (q : Nat)
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
    (hpath : extractCopyT1ShortPathAmbient bs off len items q)
    (hcover : regionBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  obtain ⟨hsuccess, hcopyFlag, htype1, hdecL, hshort, hq_align, hq⟩ := hpath
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
    extractAssumed_copy_shortConcrete_pureHvalid_t1_ambient_fullCode
      spVal spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len items q
      hq_align hq hcover hcvalid
      hspC hret htalign htover htvalid hlen hptr hbound hsuccess hcopyFlag htype1 hdecL hshort
      hsalign hover hvalidBuf

#print axioms extractAssumed_copy_shortConcrete_pureHvalid_t1_ambient
#print axioms extractAssumed_copy_shortConcrete_pureHvalid_t1_ambient_fullCode
#print axioms extractAssumed_success_flat_copy_t1_short_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
