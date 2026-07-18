/-
  Wire pure honesty into ambient short concrete Assumed copy (region).
  Pure on txSlice+loadPtr; bridge to regionBase/bs abs offsets.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressAmbientPureBridge
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyShortConcreteAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitShort

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
/-- Ambient short concrete Assumed copy with pure-discharged hcur/hnext/hlen20/hnext_content/hinb/
    hoff/hover/hls/hll/hne and short walk guards. Residual: hvalid*/hvalid1_*/hdec*. -/
theorem extractAssumed_copy_shortConcrete_pure_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1 =
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
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidTx0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (hinover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0))) = true)
    (hvalid1_0 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0) + 1)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next0 len0)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1))) = true)
    (hvalid1_1 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1) + 1)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next1 len1)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2))) = true)
    (hvalid1_2 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2) + 1)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next2 len2)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3))) = true)
    (hvalid1_3 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next3 len3)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4))) = true)
    (hvalid1_4 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4) + 1)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next4 len4)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5))) = true)
    (hvalid1_5 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1)) = true)
    (hdec5 : ∃ next5 len5 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next5 len5)
    (hge7 : 7 ≤ items.length) :
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
  set srcOff5 := shortListSrcOff listOff items 5
  set absOff0 := ambientAbsOff off srcOff0
  set absOff1 := ambientAbsOff off srcOff1
  set absOff2 := ambientAbsOff off srcOff2
  set absOff3 := ambientAbsOff off srcOff3
  set absOff4 := ambientAbsOff off srcOff4
  set absOff5 := ambientAbsOff off srcOff5
  set absListOff := ambientAbsOff off listOff
  set endW := shortWalkEnd regionBase (lenW - (teerTxTypeDispatch slice).2.2) absListOff
  have hty0 := extractSuccess_type_ok slice hsuccess
  have hlen_sl := txSlice_length bs off len hbound
  have hlenW : lenW.toNat = slice.length := by
    have hspan : len < 2 ^ 64 := by omega
    rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspan, hlen_sl]
  have hoffInner : listOff < slice.length := extractSuccess_inner_lt slice hsuccess
  have hwalk :=
    extractSuccess_short_front_walkInit_hyps loadPtr lenW slice hsuccess hlenW
      items hdecL hshort
  have hlistLen_ne := hwalk.1
  have h_ge_sl := hwalk.2.1
  have h_hi_sl := hwalk.2.2.1
  have h_exact_sl := hwalk.2.2.2
  have hne0 : (teerTxTypeDispatch slice).2.1 ≠ 0 := by
    intro hz
    have : (teerTxTypeDispatch slice).2.1.toNat = 0 := by simp [hz]
    omega
  have hne1 : (teerTxTypeDispatch slice).2.1 ≠ 1 := by
    intro hz
    have : (teerTxTypeDispatch slice).2.1.toNat = 1 := by simp [hz]
    omega
  have hhoff :=
    extractSuccess_copy_type234_hoff_srcOff slice hsuccess hcopyFlag hge
      items hdecL hshort
  have hlp : loadPtr.toNat = regionBase.toNat + off :=
    loadPtr_toNat_eq regionBase loadPtr off hptr (by omega)
  have hover_sl : loadPtr.toNat + slice.length < 2 ^ 64 := by
    rw [hlp, hlen_sl]; omega
  have hhover :=
    extractSuccess_copy_type234_hover_srcOff slice loadPtr hsuccess hcopyFlag hge
      items hdecL hshort hover_sl
  have hlenItems :=
    extractSuccess_copy_type234_items_length slice hsuccess hcopyFlag hge
      items hdecL hshort
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hn4 : (4 : Nat) < items.length := by omega
  have hn5 : (5 : Nat) < items.length := by omega
  have hfields04 :=
    extractSuccess_copy_type234_hnext_fields04 slice hsuccess hcopyFlag hge
      items hdecL hshort
  have hencInner : slice.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ hdecL
  have hoverEnd :
      regionBase.toNat +
        (off + (listOff + 1 + (encode.encodeItems items).length)) < 2 ^ 64 := by
    have hencLen := encode_list_short_length items hshort
    have hdropEq : (slice.drop listOff).length = (encode (.list items)).length := by
      rw [hencInner]
    have hdrop : (slice.drop listOff).length = slice.length - listOff := by
      simp [List.length_drop]
    omega
  have hspan_list : regionBase.toNat + (off + listOff) < 2 ^ 64 := by
    simpa [absListOff, ambientAbsOff] using hinover
  have hend_sl_eq :
      shortWalkEnd loadPtr (lenW - (teerTxTypeDispatch slice).2.2) listOff =
        shortListEndPtr loadPtr listOff items :=
    shortWalkEnd_eq_shortListEndPtr loadPtr lenW slice items hsuccess hlenW
      hdecL hshort hover_sl
  have hendEq :
      endW = regionBase + BitVec.ofNat 64
        (ambientAbsOff off (listOff + 1 + (encode.encodeItems items).length)) := by
    have hend_bridge :=
      shortWalkEnd_loadPtr_eq regionBase loadPtr
        (lenW - (teerTxTypeDispatch slice).2.2) off listOff hptr hspan_list
    have hptr_end :=
      loadPtr_add_rel_eq regionBase loadPtr off
        (listOff + 1 + (encode.encodeItems items).length) hptr hoverEnd
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
  have hspan_src0 : regionBase.toNat + (off + (listOff + 1)) < 2 ^ 64 := by
    have h0 := hhover.1
    simp only [shortListSrcOff_zero] at h0
    omega
  have hcur :
      shortWalkCursor regionBase absListOff =
        regionBase + BitVec.ofNat 64 absOff0 := by
    simpa [absListOff, absOff0, srcOff0, listOff] using
      hcur_ambient_short_srcOff0 regionBase loadPtr off listOff items
        hptr hspan_list hspan_src0
  have hhnext :=
    extractSuccess_copy_type234_hnext_hlen20_srcOff slice loadPtr hsuccess
      hcopyFlag hge items hdecL hshort
      hhover.1 hhover.2.1 hhover.2.2.1 hhover.2.2.2.1 hhover.2.2.2.2.1 hhover.2.2.2.2.2
  have hoff0_sl : srcOff0 < slice.length := hhoff.1
  have hoff1_sl : srcOff1 < slice.length := hhoff.2.1
  have hoff2_sl : srcOff2 < slice.length := hhoff.2.2.1
  have hoff3_sl : srcOff3 < slice.length := hhoff.2.2.2.1
  have hoff4_sl : srcOff4 < slice.length := hhoff.2.2.2.2.1
  have hoff5_sl : srcOff5 < slice.length := hhoff.2.2.2.2.2
  have hspan0a : regionBase.toNat + (off + srcOff0) < 2 ^ 64 := by
    have hs := hhover.1
    omega
  have hspan1a : regionBase.toNat + (off + srcOff1) < 2 ^ 64 := by
    have hs := hhover.2.1
    omega
  have hspan2a : regionBase.toNat + (off + srcOff2) < 2 ^ 64 := by
    have hs := hhover.2.2.1
    omega
  have hspan3a : regionBase.toNat + (off + srcOff3) < 2 ^ 64 := by
    have hs := hhover.2.2.2.1
    omega
  have hspan4a : regionBase.toNat + (off + srcOff4) < 2 ^ 64 := by
    have hs := hhover.2.2.2.2.1
    omega
  have hspan5a : regionBase.toNat + (off + srcOff5) < 2 ^ 64 := by
    have hs := hhover.2.2.2.2.2
    omega
  have hroom0 : srcOff0 + 1 < slice.length :=
    shortListSrcOff_succ_room slice listOff items 0 hencInner hshort (by omega)
  have hroom1 : srcOff1 + 1 < slice.length :=
    shortListSrcOff_succ_room slice listOff items 1 hencInner hshort (by omega)
  have hroom2 : srcOff2 + 1 < slice.length :=
    shortListSrcOff_succ_room slice listOff items 2 hencInner hshort (by omega)
  have hroom3 : srcOff3 + 1 < slice.length :=
    shortListSrcOff_succ_room slice listOff items 3 hencInner hshort (by omega)
  have hroom4 : srcOff4 + 1 < slice.length :=
    shortListSrcOff_succ_room slice listOff items 4 hencInner hshort (by omega)
  have hroom5 : srcOff5 + 1 < slice.length :=
    shortListSrcOff_succ_room slice listOff items 5 hencInner hshort (by omega)
  have hnext1 : ∀ (next0 len0 : Word),
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0) endW
        next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 absOff1 := by
    simpa [absOff0, absOff1, srcOff0, srcOff1, listOff, endW, absListOff] using
      packaging_hnext_ambient_field regionBase loadPtr bs off len listOff items 0 1
        endW hptr hbound hencInner hshort hn0 hoff0_sl hspan0a hspan1a hroom0
        (fun n l hd => hhnext.1 endW n l hd)
  have hnext2 : ∀ (next1 len1 : Word),
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1) endW
        next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 absOff2 := by
    simpa [absOff1, absOff2, srcOff1, srcOff2, listOff, endW, absListOff] using
      packaging_hnext_ambient_field regionBase loadPtr bs off len listOff items 1 2
        endW hptr hbound hencInner hshort hn1 hoff1_sl hspan1a hspan2a hroom1
        (fun n l hd => hhnext.2.1 endW n l hd)
  have hnext3 : ∀ (next2 len2 : Word),
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2) endW
        next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 absOff3 := by
    simpa [absOff2, absOff3, srcOff2, srcOff3, listOff, endW, absListOff] using
      packaging_hnext_ambient_field regionBase loadPtr bs off len listOff items 2 3
        endW hptr hbound hencInner hshort hn2 hoff2_sl hspan2a hspan3a hroom2
        (fun n l hd => hhnext.2.2.1 endW n l hd)
  have hnext4 : ∀ (next3 len3 : Word),
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3) endW
        next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 absOff4 := by
    simpa [absOff3, absOff4, srcOff3, srcOff4, listOff, endW, absListOff] using
      packaging_hnext_ambient_field regionBase loadPtr bs off len listOff items 3 4
        endW hptr hbound hencInner hshort hn3 hoff3_sl hspan3a hspan4a hroom3
        (fun n l hd => hhnext.2.2.2.1 endW n l hd)
  have hnext5 : ∀ (next4 len4 : Word),
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4) endW
        next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 absOff5 := by
    simpa [absOff4, absOff5, srcOff4, srcOff5, listOff, endW, absListOff] using
      packaging_hnext_ambient_field regionBase loadPtr bs off len listOff items 4 5
        endW hptr hbound hencInner hshort hn4 hoff4_sl hspan4a hspan5a hroom4
        (fun n l hd => hhnext.2.2.2.2.1 endW n l hd)
  have hlen20 : ∀ (next5 len5 : Word),
      rlpItemDecode bs absOff5 (regionBase + BitVec.ofNat 64 absOff5) endW
        next5 len5 →
      len5 = (20 : Word) := by
    simpa [absOff5, srcOff5, listOff, endW, absListOff] using
      hlen20_ambient_of_slice regionBase loadPtr bs off len listOff items 5 endW
        hptr hbound hencInner hshort hn5 hoff5_sl hspan5a hroom5
        (fun n l hd => hhnext.2.2.2.2.2 endW n l hd)
  have hq_abs : ambientAbsOff off srcOff5 + 1 = 8 * q := by
    simpa [srcOff5, listOff, ambientAbsOff] using hq_align
  have hnext_sl_content : ∀ (next5 len5 : Word),
      rlpItemDecode slice srcOff5 (loadPtr + BitVec.ofNat 64 srcOff5) endW
        next5 len5 →
      next5 = loadPtr + BitVec.ofNat 64 srcOff5 + (1 : Word) + (20 : Word) := by
    intro n l hd
    have hc := extractSuccess_copy_type234_hnext_content_srcOff slice loadPtr
      (loadPtr + BitVec.ofNat 64 srcOff5 + (1 : Word))
      hsuccess hcopyFlag hge items hdecL hshort rfl
    -- contentPtr + 20 with contentPtr = loadPtr + ofNat srcOff5 + 1
    simpa using hc endW n l hd
  have hcover20 : regionBase.toNat + 8 * q + 20 < 2 ^ 64 := by omega
  have hnext_content : ∀ (next5 len5 : Word),
      rlpItemDecode bs absOff5 (regionBase + BitVec.ofNat 64 absOff5) endW
        next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 (8 * q) + (20 : Word) := by
    simpa [absOff5, srcOff5, listOff, endW, absListOff] using
      hnext_content_ambient_of_slice regionBase loadPtr bs off len listOff items 5 q endW
        hptr hbound hencInner hshort hn5 hoff5_sl hspan5a hroom5 hq_abs hcover20
        hnext_sl_content
  have hinb0 :=
    hinb_ambient_short_list_end regionBase off listOff items 0 hn0 hoverEnd endW hendEq
  have hinb1 :=
    hinb_ambient_short_list_end regionBase off listOff items 1 hn1 hoverEnd endW hendEq
  have hinb2 :=
    hinb_ambient_short_list_end regionBase off listOff items 2 hn2 hoverEnd endW hendEq
  have hinb3 :=
    hinb_ambient_short_list_end regionBase off listOff items 3 hn3 hoverEnd endW hendEq
  have hinb4 :=
    hinb_ambient_short_list_end regionBase off listOff items 4 hn4 hoverEnd endW hendEq
  have hinb5 :=
    hinb_ambient_short_list_end regionBase off listOff items 5 hn5 hoverEnd endW hendEq
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
      have : srcOff3 < slice.length := hhoff.2.2.2.1
      rwa [hlen_sl] at this
    simpa [absOff3, srcOff3] using absOff_lt_bs bs off len srcOff3 hbound hrel
  have hover3 : regionBase.toNat + absOff3 < 2 ^ 64 := by
    simpa [absOff3, ambientAbsOff, srcOff3] using hspan3a
  have hoff4 : absOff4 < bs.length := by
    have hrel : srcOff4 < len := by
      have : srcOff4 < slice.length := hhoff.2.2.2.2.1
      rwa [hlen_sl] at this
    simpa [absOff4, srcOff4] using absOff_lt_bs bs off len srcOff4 hbound hrel
  have hover4 : regionBase.toNat + absOff4 < 2 ^ 64 := by
    simpa [absOff4, ambientAbsOff, srcOff4] using hspan4a
  have hoff5 : absOff5 < bs.length := by
    have hrel : srcOff5 < len := by
      have : srcOff5 < slice.length := hhoff.2.2.2.2.2
      rwa [hlen_sl] at this
    simpa [absOff5, srcOff5] using absOff_lt_bs bs off len srcOff5 hbound hrel
  have hover5 : regionBase.toNat + absOff5 < 2 ^ 64 := by
    simpa [absOff5, ambientAbsOff, srcOff5] using hspan5a
  have hss0 :=
    hss_ambient_of_short_list_field regionBase loadPtr bs off len listOff items 0
      hptr hbound hencInner hshort hn0 hoff0_sl hover (Or.inl hfields04.1)
      hvalid1_0 hoff0
  have hss1 :=
    hss_ambient_of_short_list_field regionBase loadPtr bs off len listOff items 1
      hptr hbound hencInner hshort hn1 hoff1_sl hover (Or.inl hfields04.2.1)
      hvalid1_1 hoff1
  have hss2 :=
    hss_ambient_of_short_list_field regionBase loadPtr bs off len listOff items 2
      hptr hbound hencInner hshort hn2 hoff2_sl hover (Or.inl hfields04.2.2.1)
      hvalid1_2 hoff2
  have hss3 :=
    hss_ambient_of_short_list_field regionBase loadPtr bs off len listOff items 3
      hptr hbound hencInner hshort hn3 hoff3_sl hover (Or.inl hfields04.2.2.2.1)
      hvalid1_3 hoff3
  have hss4 :=
    hss_ambient_of_short_list_field regionBase loadPtr bs off len listOff items 4
      hptr hbound hencInner hshort hn4 hoff4_sl hover (Or.inl hfields04.2.2.2.2)
      hvalid1_4 hoff4
  have hss5 :=
    hss_ambient_of_short_list_field regionBase loadPtr bs off len listOff items 5
      hptr hbound hencInner hshort hn5 hoff5_sl hover (Or.inl (by omega : 6 < items.length))
      hvalid1_5 hoff5
  have hls0 :
      ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + k)) = true := by
    intro hlo hhi
    have heq : bs[absOff0]'hoff0 = slice[srcOff0]'hoff0_sl := by
      simp only [absOff0, ambientAbsOff, srcOff0]
      have hrel : srcOff0 < len := by
        have : srcOff0 < slice.length := hoff0_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff0 hbound hrel hoff0_sl hoff0).symm
    have hlo' := hlo; rw [heq] at hlo'
    have hhi' := hhi; rw [heq] at hhi'
    exact hls_vacuous_of_short_list_item slice listOff items 0
      hencInner hshort hn0 hoff0_sl hlo' hhi'
  have hll0 :
      ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + k)) = true := by
    intro hgeF8
    have heq : bs[absOff0]'hoff0 = slice[srcOff0]'hoff0_sl := by
      simp only [absOff0, ambientAbsOff, srcOff0]
      have hrel : srcOff0 < len := by
        have : srcOff0 < slice.length := hoff0_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff0 hbound hrel hoff0_sl hoff0).symm
    have h' := hgeF8; rw [heq] at h'
    exact hll_vacuous_of_short_list_item slice listOff items 0
      hencInner hshort hn0 hoff0_sl h'
  have hls1 :
      ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true := by
    intro hlo hhi
    have heq : bs[absOff1]'hoff1 = slice[srcOff1]'hoff1_sl := by
      simp only [absOff1, ambientAbsOff, srcOff1]
      have hrel : srcOff1 < len := by
        have : srcOff1 < slice.length := hoff1_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff1 hbound hrel hoff1_sl hoff1).symm
    have hlo' := hlo; rw [heq] at hlo'
    have hhi' := hhi; rw [heq] at hhi'
    exact hls_vacuous_of_short_list_item slice listOff items 1
      hencInner hshort hn1 hoff1_sl hlo' hhi'
  have hll1 :
      ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true := by
    intro hgeF8
    have heq : bs[absOff1]'hoff1 = slice[srcOff1]'hoff1_sl := by
      simp only [absOff1, ambientAbsOff, srcOff1]
      have hrel : srcOff1 < len := by
        have : srcOff1 < slice.length := hoff1_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff1 hbound hrel hoff1_sl hoff1).symm
    have h' := hgeF8; rw [heq] at h'
    exact hll_vacuous_of_short_list_item slice listOff items 1
      hencInner hshort hn1 hoff1_sl h'
  have hls2 :
      ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + k)) = true := by
    intro hlo hhi
    have heq : bs[absOff2]'hoff2 = slice[srcOff2]'hoff2_sl := by
      simp only [absOff2, ambientAbsOff, srcOff2]
      have hrel : srcOff2 < len := by
        have : srcOff2 < slice.length := hoff2_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff2 hbound hrel hoff2_sl hoff2).symm
    have hlo' := hlo; rw [heq] at hlo'
    have hhi' := hhi; rw [heq] at hhi'
    exact hls_vacuous_of_short_list_item slice listOff items 2
      hencInner hshort hn2 hoff2_sl hlo' hhi'
  have hll2 :
      ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + k)) = true := by
    intro hgeF8
    have heq : bs[absOff2]'hoff2 = slice[srcOff2]'hoff2_sl := by
      simp only [absOff2, ambientAbsOff, srcOff2]
      have hrel : srcOff2 < len := by
        have : srcOff2 < slice.length := hoff2_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff2 hbound hrel hoff2_sl hoff2).symm
    have h' := hgeF8; rw [heq] at h'
    exact hll_vacuous_of_short_list_item slice listOff items 2
      hencInner hshort hn2 hoff2_sl h'
  have hls3 :
      ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + k)) = true := by
    intro hlo hhi
    have heq : bs[absOff3]'hoff3 = slice[srcOff3]'hoff3_sl := by
      simp only [absOff3, ambientAbsOff, srcOff3]
      have hrel : srcOff3 < len := by
        have : srcOff3 < slice.length := hoff3_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff3 hbound hrel hoff3_sl hoff3).symm
    have hlo' := hlo; rw [heq] at hlo'
    have hhi' := hhi; rw [heq] at hhi'
    exact hls_vacuous_of_short_list_item slice listOff items 3
      hencInner hshort hn3 hoff3_sl hlo' hhi'
  have hll3 :
      ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + k)) = true := by
    intro hgeF8
    have heq : bs[absOff3]'hoff3 = slice[srcOff3]'hoff3_sl := by
      simp only [absOff3, ambientAbsOff, srcOff3]
      have hrel : srcOff3 < len := by
        have : srcOff3 < slice.length := hoff3_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff3 hbound hrel hoff3_sl hoff3).symm
    have h' := hgeF8; rw [heq] at h'
    exact hll_vacuous_of_short_list_item slice listOff items 3
      hencInner hshort hn3 hoff3_sl h'
  have hls4 :
      ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + k)) = true := by
    intro hlo hhi
    have heq : bs[absOff4]'hoff4 = slice[srcOff4]'hoff4_sl := by
      simp only [absOff4, ambientAbsOff, srcOff4]
      have hrel : srcOff4 < len := by
        have : srcOff4 < slice.length := hoff4_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff4 hbound hrel hoff4_sl hoff4).symm
    have hlo' := hlo; rw [heq] at hlo'
    have hhi' := hhi; rw [heq] at hhi'
    exact hls_vacuous_of_short_list_item slice listOff items 4
      hencInner hshort hn4 hoff4_sl hlo' hhi'
  have hll4 :
      ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + k)) = true := by
    intro hgeF8
    have heq : bs[absOff4]'hoff4 = slice[srcOff4]'hoff4_sl := by
      simp only [absOff4, ambientAbsOff, srcOff4]
      have hrel : srcOff4 < len := by
        have : srcOff4 < slice.length := hoff4_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff4 hbound hrel hoff4_sl hoff4).symm
    have h' := hgeF8; rw [heq] at h'
    exact hll_vacuous_of_short_list_item slice listOff items 4
      hencInner hshort hn4 hoff4_sl h'
  have hls5 :
      ¬ BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        absOff5 + 1 + ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff5 + 1 +
          ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff5 + 1 + k)) = true := by
    intro hlo hhi
    have heq : bs[absOff5]'hoff5 = slice[srcOff5]'hoff5_sl := by
      simp only [absOff5, ambientAbsOff, srcOff5]
      have hrel : srcOff5 < len := by
        have : srcOff5 < slice.length := hoff5_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff5 hbound hrel hoff5_sl hoff5).symm
    have hlo' := hlo; rw [heq] at hlo'
    have hhi' := hhi; rw [heq] at hhi'
    exact hls_vacuous_of_short_list_item slice listOff items 5
      hencInner hshort hn5 hoff5_sl hlo' hhi'
  have hll5 :
      ¬ BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        absOff5 + 1 + ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff5 + 1 +
          ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff5 + 1 + k)) = true := by
    intro hgeF8
    have heq : bs[absOff5]'hoff5 = slice[srcOff5]'hoff5_sl := by
      simp only [absOff5, ambientAbsOff, srcOff5]
      have hrel : srcOff5 < len := by
        have : srcOff5 < slice.length := hoff5_sl
        rwa [hlen_sl] at this
      exact (txSlice_getElem_eq bs off len srcOff5 hbound hrel hoff5_sl hoff5).symm
    have h' := hgeF8; rw [heq] at h'
    exact hll_vacuous_of_short_list_item slice listOff items 5
      hencInner hshort hn5 hoff5_sl h'
  have hoff_list : absListOff < bs.length := by
    have hrel : listOff < len := by
      have : listOff < slice.length := hoffInner
      rwa [hlen_sl] at this
    simpa [absListOff, ambientAbsOff] using absOff_lt_bs bs off len listOff hbound hrel
  have hge_hi :=
    walk_init_ge_hi_ambient regionBase loadPtr bs off len listOff hptr hbound
      hoffInner h_ge_sl h_hi_sl hoff_list
  have h_ge := hge_hi.1
  have h_hi := hge_hi.2
  have h_exact :=
    walk_init_exact_ambient regionBase loadPtr
      (lenW - (teerTxTypeDispatch slice).2.2) bs off len listOff
      hptr hbound hoffInner hspan_list h_exact_sl hoff_list
  have hoff := hoff_list
  have hspan : regionBase.toNat + (off + listOff) < 2 ^ 64 := hspan_list
  exact extractAssumed_copy_under_honesty_of_decode_short_concrete_region_ambient
    sp0 spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len
    absOff0 absOff1 absOff2 absOff3 absOff4 absOff5 q
    hspC hret hcur hne0 hne1 hsalign
    hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
    hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hnext1 hnext2 hnext3 hnext4 hnext5 hlen20 hnext_content
    hq hcover hcvalid
    htalign htover htvalid hlen hty0 hover hvalidTx0
    hoff hinover hinvalid hspan hptr hbound hlistLen_ne h_ge h_hi h_exact

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_shortConcrete_pure_ambient_fullCode
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (items : List EL.RLP.RLPItem)
    (q : Nat)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1 =
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
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidTx0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (hinover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0))) = true)
    (hvalid1_0 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0) + 1)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 0)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next0 len0)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1))) = true)
    (hvalid1_1 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1) + 1)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 1)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next1 len1)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2))) = true)
    (hvalid1_2 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2) + 1)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 2)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next2 len2)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3))) = true)
    (hvalid1_3 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next3 len3)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4))) = true)
    (hvalid1_4 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4) + 1)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next4 len4)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5))) = true)
    (hvalid1_5 : isValidByteAccess (regionBase + BitVec.ofNat 64
      (ambientAbsOff off (shortListSrcOff
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1)) = true)
    (hdec5 : ∃ next5 len5 : Word,
      rlpItemDecode bs
        (ambientAbsOff off (shortListSrcOff
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5)))
        (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
        next5 len5)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_copy_shortConcrete_pure_ambient sp0 spC s
      regionBase loadPtr lenW toBuf isCreationPtr bs off len items q
      hq_align hq hcover hcvalid
      hspC hret htalign htover htvalid hlen hptr hbound hsuccess hcopyFlag hge hdecL hshort
      hsalign hover hvalidTx0 hinover hinvalid
      hvalid0 hvalid1_0 hdec0
      hvalid1 hvalid1_1 hdec1
      hvalid2 hvalid1_2 hdec2
      hvalid3 hvalid1_3 hdec3
      hvalid4 hvalid1_4 hdec4
      hvalid5 hvalid1_5 hdec5
      hge7)

#print axioms extractAssumed_copy_shortConcrete_pure_ambient
#print axioms extractAssumed_copy_shortConcrete_pure_ambient_fullCode

end EvmAsm.Codegen.TxExtractToAddressSpec
