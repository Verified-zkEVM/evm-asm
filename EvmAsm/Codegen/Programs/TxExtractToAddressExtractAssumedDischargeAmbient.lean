/-
  Ambient ExtractAssumedAmbient success_flat case-split.

  Packages all 12 path-gated ambient flats under one arm inductive.
  Full structure fill from bare `extractSuccess` remains residual: the pure
  model is wider than the verified assembly domain (copy needs 8-aligned
  content start + cover; long outer needs per-field short-encode; short
  creation needs hgeN past to-field for empty-content hss room). Consumers
  keep `ExtractAssumedAmbient` as a named hyp until domain bridge lands.

  Short-creation ambient flats with residual hgeN only:
  `extractAssumed_success_flat_ambient_creShort{Type234,Legacy,T1}`.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedPureHvalidAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedPureHvalidLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedPureHvalidT1Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedLongConcretePureHvalidAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedLongConcretePureHvalidLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedLongConcretePureHvalidT1Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidT1Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidLongAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidLongLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidLongT1Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.DualReadByteScan (validByteRange isValidByteAccess_of_validByteRange)
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec
  (txSlice teerTxTypeDispatch txSlice_length ambientAbsOff ambientAbsOff_lt)
open EvmAsm.Codegen.TxExtractToAddressModel
  (extractSuccess teerExtractToAddress decodeListItems decodeListItems_some_ne_nil
    toFieldIndex toFieldIndex_legacy toFieldIndex_t1 toFieldIndex_type234
    extractSuccess_type_le4 extractSuccess_decode extractSuccess_copy
    extractSuccess_to_field)
open EvmAsm.Codegen.TxExtractToAddressHonesty
  (encodeItems_le_55_of_decode_short_list_head
    short_list_head_ult_f8_of_decode_hshort
    encodeItems_gt_55_of_decode_long_list_head shortListSrcOff longListSrcOff
    decodeListItems_eq_encode short_list_item_drop long_list_item_drop
    encode_bytes_len20_pfx extractSuccess_copy_encode_addr20)
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (nExtractSteps fullCode)
open EvmAsm.EL.RLP

/-- Cover/valid extras for copy arms (regionBase-dependent; outside path Prop). -/
structure CopyAmbientExtras (regionBase : Word) (q : Nat) : Prop where
  hcover : regionBase.toNat + 8 * q + 16 < 2 ^ 64
  hcvalid : isValidMemAccess
    (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true

/-- Verified ambient extract arm: path Prop + extras flats need beyond path. -/
inductive ExtractAssumedAmbientArm
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat) : Type where
  | creShortType234 (items : List RLPItem)
      (hpath : extractCreationType234ShortPathAmbient bs off len items)
  | creShortLegacy (items : List RLPItem)
      (hpath : extractCreationLegacyShortPathAmbient bs off len items)
  | creShortT1 (items : List RLPItem)
      (hpath : extractCreationT1ShortPathAmbient bs off len items)
  | creLongType234 (items : List RLPItem)
      (hpath : extractCreationType234LongPathAmbient bs off len items)
      (hitem0 : (encode (items[0]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem1 : (encode (items[1]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem2 : (encode (items[2]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem3 : (encode (items[3]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem4 : (encode (items[4]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem5 : (encode (items[5]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
  | creLongLegacy (items : List RLPItem)
      (hpath : extractCreationLegacyLongPathAmbient bs off len items)
      (hitem0 : (encode (items[0]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem1 : (encode (items[1]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem2 : (encode (items[2]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem3 : (encode (items[3]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
  | creLongT1 (items : List RLPItem)
      (hpath : extractCreationT1LongPathAmbient bs off len items)
      (hitem0 : (encode (items[0]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem1 : (encode (items[1]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem2 : (encode (items[2]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem3 : (encode (items[3]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
      (hitem4 : (encode (items[4]'(by have := hpath.2.2.2.2.2; omega))).length ≤ 55)
  | copyShortType234 (items : List RLPItem) (q : Nat)
      (hpath : extractCopyType234ShortPathAmbient bs off len items q)
      (hex : CopyAmbientExtras regionBase q)
  | copyShortLegacy (items : List RLPItem) (q : Nat)
      (hpath : extractCopyLegacyShortPathAmbient bs off len items q)
      (hex : CopyAmbientExtras regionBase q)
  | copyShortT1 (items : List RLPItem) (q : Nat)
      (hpath : extractCopyT1ShortPathAmbient bs off len items q)
      (hex : CopyAmbientExtras regionBase q)
  | copyLongType234 (items : List RLPItem) (q : Nat)
      (hpath : extractCopyType234LongPathAmbient bs off len items q)
      (hex : CopyAmbientExtras regionBase q)
      (hitem0 : (encode (items[0]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
      (hitem1 : (encode (items[1]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
      (hitem2 : (encode (items[2]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
      (hitem3 : (encode (items[3]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
      (hitem4 : (encode (items[4]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
  | copyLongLegacy (items : List RLPItem) (q : Nat)
      (hpath : extractCopyLegacyLongPathAmbient bs off len items q)
      (hex : CopyAmbientExtras regionBase q)
      (hitem0 : (encode (items[0]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
      (hitem1 : (encode (items[1]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
      (hitem2 : (encode (items[2]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
  | copyLongT1 (items : List RLPItem) (q : Nat)
      (hpath : extractCopyT1LongPathAmbient bs off len items q)
      (hex : CopyAmbientExtras regionBase q)
      (hitem0 : (encode (items[0]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
      (hitem1 : (encode (items[1]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
      (hitem2 : (encode (items[2]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)
      (hitem3 : (encode (items[3]'(by have := hpath.2.2.2.2.2.1; omega))).length ≤ 55)

private theorem copyExtras_hcover_assoc (regionBase : Word) (q : Nat)
    (h : regionBase.toNat + 8 * q + 16 < 2 ^ 64) :
    regionBase.toNat + (8 * q + 16) < 2 ^ 64 := by
  omega

set_option maxRecDepth 8000 in
/-- Case-split: any ambient arm + statics ⇒ Assumed success footprint. classical-3. -/
theorem extractAssumed_success_flat_ambient_of_arm
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
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
    (arm : ExtractAssumedAmbientArm regionBase bs off len) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  cases arm with
  | creShortType234 items hpath =>
    exact extractAssumed_success_flat_creation_type234_short_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid hpath
  | creShortLegacy items hpath =>
    exact extractAssumed_success_flat_creation_legacy_short_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid hpath
  | creShortT1 items hpath =>
    exact extractAssumed_success_flat_creation_t1_short_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid hpath
  | creLongType234 items hpath h0 h1 h2 h3 h4 h5 =>
    exact extractAssumed_success_flat_creation_type234_long_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid hpath
      h0 h1 h2 h3 h4 h5
  | creLongLegacy items hpath h0 h1 h2 h3 =>
    exact extractAssumed_success_flat_creation_legacy_long_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid hpath
      h0 h1 h2 h3
  | creLongT1 items hpath h0 h1 h2 h3 h4 =>
    exact extractAssumed_success_flat_creation_t1_long_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid hpath
      h0 h1 h2 h3 h4
  | copyShortType234 items q hpath hex =>
    exact extractAssumed_success_flat_copy_type234_short_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid hpath
      hex.hcover hex.hcvalid
  | copyShortLegacy items q hpath hex =>
    exact extractAssumed_success_flat_copy_legacy_short_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid hpath
      hex.hcover hex.hcvalid
  | copyShortT1 items q hpath hex =>
    exact extractAssumed_success_flat_copy_t1_short_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid hpath
      hex.hcover hex.hcvalid
  | copyLongType234 items q hpath hex h0 h1 h2 h3 h4 =>
    exact extractAssumed_success_flat_copy_type234_long_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid
      (copyExtras_hcover_assoc regionBase q hex.hcover) hex.hcvalid hpath
      h0 h1 h2 h3 h4
  | copyLongLegacy items q hpath hex h0 h1 h2 =>
    exact extractAssumed_success_flat_copy_legacy_long_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid
      hex.hcover hex.hcvalid hpath h0 h1 h2
  | copyLongT1 items q hpath hex h0 h1 h2 h3 =>
    exact extractAssumed_success_flat_copy_t1_long_ambient
      ret spVal regionBase loadPtr lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
      hret hptr hlen hsalign hbound hover hvalidBuf htalign htover htvalid
      hex.hcover hex.hcvalid hpath h0 h1 h2 h3

/-- Every arm implies `extractSuccess` on the slice (path conjunct). -/
theorem extractAssumedAmbientArm_success
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (arm : ExtractAssumedAmbientArm regionBase bs off len) :
    extractSuccess (txSlice bs off len) := by
  cases arm with
  | creShortType234 _ hpath => exact hpath.1
  | creShortLegacy _ hpath => exact hpath.1
  | creShortT1 _ hpath => exact hpath.1
  | creLongType234 _ hpath _ _ _ _ _ _ => exact hpath.1
  | creLongLegacy _ hpath _ _ _ _ => exact hpath.1
  | creLongT1 _ hpath _ _ _ _ _ => exact hpath.1
  | copyShortType234 _ _ hpath _ => exact hpath.1
  | copyShortLegacy _ _ hpath _ => exact hpath.1
  | copyShortT1 _ _ hpath _ => exact hpath.1
  | copyLongType234 _ _ hpath _ _ _ _ _ _ => exact hpath.1
  | copyLongLegacy _ _ hpath _ _ _ _ => exact hpath.1
  | copyLongT1 _ _ hpath _ _ _ _ _ => exact hpath.1

/-- Domain residual: bare `extractSuccess` ↛ arm (copy align/cover, long hitem, hge7).
    Short-creation arms: `hshort` discharged by short-list head; residual `hgeN`
    (one extra item past `to`-field for hss room on empty content). -/
def extractAssumedAmbient_success_flat_domain_residual : True := trivial

/-- Short-list head at inner offset ⇒ `hshort` for ambient short arms. -/
theorem hshort_ambient_of_inner_short_head
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hbound : off + len ≤ bs.length)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true) :
    (encode.encodeItems items).length ≤ 55 := by
  set slice := txSlice bs off len
  set listOff := (teerTxTypeDispatch slice).2.2.toNat
  set inner := slice.drop listOff
  have hdec' : decodeListItems inner = some items := by
    simpa [inner, listOff, slice] using hdec
  have h0' : 0 < inner.length := by simpa [inner, listOff, slice] using h0
  have hhi' :
      BitVec.ult ((inner[0]'h0').zeroExtend 64) (0xf8 : Word) = true := by
    simpa [inner, listOff, slice] using hhi
  have hlen_inner : inner.length < 256 ^ 8 := by
    have hle : inner.length ≤ slice.length := by
      simp only [inner, List.length_drop]; omega
    have hslice : slice.length = len := txSlice_length bs off len hbound
    omega
  exact encodeItems_le_55_of_decode_short_list_head inner items hdec' h0' hlen_inner hhi'

/-- Long-list head at inner offset ⇒ `hlong` for ambient long arms. -/
theorem hlong_ambient_of_inner_long_head
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hbound : off + len ≤ bs.length)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true) :
    55 < (encode.encodeItems items).length := by
  set slice := txSlice bs off len
  set listOff := (teerTxTypeDispatch slice).2.2.toNat
  set inner := slice.drop listOff
  have hdec' : decodeListItems inner = some items := by
    simpa [inner, listOff, slice] using hdec
  have h0' : 0 < inner.length := by simpa [inner, listOff, slice] using h0
  have hge' :
      ¬ BitVec.ult ((inner[0]'h0').zeroExtend 64) (0xf8 : Word) = true := by
    simpa [inner, listOff, slice] using hge_f8
  exact encodeItems_gt_55_of_decode_long_list_head inner items hdec' h0' hge'

/-- Package long type234 creation arm (long head; residual hge7 + hitem0..5). -/
def extractAssumedAmbientArm_creLongType234
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem)
    (hbound : off + len ≤ bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge7 : 7 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by omega))).length ≤ 55)
    (hitem5 : (encode (items[5]'(by omega))).length ≤ 55) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .creLongType234 items
    ⟨hsuccess, hcre, hge, hdec,
      hlong_ambient_of_inner_long_head bs off len items hbound hdec h0 hge_f8, hge7⟩
    hitem0 hitem1 hitem2 hitem3 hitem4 hitem5

/-- Package long legacy creation arm (residual hge5 + hitem0..3). -/
def extractAssumedAmbientArm_creLongLegacy
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem)
    (hbound : off + len ≤ bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge5 : 5 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .creLongLegacy items
    ⟨hsuccess, hcre, htype0, hdec,
      hlong_ambient_of_inner_long_head bs off len items hbound hdec h0 hge_f8, hge5⟩
    hitem0 hitem1 hitem2 hitem3

/-- Package long t1 creation arm (residual hge6 + hitem0..4). -/
def extractAssumedAmbientArm_creLongT1
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem)
    (hbound : off + len ≤ bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge6 : 6 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by omega))).length ≤ 55) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .creLongT1 items
    ⟨hsuccess, hcre, htype1, hdec,
      hlong_ambient_of_inner_long_head bs off len items hbound hdec h0 hge_f8, hge6⟩
    hitem0 hitem1 hitem2 hitem3 hitem4

/-- Package short type234 creation arm (path flags + short head; residual hge7). -/
def extractAssumedAmbientArm_creShortType234
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem)
    (hbound : off + len ≤ bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge7 : 7 ≤ items.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .creShortType234 items
    ⟨hsuccess, hcre, hge, hdec,
      hshort_ambient_of_inner_short_head bs off len items hbound hdec hlen h0 hhi, hge7⟩

/-- Package short legacy creation arm (residual hge5). -/
def extractAssumedAmbientArm_creShortLegacy
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem)
    (hbound : off + len ≤ bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge5 : 5 ≤ items.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .creShortLegacy items
    ⟨hsuccess, hcre, htype0, hdec,
      hshort_ambient_of_inner_short_head bs off len items hbound hdec hlen h0 hhi, hge5⟩

/-- Package short t1 creation arm (residual hge6). -/
def extractAssumedAmbientArm_creShortT1
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem)
    (hbound : off + len ≤ bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge6 : 6 ≤ items.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .creShortT1 items
    ⟨hsuccess, hcre, htype1, hdec,
      hshort_ambient_of_inner_short_head bs off len items hbound hdec hlen h0 hhi, hge6⟩

#print axioms extractAssumed_success_flat_ambient_of_arm
#print axioms extractAssumedAmbientArm_success
#print axioms hshort_ambient_of_inner_short_head
#print axioms hlong_ambient_of_inner_long_head
#print axioms extractAssumedAmbientArm_creShortType234
#print axioms extractAssumedAmbientArm_creLongType234
#print axioms extractAssumedAmbientArm_creShortLegacy
#print axioms extractAssumedAmbientArm_creShortT1

/-! ### Short-creation ambient flats with residual hgeN only

Everything else is discharged from `extractSuccess` + short-list head.
`hgeN` remains residual: empty `to` is a 1-byte `0x80` string, and
`hss_of_short_list_item` needs either encode-length ≥ 2 or a next item
(`n+1 < items.length`) so `srcOff+1` stays inside the payload.
-/

set_option maxRecDepth 8000 in
/-- Short type234 creation ambient Assumed: residual only `hge7`. classical-3. -/
theorem extractAssumed_success_flat_ambient_creShortType234
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_creShortType234 regionBase bs off len items
      hbound hsuccess hcre hge hdec hlen h0 hhi hge7)

set_option maxRecDepth 8000 in
/-- Short legacy creation ambient Assumed: residual only `hge5`. classical-3. -/
theorem extractAssumed_success_flat_ambient_creShortLegacy
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge5 : 5 ≤ items.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_creShortLegacy regionBase bs off len items
      hbound hsuccess hcre htype0 hdec hlen h0 hhi hge5)

set_option maxRecDepth 8000 in
/-- Short t1 creation ambient Assumed: residual only `hge6`. classical-3. -/
theorem extractAssumed_success_flat_ambient_creShortT1
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge6 : 6 ≤ items.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_creShortT1 regionBase bs off len items
      hbound hsuccess hcre htype1 hdec hlen h0 hhi hge6)

/-- Inner drop nonempty from successful `decodeListItems`. -/
theorem decodeListItems_drop_pos
    (bs : List (BitVec 8)) (listOff : Nat) (items : List RLPItem)
    (hdec : decodeListItems (bs.drop listOff) = some items) :
    0 < (bs.drop listOff).length := by
  have hne := decodeListItems_some_ne_nil hdec
  exact List.length_pos_iff.mpr hne

#print axioms extractAssumed_success_flat_ambient_creShortType234
#print axioms extractAssumed_success_flat_ambient_creShortLegacy
#print axioms extractAssumed_success_flat_ambient_creShortT1
#print axioms decodeListItems_drop_pos

/-- Package short type234 creation arm from `hshort` (no head guard). residual hge7. -/
def extractAssumedAmbientArm_creShortType234_of_hshort
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hge7 : 7 ≤ items.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .creShortType234 items ⟨hsuccess, hcre, hge, hdec, hshort, hge7⟩

def extractAssumedAmbientArm_creShortLegacy_of_hshort
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hge5 : 5 ≤ items.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .creShortLegacy items ⟨hsuccess, hcre, htype0, hdec, hshort, hge5⟩

def extractAssumedAmbientArm_creShortT1_of_hshort
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hge6 : 6 ≤ items.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .creShortT1 items ⟨hsuccess, hcre, htype1, hdec, hshort, hge6⟩

/-- `hover` ⇒ `bs.length < 256^8` (for short-head `hshort` bridge). -/
theorem bs_length_lt_256_pow8_of_hover
    (regionBase : Word) (bs : List (BitVec 8))
    (hover : regionBase.toNat + bs.length < 2 ^ 64) :
    bs.length < 256 ^ 8 := by
  have hpow : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have hlt : bs.length < 2 ^ 64 := by omega
  simpa [hpow] using hlt

set_option maxRecDepth 8000 in
/-- Short type234 creation ambient: residual only `hge7` (takes `hshort`). classical-3. -/
theorem extractAssumed_success_flat_ambient_creShortType234_of_hshort
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hge7 : 7 ≤ items.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_creShortType234_of_hshort regionBase bs off len items
      hsuccess hcre hge hdec hshort hge7)

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_creShortLegacy_of_hshort
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hge5 : 5 ≤ items.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_creShortLegacy_of_hshort regionBase bs off len items
      hsuccess hcre htype0 hdec hshort hge5)

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_creShortT1_of_hshort
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hge6 : 6 ≤ items.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_creShortT1_of_hshort regionBase bs off len items
      hsuccess hcre htype1 hdec hshort hge6)

#print axioms TxExtractToAddressHonesty.short_list_head_ult_f8_of_decode_hshort
#print axioms extractAssumed_success_flat_ambient_creShortType234_of_hshort
#print axioms extractAssumed_success_flat_ambient_creShortLegacy_of_hshort
#print axioms extractAssumed_success_flat_ambient_creShortT1_of_hshort
#print axioms bs_length_lt_256_pow8_of_hover



set_option maxRecDepth 8000 in
/-- Long type234 creation ambient: residual `hge7` + `hitem0..5` (hlong from head). classical-3. -/
theorem extractAssumed_success_flat_ambient_creLongType234
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge7 : 7 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by omega))).length ≤ 55)
    (hitem5 : (encode (items[5]'(by omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_creLongType234 regionBase bs off len items
      hbound hsuccess hcre hge hdec h0 hge_f8 hge7
      hitem0 hitem1 hitem2 hitem3 hitem4 hitem5)

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_creLongLegacy
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge5 : 5 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_creLongLegacy regionBase bs off len items
      hbound hsuccess hcre htype0 hdec h0 hge_f8 hge5
      hitem0 hitem1 hitem2 hitem3)

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_creLongT1
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge6 : 6 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_creLongT1 regionBase bs off len items
      hbound hsuccess hcre htype1 hdec h0 hge_f8 hge6
      hitem0 hitem1 hitem2 hitem3 hitem4)

#print axioms hlong_ambient_of_inner_long_head
#print axioms extractAssumed_success_flat_ambient_creLongType234
#print axioms extractAssumed_success_flat_ambient_creLongLegacy
#print axioms extractAssumed_success_flat_ambient_creLongT1

/-! ### Short-copy ambient packaging: residual q + hq_align + hq only

`hcover`/`hcvalid` discharge from statics (`hsalign`/`hover`/`hvalidBuf`) + `hq`.
`hshort` from short-list head (or direct). Path flags still needed:
`hcopyFlag`/`type`/`hdec` (from extractSuccess + case).
-/

/-- Copy cover from ambient span + content dword bound. -/
theorem copyAmbientExtras_of_statics
    (regionBase : Word) (bs : List (BitVec 8)) (q : Nat)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hq : 8 * q + 16 < bs.length) :
    CopyAmbientExtras regionBase q := by
  have hcover : regionBase.toNat + 8 * q + 16 < 2 ^ 64 := by omega
  have hsum : regionBase.toNat + (8 * q + 16) < 2 ^ 64 := by omega
  have hadd :
      regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word) =
        regionBase + BitVec.ofNat 64 (8 * q + 16) := by
    have h16 : (16 : Word) = BitVec.ofNat 64 16 := rfl
    rw [h16, BitVec.add_assoc, BitVec.ofNat_add]
  have haddr :
      (regionBase + BitVec.ofNat 64 (8 * q + 16)).toNat =
        regionBase.toNat + (8 * q + 16) := by
    have ha := regionBase.isLt
    have hk : 8 * q + 16 < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hsum]
  have hbyte :
      isValidByteAccess (regionBase + BitVec.ofNat 64 (8 * q + 16)) = true :=
    isValidByteAccess_of_validByteRange regionBase bs.length (8 * q + 16)
      hvalidBuf hq
  have hmemAddr :
      isValidMemAddr (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true := by
    simpa [isValidByteAccess, hadd] using hbyte
  have hal4 :
      isAligned4 (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true := by
    have : (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)).toNat % 4 = 0 := by
      rw [hadd, haddr]
      have hb : regionBase.toNat % 8 = 0 := hsalign
      omega
    simpa [isAligned4] using this
  exact ⟨hcover, by simp only [isValidMemAccess_eq, hmemAddr, hal4, Bool.and_self]⟩

/-- Package short type234 copy arm (residual q/hq_align/hq; hshort from head). -/
def extractAssumedAmbientArm_copyShortType234
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem) (q : Nat)
    (hbound : off + len ≤ bs.length)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .copyShortType234 items q
    ⟨hsuccess, hcopyFlag, hge, hdec,
      hshort_ambient_of_inner_short_head bs off len items hbound hdec hlen h0 hhi,
      hq_align, hq⟩
    (copyAmbientExtras_of_statics regionBase bs q hsalign hover hvalidBuf hq)

/-- Package short legacy copy arm (residual q/hq_align/hq). -/
def extractAssumedAmbientArm_copyShortLegacy
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem) (q : Nat)
    (hbound : off + len ≤ bs.length)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .copyShortLegacy items q
    ⟨hsuccess, hcopyFlag, htype0, hdec,
      hshort_ambient_of_inner_short_head bs off len items hbound hdec hlen h0 hhi,
      hq_align, hq⟩
    (copyAmbientExtras_of_statics regionBase bs q hsalign hover hvalidBuf hq)

/-- Package short t1 copy arm (residual q/hq_align/hq). -/
def extractAssumedAmbientArm_copyShortT1
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem) (q : Nat)
    (hbound : off + len ≤ bs.length)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .copyShortT1 items q
    ⟨hsuccess, hcopyFlag, htype1, hdec,
      hshort_ambient_of_inner_short_head bs off len items hbound hdec hlen h0 hhi,
      hq_align, hq⟩
    (copyAmbientExtras_of_statics regionBase bs q hsalign hover hvalidBuf hq)

set_option maxRecDepth 8000 in
/-- Short type234 copy ambient Assumed: residual only `q`/`hq_align`/`hq`. classical-3. -/
theorem extractAssumed_success_flat_ambient_copyShortType234
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_copyShortType234 regionBase bs off len items q
      hbound hsalign hover hvalidBuf hsuccess hcopyFlag hge hdec hlen h0 hhi
      hq_align hq)

set_option maxRecDepth 8000 in
/-- Short legacy copy ambient Assumed: residual only `q`/`hq_align`/`hq`. classical-3. -/
theorem extractAssumed_success_flat_ambient_copyShortLegacy
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_copyShortLegacy regionBase bs off len items q
      hbound hsalign hover hvalidBuf hsuccess hcopyFlag htype0 hdec hlen h0 hhi
      hq_align hq)

set_option maxRecDepth 8000 in
/-- Short t1 copy ambient Assumed: residual only `q`/`hq_align`/`hq`. classical-3. -/
theorem extractAssumed_success_flat_ambient_copyShortT1
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hlen : bs.length < 256 ^ 8)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hhi : BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_copyShortT1 regionBase bs off len items q
      hbound hsalign hover hvalidBuf hsuccess hcopyFlag htype1 hdec hlen h0 hhi
      hq_align hq)

/-- Package short type234 copy arm from `hshort` (no head guard). residual q/hq_align/hq. -/
def extractAssumedAmbientArm_copyShortType234_of_hshort
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem) (q : Nat)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .copyShortType234 items q
    ⟨hsuccess, hcopyFlag, hge, hdec, hshort, hq_align, hq⟩
    (copyAmbientExtras_of_statics regionBase bs q hsalign hover hvalidBuf hq)

def extractAssumedAmbientArm_copyShortLegacy_of_hshort
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem) (q : Nat)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .copyShortLegacy items q
    ⟨hsuccess, hcopyFlag, htype0, hdec, hshort, hq_align, hq⟩
    (copyAmbientExtras_of_statics regionBase bs q hsalign hover hvalidBuf hq)

def extractAssumedAmbientArm_copyShortT1_of_hshort
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem) (q : Nat)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .copyShortT1 items q
    ⟨hsuccess, hcopyFlag, htype1, hdec, hshort, hq_align, hq⟩
    (copyAmbientExtras_of_statics regionBase bs q hsalign hover hvalidBuf hq)

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_copyShortType234_of_hshort
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_copyShortType234_of_hshort regionBase bs off len items q
      hsalign hover hvalidBuf hsuccess hcopyFlag hge hdec hshort hq_align hq)

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_copyShortLegacy_of_hshort
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_copyShortLegacy_of_hshort regionBase bs off len items q
      hsalign hover hvalidBuf hsuccess hcopyFlag htype0 hdec hshort hq_align hq)

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_copyShortT1_of_hshort
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_copyShortT1_of_hshort regionBase bs off len items q
      hsalign hover hvalidBuf hsuccess hcopyFlag htype1 hdec hshort hq_align hq)

#print axioms copyAmbientExtras_of_statics
#print axioms extractAssumed_success_flat_ambient_copyShortType234
#print axioms extractAssumed_success_flat_ambient_copyShortLegacy
#print axioms extractAssumed_success_flat_ambient_copyShortT1
#print axioms extractAssumed_success_flat_ambient_copyShortType234_of_hshort
#print axioms extractAssumed_success_flat_ambient_copyShortLegacy_of_hshort
#print axioms extractAssumed_success_flat_ambient_copyShortT1_of_hshort



/-! ### Unified short-copy ambient: residual hshort + q/hq_align/hq

Cases on type (legacy/t1/type234). `hdec`/`hcopyFlag` from path hyps;
`hq_align` uses `toFieldIndex` so one residual shape covers all three.
-/

/-- Package short-copy arm from hshort + aligned content start (any success type). -/
def extractAssumedAmbientArm_copyShort_of_hshort
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem) (q : Nat)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items
          (toFieldIndex (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    ExtractAssumedAmbientArm regionBase bs off len := by
  set slice := txSlice bs off len
  set ty := (teerTxTypeDispatch slice).2.1.toNat
  set listOff := (teerTxTypeDispatch slice).2.2.toNat
  have hle : ty ≤ 4 := by
    simpa [slice, ty] using extractSuccess_type_le4 slice hsuccess
  by_cases h0 : ty = 0
  · have htype0 : (teerTxTypeDispatch slice).2.1 = (0 : Word) := by
      apply BitVec.eq_of_toNat_eq
      simpa [ty, BitVec.toNat_zero] using h0
    have hq_align' :
        ambientAbsOff off (shortListSrcOff listOff items 3) + 1 = 8 * q := by
      simpa [slice, listOff, ty, h0, toFieldIndex_legacy] using hq_align
    exact extractAssumedAmbientArm_copyShortLegacy_of_hshort
      regionBase bs off len items q hsalign hover hvalidBuf hsuccess
      (by simpa [slice] using hcopyFlag) htype0 (by simpa [slice] using hdec)
      hshort hq_align' hq
  · by_cases h1 : ty = 1
    · have htype1 : (teerTxTypeDispatch slice).2.1 = (1 : Word) := by
        apply BitVec.eq_of_toNat_eq
        have : ty = 1 := h1
        simpa [ty, show (1 : Word).toNat = 1 by decide] using this
      have hq_align' :
          ambientAbsOff off (shortListSrcOff listOff items 4) + 1 = 8 * q := by
        simpa [slice, listOff, ty, h0, h1, toFieldIndex_t1] using hq_align
      exact extractAssumedAmbientArm_copyShortT1_of_hshort
        regionBase bs off len items q hsalign hover hvalidBuf hsuccess
        (by simpa [slice] using hcopyFlag) htype1 (by simpa [slice] using hdec)
        hshort hq_align' hq
    · have hge : 2 ≤ ty := by omega
      have hq_align' :
          ambientAbsOff off (shortListSrcOff listOff items 5) + 1 = 8 * q := by
        have hidx : toFieldIndex ty = 5 := toFieldIndex_type234 ty hge hle
        simpa [slice, listOff, ty, hidx] using hq_align
      exact extractAssumedAmbientArm_copyShortType234_of_hshort
        regionBase bs off len items q hsalign hover hvalidBuf hsuccess
        (by simpa [slice] using hcopyFlag) (by simpa [slice, ty] using hge)
        (by simpa [slice] using hdec) hshort hq_align' hq

set_option maxRecDepth 8000 in
/-- Short-copy ambient Assumed unified: residual `hshort` + `q`/`hq_align`/`hq`.
    `hq_align` at `toFieldIndex` content start. classical-3. -/
theorem extractAssumed_success_flat_ambient_copyShort_of_hshort
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hq_align : ambientAbsOff off
        (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items
          (toFieldIndex (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_copyShort_of_hshort regionBase bs off len items q
      hsalign hover hvalidBuf hsuccess hcopyFlag hdec hshort hq_align hq)

set_option maxRecDepth 8000 in
/-- Same residual, but obtain `hdec`/`hcopyFlag` from `extractSuccess` + content-len 20. -/
theorem extractAssumed_success_flat_ambient_copyShort_of_success_hshort
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyLen : (teerExtractToAddress (txSlice bs off len)).2.1.length = 20)
    (hshort : ∀ items,
      decodeListItems
          ((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items →
        (encode.encodeItems items).length ≤ 55)
    (hq_align : ∀ items,
      decodeListItems
          ((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items →
        ambientAbsOff off
            (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items
              (toFieldIndex (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)) + 1 =
          8 * q)
    (hq : 8 * q + 16 < bs.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  set slice := txSlice bs off len
  have hcopyFlag := extractSuccess_copy slice hsuccess hcopyLen
  obtain ⟨items, hdec⟩ := extractSuccess_decode slice hsuccess
  exact extractAssumed_success_flat_ambient_copyShort_of_hshort
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    hsuccess hcopyFlag hdec (hshort items hdec) (hq_align items hdec) hq

#print axioms extractAssumedAmbientArm_copyShort_of_hshort
#print axioms extractAssumed_success_flat_ambient_copyShort_of_hshort
#print axioms extractAssumed_success_flat_ambient_copyShort_of_success_hshort

set_option maxRecDepth 8000 in
/-- Short-copy ambient from extractSuccess + short-list head.
    Residual only `q` / `hq_align` / `hq` (hshort from head; hdec/hcopyFlag from success).
    classical-3. -/
theorem extractAssumed_success_flat_ambient_copyShort_of_success_head
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyLen : (teerExtractToAddress (txSlice bs off len)).2.1.length = 20)
    (hhi : ∀ (h0 : 0 <
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length),
      BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hq_align : ∀ items,
      decodeListItems
          ((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items →
        ambientAbsOff off
            (shortListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items
              (toFieldIndex (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)) + 1 =
          8 * q)
    (hq : 8 * q + 16 < bs.length) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  set slice := txSlice bs off len
  have hcopyFlag := extractSuccess_copy slice hsuccess hcopyLen
  obtain ⟨items, hdec⟩ := extractSuccess_decode slice hsuccess
  have hlen := bs_length_lt_256_pow8_of_hover regionBase bs hover
  have h0 : 0 <
      (slice.drop (teerTxTypeDispatch slice).2.2.toNat).length :=
    decodeListItems_drop_pos slice _ items (by simpa [slice] using hdec)
  have hhi' := hhi (by simpa [slice] using h0)
  have hshort :=
    hshort_ambient_of_inner_short_head bs off len items hbound hdec hlen
      (by simpa [slice] using h0) (by simpa [slice] using hhi')
  exact extractAssumed_success_flat_ambient_copyShort_of_hshort
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    hsuccess hcopyFlag hdec hshort (hq_align items hdec) hq

#print axioms extractAssumed_success_flat_ambient_copyShort_of_success_head




/-! ### Short-copy residual thin: alignment → q/hq_align; content span → hq -/

/-- Absolute content-dword start after the `0x94` prefix of a short-list field. -/
def copyContentStartAbs (off listOff : Nat) (items : List RLPItem) (k : Nat) : Nat :=
  ambientAbsOff off (shortListSrcOff listOff items k) + 1

/-- Canonical content qword index when content start is 8-aligned. -/
def copyContentQ (off listOff : Nat) (items : List RLPItem) (k : Nat) : Nat :=
  copyContentStartAbs off listOff items k / 8

theorem hq_align_of_content_mod8
    (off listOff : Nat) (items : List RLPItem) (k : Nat)
    (halign : copyContentStartAbs off listOff items k % 8 = 0) :
    copyContentStartAbs off listOff items k =
      8 * copyContentQ off listOff items k := by
  have hdvd : 8 ∣ copyContentStartAbs off listOff items k :=
    Nat.dvd_of_mod_eq_zero halign
  simpa [copyContentQ] using (Nat.mul_div_cancel' hdvd).symm

/-- 20-byte short-string field in short list ⇒ content start + 20 ≤ ambient length. -/
theorem copy_content20_span_le_bs
    (bs : List (BitVec 8)) (off len listOff : Nat) (items : List RLPItem) (k : Nat)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : k < items.length)
    (content : List (BitVec 8))
    (hitem : items[k]'hn = .bytes content)
    (hlen20 : content.length = 20) :
    copyContentStartAbs off listOff items k + 20 ≤ bs.length := by
  set slice := txSlice bs off len
  set srcOff := shortListSrcOff listOff items k
  have hdrop := short_list_item_drop slice listOff items k henc hshort hn
  have hencI : encode (items[k]'hn) = BitVec.ofNat 8 0x94 :: content := by
    rw [hitem, encode_bytes_len20_pfx content hlen20]
  have hdrop' :
      slice.drop srcOff =
        BitVec.ofNat 8 0x94 :: (content ++ encode.encodeItems (items.drop (k + 1))) := by
    simpa [srcOff, hencI, List.cons_append] using hdrop
  have hlen_drop : 21 ≤ (slice.drop srcOff).length := by
    rw [hdrop']
    simp only [List.length_cons, List.length_append, hlen20]
    omega
  have hslice_len : slice.length = len := txSlice_length bs off len hbound
  have hsrc_le : srcOff + 21 ≤ len := by
    have hld :
        (slice.drop srcOff).length = slice.length - srcOff := by
      simp only [List.length_drop]
    have hle : srcOff ≤ slice.length := by
      have : 0 < (slice.drop srcOff).length := by omega
      simp only [List.length_drop] at this
      omega
    rw [hld, hslice_len] at hlen_drop
    omega
  have hstart :
      copyContentStartAbs off listOff items k = off + srcOff + 1 := by
    simp only [copyContentStartAbs, ambientAbsOff, srcOff]
  rw [hstart]
  omega

/-- Aligned content start ⇒ `8 * q + 16 < bs.length` for 20B content field. -/
theorem hq_of_copy_content20_aligned
    (bs : List (BitVec 8)) (off len listOff : Nat) (items : List RLPItem) (k : Nat)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : k < items.length)
    (content : List (BitVec 8))
    (hitem : items[k]'hn = .bytes content)
    (hlen20 : content.length = 20)
    (halign : copyContentStartAbs off listOff items k % 8 = 0) :
    8 * copyContentQ off listOff items k + 16 < bs.length := by
  have hspan :=
    copy_content20_span_le_bs bs off len listOff items k hbound henc hshort hn
      content hitem hlen20
  have hq_align := hq_align_of_content_mod8 off listOff items k halign
  omega

set_option maxRecDepth 8000 in
/-- Short-copy ambient from extractSuccess + short-list head + **content-start 8-align**.
    Residual only `halign` (content start % 8 = 0) + short-list head.
    `q`/`hq_align`/`hq` derived. classical-3. -/
theorem extractAssumed_success_flat_ambient_copyShort_of_success_head_aligned
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyLen : (teerExtractToAddress (txSlice bs off len)).2.1.length = 20)
    (hhi : ∀ (h0 : 0 <
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length),
      BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (halign : ∀ items,
      decodeListItems
          ((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items →
        copyContentStartAbs off
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items
            (toFieldIndex (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat) % 8 = 0) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  set slice := txSlice bs off len
  have hcopyFlag := extractSuccess_copy slice hsuccess hcopyLen
  obtain ⟨items, content, hdec, hitem?, hlen20, _hencBytes⟩ :=
    extractSuccess_copy_encode_addr20 slice hsuccess (by simpa [slice] using hcopyFlag)
  have hlen := bs_length_lt_256_pow8_of_hover regionBase bs hover
  have h0 : 0 <
      (slice.drop (teerTxTypeDispatch slice).2.2.toNat).length :=
    decodeListItems_drop_pos slice _ items (by simpa [slice] using hdec)
  have hhi' := hhi (by simpa [slice] using h0)
  have hshort :=
    hshort_ambient_of_inner_short_head bs off len items hbound
      (by simpa [slice] using hdec) hlen
      (by simpa [slice] using h0) (by simpa [slice] using hhi')
  set listOff := (teerTxTypeDispatch slice).2.2.toNat
  set ty := (teerTxTypeDispatch slice).2.1.toNat
  set k := toFieldIndex ty
  set q := copyContentQ off listOff items k
  have hmod : copyContentStartAbs off listOff items k % 8 = 0 := by
    simpa [slice, listOff, ty, k] using
      halign items (by simpa [slice] using hdec)
  have hq_align :
      ambientAbsOff off (shortListSrcOff listOff items k) + 1 = 8 * q := by
    simpa [copyContentStartAbs, q] using
      hq_align_of_content_mod8 off listOff items k hmod
  have hsome : items[k]? = some (RLPItem.bytes content) := by
    simpa [slice, listOff, ty, k] using hitem?
  have hn : k < items.length := (List.getElem?_eq_some_iff.1 hsome).1
  have hitem : items[k]'hn = RLPItem.bytes content :=
    (List.getElem?_eq_some_iff.1 hsome).2
  have henc :
      slice.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ (by simpa [slice, listOff] using hdec)
  have hq :
      8 * q + 16 < bs.length := by
    simpa [q, slice, listOff] using
      hq_of_copy_content20_aligned bs off len listOff items k hbound henc hshort hn
        content hitem hlen20 hmod
  have hq_align' :
      ambientAbsOff off
          (shortListSrcOff (teerTxTypeDispatch slice).2.2.toNat items
            (toFieldIndex (teerTxTypeDispatch slice).2.1.toNat)) + 1 =
        8 * q := by
    simpa [slice, listOff, ty, k] using hq_align
  exact extractAssumed_success_flat_ambient_copyShort_of_hshort
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    hsuccess hcopyFlag (by simpa [slice] using hdec) hshort hq_align' hq

#print axioms hq_align_of_content_mod8
#print axioms copy_content20_span_le_bs
#print axioms hq_of_copy_content20_aligned
#print axioms extractAssumed_success_flat_ambient_copyShort_of_success_head_aligned


/-! ### Long-copy ambient packaging: residual hgeN + hitem + q/hq_align/hq

`hlong` from long-list head. `hcover`/`hcvalid` from statics + `hq`.
Content field hitem is derived inside the long-copy flat (pfx94).
-/

/-- Package long type234 copy arm (long head; residual hge7 + hitem0..4 + q). -/
def extractAssumedAmbientArm_copyLongType234
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem) (q : Nat)
    (hbound : off + len ≤ bs.length)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge7 : 7 ≤ items.length)
    (hq_align : ambientAbsOff off
        (longListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by omega))).length ≤ 55) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .copyLongType234 items q
    ⟨hsuccess, hcopyFlag, hge, hdec,
      hlong_ambient_of_inner_long_head bs off len items hbound hdec h0 hge_f8,
      hge7, hq_align, hq⟩
    (copyAmbientExtras_of_statics regionBase bs q hsalign hover hvalidBuf hq)
    hitem0 hitem1 hitem2 hitem3 hitem4

/-- Package long legacy copy arm (residual hge5 + hitem0..2 + q). -/
def extractAssumedAmbientArm_copyLongLegacy
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem) (q : Nat)
    (hbound : off + len ≤ bs.length)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge5 : 5 ≤ items.length)
    (hq_align : ambientAbsOff off
        (longListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .copyLongLegacy items q
    ⟨hsuccess, hcopyFlag, htype0, hdec,
      hlong_ambient_of_inner_long_head bs off len items hbound hdec h0 hge_f8,
      hge5, hq_align, hq⟩
    (copyAmbientExtras_of_statics regionBase bs q hsalign hover hvalidBuf hq)
    hitem0 hitem1 hitem2

/-- Package long t1 copy arm (residual hge6 + hitem0..3 + q). -/
def extractAssumedAmbientArm_copyLongT1
    (regionBase : Word) (bs : List (BitVec 8)) (off len : Nat)
    (items : List RLPItem) (q : Nat)
    (hbound : off + len ≤ bs.length)
    (hsalign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge6 : 6 ≤ items.length)
    (hq_align : ambientAbsOff off
        (longListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55) :
    ExtractAssumedAmbientArm regionBase bs off len :=
  .copyLongT1 items q
    ⟨hsuccess, hcopyFlag, htype1, hdec,
      hlong_ambient_of_inner_long_head bs off len items hbound hdec h0 hge_f8,
      hge6, hq_align, hq⟩
    (copyAmbientExtras_of_statics regionBase bs q hsalign hover hvalidBuf hq)
    hitem0 hitem1 hitem2 hitem3

set_option maxRecDepth 8000 in
/-- Long type234 copy ambient: residual `hge7` + `hitem0..4` + `q`/`hq_align`/`hq`.
    `hlong` from head; cover from statics. classical-3. -/
theorem extractAssumed_success_flat_ambient_copyLongType234
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge7 : 7 ≤ items.length)
    (hq_align : ambientAbsOff off
        (longListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_copyLongType234 regionBase bs off len items q
      hbound hsalign hover hvalidBuf hsuccess hcopyFlag hge hdec h0 hge_f8 hge7
      hq_align hq hitem0 hitem1 hitem2 hitem3 hitem4)

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_copyLongLegacy
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge5 : 5 ≤ items.length)
    (hq_align : ambientAbsOff off
        (longListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_copyLongLegacy regionBase bs off len items q
      hbound hsalign hover hvalidBuf hsuccess hcopyFlag htype0 hdec h0 hge_f8 hge5
      hq_align hq hitem0 hitem1 hitem2)

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_copyLongT1
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem) (q : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge6 : 6 ≤ items.length)
    (hq_align : ambientAbsOff off
        (longListSrcOff (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4) + 1 =
      8 * q)
    (hq : 8 * q + 16 < bs.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_success_flat_ambient_of_arm
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    (extractAssumedAmbientArm_copyLongT1 regionBase bs off len items q
      hbound hsalign hover hvalidBuf hsuccess hcopyFlag htype1 hdec h0 hge_f8 hge6
      hq_align hq hitem0 hitem1 hitem2 hitem3)

#print axioms extractAssumed_success_flat_ambient_copyLongType234
#print axioms extractAssumed_success_flat_ambient_copyLongLegacy
#print axioms extractAssumed_success_flat_ambient_copyLongT1


/-! ### Long-copy residual thin: alignment → q/hq; content span → hq

Dual of short-copy content-start helpers using `longListSrcOff`.
-/

/-- Absolute content-dword start after the `0x94` prefix of a long-list field. -/
def copyContentStartAbsLong (off listOff : Nat) (items : List RLPItem) (k : Nat) : Nat :=
  ambientAbsOff off (longListSrcOff listOff items k) + 1

def copyContentQLong (off listOff : Nat) (items : List RLPItem) (k : Nat) : Nat :=
  copyContentStartAbsLong off listOff items k / 8

theorem hq_align_of_content_mod8_long
    (off listOff : Nat) (items : List RLPItem) (k : Nat)
    (halign : copyContentStartAbsLong off listOff items k % 8 = 0) :
    copyContentStartAbsLong off listOff items k =
      8 * copyContentQLong off listOff items k := by
  have hdvd : 8 ∣ copyContentStartAbsLong off listOff items k :=
    Nat.dvd_of_mod_eq_zero halign
  simpa [copyContentQLong] using (Nat.mul_div_cancel' hdvd).symm

/-- 20-byte short-string field in long list ⇒ content start + 20 ≤ ambient length. -/
theorem copy_content20_span_le_bs_long
    (bs : List (BitVec 8)) (off len listOff : Nat) (items : List RLPItem) (k : Nat)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hlong : 55 < (encode.encodeItems items).length)
    (hn : k < items.length)
    (content : List (BitVec 8))
    (hitem : items[k]'hn = .bytes content)
    (hlen20 : content.length = 20) :
    copyContentStartAbsLong off listOff items k + 20 ≤ bs.length := by
  set slice := txSlice bs off len
  set srcOff := longListSrcOff listOff items k
  have hdrop := long_list_item_drop slice listOff items k henc hlong hn
  have hencI : encode (items[k]'hn) = BitVec.ofNat 8 0x94 :: content := by
    rw [hitem, encode_bytes_len20_pfx content hlen20]
  have hdrop' :
      slice.drop srcOff =
        BitVec.ofNat 8 0x94 :: (content ++ encode.encodeItems (items.drop (k + 1))) := by
    simpa [srcOff, hencI, List.cons_append] using hdrop
  have hlen_drop : 21 ≤ (slice.drop srcOff).length := by
    rw [hdrop']
    simp only [List.length_cons, List.length_append, hlen20]
    omega
  have hslice_len : slice.length = len := txSlice_length bs off len hbound
  have hsrc_le : srcOff + 21 ≤ len := by
    have hld :
        (slice.drop srcOff).length = slice.length - srcOff := by
      simp only [List.length_drop]
    have hle : srcOff ≤ slice.length := by
      have : 0 < (slice.drop srcOff).length := by omega
      simp only [List.length_drop] at this
      omega
    rw [hld, hslice_len] at hlen_drop
    omega
  have hstart :
      copyContentStartAbsLong off listOff items k = off + srcOff + 1 := by
    simp only [copyContentStartAbsLong, ambientAbsOff, srcOff]
  rw [hstart]
  omega

theorem hq_of_copy_content20_aligned_long
    (bs : List (BitVec 8)) (off len listOff : Nat) (items : List RLPItem) (k : Nat)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hlong : 55 < (encode.encodeItems items).length)
    (hn : k < items.length)
    (content : List (BitVec 8))
    (hitem : items[k]'hn = .bytes content)
    (hlen20 : content.length = 20)
    (halign : copyContentStartAbsLong off listOff items k % 8 = 0) :
    8 * copyContentQLong off listOff items k + 16 < bs.length := by
  have hspan :=
    copy_content20_span_le_bs_long bs off len listOff items k hbound henc hlong hn
      content hitem hlen20
  have hq_align := hq_align_of_content_mod8_long off listOff items k halign
  omega

set_option maxRecDepth 8000 in
/-- Long type234 copy ambient: residual `hge7` + `hitem0..4` + long head + **content-start %8=0**.
    `hlong`/`q`/`hq_align`/`hq` derived. classical-3. -/
theorem extractAssumed_success_flat_ambient_copyLongType234_of_success_head_aligned
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge7 : 7 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by omega))).length ≤ 55)
    (halign : copyContentStartAbsLong off
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 5 % 8 = 0) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  set slice := txSlice bs off len
  set listOff := (teerTxTypeDispatch slice).2.2.toNat
  set k := (5 : Nat)
  set q := copyContentQLong off listOff items k
  have hlong :=
    hlong_ambient_of_inner_long_head bs off len items hbound hdec h0 hge_f8
  have henc :
      slice.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ (by simpa [slice, listOff] using hdec)
  have hmod : copyContentStartAbsLong off listOff items k % 8 = 0 := by
    simpa [slice, listOff, k] using halign
  have hq_align :
      ambientAbsOff off (longListSrcOff listOff items k) + 1 = 8 * q := by
    simpa [copyContentStartAbsLong, q] using
      hq_align_of_content_mod8_long off listOff items k hmod
  obtain ⟨items', content, hdec', hitem?, hlen20, _hencBytes⟩ :=
    extractSuccess_copy_encode_addr20 slice hsuccess (by simpa [slice] using hcopyFlag)
  have hitems : items = items' := by
    have h1 : decodeListItems (slice.drop (teerTxTypeDispatch slice).2.2.toNat) =
        some items := by simpa [slice] using hdec
    have h2 : decodeListItems (slice.drop (teerTxTypeDispatch slice).2.2.toNat) =
        some items' := by simpa [slice] using hdec'
    exact Option.some.inj (h1.symm.trans h2)
  subst hitems
  have hidx : toFieldIndex (teerTxTypeDispatch slice).2.1.toNat = 5 := by
    have hty : 2 ≤ (teerTxTypeDispatch slice).2.1.toNat := by simpa [slice] using hge
    have hle : (teerTxTypeDispatch slice).2.1.toNat ≤ 4 :=
      extractSuccess_type_le4 slice hsuccess
    simpa using toFieldIndex_type234 _ hty hle
  have hsome : items[k]? = some (RLPItem.bytes content) := by
    simpa [slice, k, hidx] using hitem?
  have hn : k < items.length := (List.getElem?_eq_some_iff.1 hsome).1
  have hitem : items[k]'hn = RLPItem.bytes content :=
    (List.getElem?_eq_some_iff.1 hsome).2
  have hq : 8 * q + 16 < bs.length := by
    simpa [q, slice, listOff, k] using
      hq_of_copy_content20_aligned_long bs off len listOff items k hbound henc hlong hn
        content hitem hlen20 hmod
  have hq_align' :
      ambientAbsOff off
          (longListSrcOff (teerTxTypeDispatch slice).2.2.toNat items 5) + 1 =
        8 * q := by
    simpa [slice, listOff, k] using hq_align
  exact extractAssumed_success_flat_ambient_copyLongType234
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    hsuccess hcopyFlag hge hdec h0 hge_f8 hge7 hq_align' hq
    hitem0 hitem1 hitem2 hitem3 hitem4

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_copyLongLegacy_of_success_head_aligned
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge5 : 5 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (halign : copyContentStartAbsLong off
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 3 % 8 = 0) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  set slice := txSlice bs off len
  set listOff := (teerTxTypeDispatch slice).2.2.toNat
  set k := (3 : Nat)
  set q := copyContentQLong off listOff items k
  have hlong :=
    hlong_ambient_of_inner_long_head bs off len items hbound hdec h0 hge_f8
  have henc :
      slice.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ (by simpa [slice, listOff] using hdec)
  have hmod : copyContentStartAbsLong off listOff items k % 8 = 0 := by
    simpa [slice, listOff, k] using halign
  have hq_align :
      ambientAbsOff off (longListSrcOff listOff items k) + 1 = 8 * q := by
    simpa [copyContentStartAbsLong, q] using
      hq_align_of_content_mod8_long off listOff items k hmod
  obtain ⟨items', content, hdec', hitem?, hlen20, _hencBytes⟩ :=
    extractSuccess_copy_encode_addr20 slice hsuccess (by simpa [slice] using hcopyFlag)
  have hitems : items = items' := by
    have h1 : decodeListItems (slice.drop (teerTxTypeDispatch slice).2.2.toNat) =
        some items := by simpa [slice] using hdec
    have h2 : decodeListItems (slice.drop (teerTxTypeDispatch slice).2.2.toNat) =
        some items' := by simpa [slice] using hdec'
    exact Option.some.inj (h1.symm.trans h2)
  subst hitems
  have hidx : toFieldIndex (teerTxTypeDispatch slice).2.1.toNat = 3 := by
    simp [slice, htype0, toFieldIndex_legacy,
      show (0 : Word).toNat = 0 by decide]
  have hsome : items[k]? = some (RLPItem.bytes content) := by
    simpa [slice, k, hidx] using hitem?
  have hn : k < items.length := (List.getElem?_eq_some_iff.1 hsome).1
  have hitem : items[k]'hn = RLPItem.bytes content :=
    (List.getElem?_eq_some_iff.1 hsome).2
  have hq : 8 * q + 16 < bs.length := by
    simpa [q, slice, listOff, k] using
      hq_of_copy_content20_aligned_long bs off len listOff items k hbound henc hlong hn
        content hitem hlen20 hmod
  have hq_align' :
      ambientAbsOff off
          (longListSrcOff (teerTxTypeDispatch slice).2.2.toNat items 3) + 1 =
        8 * q := by
    simpa [slice, listOff, k] using hq_align
  exact extractAssumed_success_flat_ambient_copyLongLegacy
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    hsuccess hcopyFlag htype0 hdec h0 hge_f8 hge5 hq_align' hq
    hitem0 hitem1 hitem2

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_copyLongT1_of_success_head_aligned
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcopyFlag : (teerExtractToAddress (txSlice bs off len)).2.2 = (0 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge6 : 6 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55)
    (halign : copyContentStartAbsLong off
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat items 4 % 8 = 0) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  set slice := txSlice bs off len
  set listOff := (teerTxTypeDispatch slice).2.2.toNat
  set k := (4 : Nat)
  set q := copyContentQLong off listOff items k
  have hlong :=
    hlong_ambient_of_inner_long_head bs off len items hbound hdec h0 hge_f8
  have henc :
      slice.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ (by simpa [slice, listOff] using hdec)
  have hmod : copyContentStartAbsLong off listOff items k % 8 = 0 := by
    simpa [slice, listOff, k] using halign
  have hq_align :
      ambientAbsOff off (longListSrcOff listOff items k) + 1 = 8 * q := by
    simpa [copyContentStartAbsLong, q] using
      hq_align_of_content_mod8_long off listOff items k hmod
  obtain ⟨items', content, hdec', hitem?, hlen20, _hencBytes⟩ :=
    extractSuccess_copy_encode_addr20 slice hsuccess (by simpa [slice] using hcopyFlag)
  have hitems : items = items' := by
    have h1 : decodeListItems (slice.drop (teerTxTypeDispatch slice).2.2.toNat) =
        some items := by simpa [slice] using hdec
    have h2 : decodeListItems (slice.drop (teerTxTypeDispatch slice).2.2.toNat) =
        some items' := by simpa [slice] using hdec'
    exact Option.some.inj (h1.symm.trans h2)
  subst hitems
  have hidx : toFieldIndex (teerTxTypeDispatch slice).2.1.toNat = 4 := by
    simp [slice, htype1, toFieldIndex_t1,
      show (1 : Word).toNat = 1 by decide]
  have hsome : items[k]? = some (RLPItem.bytes content) := by
    simpa [slice, k, hidx] using hitem?
  have hn : k < items.length := (List.getElem?_eq_some_iff.1 hsome).1
  have hitem : items[k]'hn = RLPItem.bytes content :=
    (List.getElem?_eq_some_iff.1 hsome).2
  have hq : 8 * q + 16 < bs.length := by
    simpa [q, slice, listOff, k] using
      hq_of_copy_content20_aligned_long bs off len listOff items k hbound henc hlong hn
        content hitem hlen20 hmod
  have hq_align' :
      ambientAbsOff off
          (longListSrcOff (teerTxTypeDispatch slice).2.2.toNat items 4) + 1 =
        8 * q := by
    simpa [slice, listOff, k] using hq_align
  exact extractAssumed_success_flat_ambient_copyLongT1
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len items q
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    hsuccess hcopyFlag htype1 hdec h0 hge_f8 hge6 hq_align' hq
    hitem0 hitem1 hitem2 hitem3

#print axioms hq_align_of_content_mod8_long
#print axioms copy_content20_span_le_bs_long
#print axioms hq_of_copy_content20_aligned_long
#print axioms extractAssumed_success_flat_ambient_copyLongType234_of_success_head_aligned
#print axioms extractAssumed_success_flat_ambient_copyLongLegacy_of_success_head_aligned
#print axioms extractAssumed_success_flat_ambient_copyLongT1_of_success_head_aligned

/-! ### Long-creation residual thin: empty `to` hitem free + head packaging

Empty creation `to` is `0x80` (encode length 1 ≤ 55) via
`TxExtractToAddressHonesty.extractSuccess_creation_to_field_encode_le55`. Residual after head packaging:
`hgeN` + non-to-field `hitem*` + long-list head.
-/

set_option maxRecDepth 8000 in
/-- Long type234 creation ambient: residual `hge7` + `hitem0..4` + long head.
    `hlong`/`hitem5` (empty `to`) derived. classical-3. -/
theorem extractAssumed_success_flat_ambient_creLongType234_of_success_head
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch (txSlice bs off len)).2.1.toNat)
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge7 : 7 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  set slice := txSlice bs off len
  have hidx : toFieldIndex (teerTxTypeDispatch slice).2.1.toNat = 5 := by
    have hty : 2 ≤ (teerTxTypeDispatch slice).2.1.toNat := by simpa [slice] using hge
    have hle : (teerTxTypeDispatch slice).2.1.toNat ≤ 4 :=
      extractSuccess_type_le4 slice hsuccess
    simpa using toFieldIndex_type234 _ hty hle
  obtain ⟨_hn5, hitem5'⟩ :=
    TxExtractToAddressHonesty.extractSuccess_creation_to_field_encode_le55 slice hsuccess
      (by simpa [slice] using hcre) items (by simpa [slice] using hdec)
  have hitem5 : (encode (items[5]'(by omega))).length ≤ 55 := by
    simpa [hidx] using hitem5'
  exact extractAssumed_success_flat_ambient_creLongType234
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len items
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    hsuccess hcre hge hdec h0 hge_f8 hge7
    hitem0 hitem1 hitem2 hitem3 hitem4 hitem5

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_creLongLegacy_of_success_head
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype0 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (0 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge5 : 5 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  set slice := txSlice bs off len
  have hidx : toFieldIndex (teerTxTypeDispatch slice).2.1.toNat = 3 := by
    have hty : (teerTxTypeDispatch slice).2.1 = (0 : Word) := by simpa [slice] using htype0
    have htyN : (teerTxTypeDispatch slice).2.1.toNat = 0 := by simp [hty]
    simp [htyN, toFieldIndex]
  obtain ⟨_hn3, hitem3'⟩ :=
    TxExtractToAddressHonesty.extractSuccess_creation_to_field_encode_le55 slice hsuccess
      (by simpa [slice] using hcre) items (by simpa [slice] using hdec)
  have hitem3 : (encode (items[3]'(by omega))).length ≤ 55 := by
    simpa [hidx] using hitem3'
  exact extractAssumed_success_flat_ambient_creLongLegacy
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len items
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    hsuccess hcre htype0 hdec h0 hge_f8 hge5
    hitem0 hitem1 hitem2 hitem3

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_ambient_creLongT1_of_success_head
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (items : List RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsalign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hsuccess : extractSuccess (txSlice bs off len))
    (hcre : (teerExtractToAddress (txSlice bs off len)).2.2 = (1 : Word))
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hdec : decodeListItems
        ((txSlice bs off len).drop
          (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) = some items)
    (h0 : 0 <
      ((txSlice bs off len).drop
        (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat).length)
    (hge_f8 : ¬ BitVec.ult
        ((((txSlice bs off len).drop
            (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)[0]'h0
          ).zeroExtend 64) (0xf8 : Word) = true)
    (hge6 : 6 ≤ items.length)
    (hitem0 : (encode (items[0]'(by omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPreAmbient ret spVal loadPtr lenW
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient ret spVal
        s0 s1 s2 s3 s4 s5 s6 s7
        regionBase toBuf isCreationPtr bs) := by
  set slice := txSlice bs off len
  have hidx : toFieldIndex (teerTxTypeDispatch slice).2.1.toNat = 4 := by
    have hty : (teerTxTypeDispatch slice).2.1 = (1 : Word) := by simpa [slice] using htype1
    have htyN : (teerTxTypeDispatch slice).2.1.toNat = 1 := by simp [hty]
    simp [htyN, toFieldIndex]
  obtain ⟨_hn4, hitem4'⟩ :=
    TxExtractToAddressHonesty.extractSuccess_creation_to_field_encode_le55 slice hsuccess
      (by simpa [slice] using hcre) items (by simpa [slice] using hdec)
  have hitem4 : (encode (items[4]'(by omega))).length ≤ 55 := by
    simpa [hidx] using hitem4'
  exact extractAssumed_success_flat_ambient_creLongT1
    ret spVal regionBase loadPtr lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs off len items
    hret hptr hlenW hsalign hbound hover hvalidBuf htalign htover htvalid
    hsuccess hcre htype1 hdec h0 hge_f8 hge6
    hitem0 hitem1 hitem2 hitem3 hitem4

#print axioms extractAssumed_success_flat_ambient_creLongType234_of_success_head
#print axioms extractAssumed_success_flat_ambient_creLongLegacy_of_success_head
#print axioms extractAssumed_success_flat_ambient_creLongT1_of_success_head


end EvmAsm.Codegen.TxExtractToAddressSpec
