/-
  Assumed-shaped packaging for short type234 creation path.

  Matches `ExtractAssumed.success_flat` footprint under path refinements
  (creation + type234 + short list + items.length ≥ 7). Full structure fill
  still needs copy / legacy / t1 / long-list arms.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedPureHvalid
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedPureHvalidLegacy
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedPureHvalidT1
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalid
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidLegacyRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidT1Region
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedLongConcretePureHvalid
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidJoin
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps fullCode ExtractAssumed extractLinked_mono extractLinkedCode)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)
open EvmAsm.Codegen.TxExtractToAddressHonesty
open EvmAsm.Codegen.TxExtractToAddressModel
open EvmAsm.EL.RLP

/-- Path refinements for the packaged short type234 creation arm. -/
def extractCreationType234ShortPath
    (txBytes : List (BitVec 8)) (items : List EL.RLP.RLPItem) : Prop :=
  extractSuccess txBytes ∧
    (teerExtractToAddress txBytes).2.2 = (1 : Word) ∧
    2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat ∧
    decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items ∧
    (encode.encodeItems items).length ≤ 55 ∧
    7 ≤ items.length

set_option maxRecDepth 8000 in
/-- Assumed footprint under short type234 creation path (statics + path).
    classical-3. Residual: other extractSuccess arms (copy/legacy/t1/long). -/
theorem extractAssumed_success_flat_creation_type234_short
    (ret spVal txBase lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hpath : extractCreationType234ShortPath txBytes items) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨hsuccess, hcreFlag, hge, hdecL, hshort, hge7⟩ := hpath
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
    extractAssumed_creation_shortConcrete_pureHvalid_fullCode
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag hge hdecL hshort
      halign hover hvalidBuf hge7

set_option maxRecDepth 8000 in
/-- Same path theorem under `extractLinkedCode` (no fullCode mono). -/
theorem extractAssumed_success_flat_creation_type234_short_linked
    (ret spVal txBase lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hpath : extractCreationType234ShortPath txBytes items) :
    cpsTripleWithin nExtractSteps E ret extractLinkedCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨hsuccess, hcreFlag, hge, hdecL, hshort, hge7⟩ := hpath
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
    extractAssumed_creation_shortConcrete_pureHvalid
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag hge hdecL hshort
      halign hover hvalidBuf hge7

/-- Entry PC for Assumed discharge. -/
def extractAssumedEntry : Word :=
  BitVec.ofNat 64 GuestAddrs.tx_extract_to_address

theorem extractAssumedEntry_eq_E : extractAssumedEntry = E := rfl

#print axioms extractAssumed_success_flat_creation_type234_short
#print axioms extractAssumed_success_flat_creation_type234_short_linked


/-- Path refinements for short type234 20B-copy arm. -/
def extractCopyType234ShortPath
    (txBytes : List (BitVec 8)) (items : List EL.RLP.RLPItem) : Prop :=
  extractSuccess txBytes ∧
    (teerExtractToAddress txBytes).2.2 = (0 : Word) ∧
    2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat ∧
    decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items ∧
    (encode.encodeItems items).length ≤ 55 ∧
    7 ≤ items.length

set_option maxRecDepth 8000 in
/-- Assumed**content footprint under short type234 copy path.
    Content dwords ambient (cannot drop via sepConj left). classical-3. -/
theorem extractAssumed_content_copy_type234_short
    (ret spVal txBase lenW toBuf isCreationPtr contentPtr w0 w1 w2 : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hcalign : contentPtr.toNat % 8 = 0)
    (hcover : contentPtr.toNat + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess (contentPtr + (16 : Word)) = true)
    (hcontent : contentPtr =
      txBase + BitVec.ofNat 64
        (shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5) +
        (1 : Word))
    (hpath : extractCopyType234ShortPath txBytes items) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes **
        contentDwords contentPtr w0 w1 w2)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes **
        contentDwords contentPtr w0 w1 w2) := by
  obtain ⟨hsuccess, hcopyFlag, hge, hdecL, hshort, hge7⟩ := hpath
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
    extractAssumed_copy_shortConcrete_pureHvalid_fullCode
      spVal spC s txBase lenW toBuf isCreationPtr contentPtr w0 w1 w2 txBytes items
      hspC hret htalign htover htvalid hcalign hcover hcvalid hcontent
      hlen hsuccess hcopyFlag hge hdecL hshort
      halign hover hvalidBuf hge7

#print axioms extractAssumed_content_copy_type234_short

/-- Path refinements for bare short type234 copy with dword-aligned content.
    `shortListSrcOff listOff items 5 + 1 = 8 * q` gates region LD alignment. -/
def extractCopyType234ShortPathRegion
    (txBytes : List (BitVec 8)) (items : List EL.RLP.RLPItem) (q : Nat) : Prop :=
  extractCopyType234ShortPath txBytes items ∧
    shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5 + 1 = 8 * q ∧
    8 * q + 16 < txBytes.length

set_option maxRecDepth 8000 in
/-- Bare Assumed footprint under short type234 copy + aligned content. classical-3. -/
theorem extractAssumed_success_flat_copy_type234_short
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
    (hpath : extractCopyType234ShortPathRegion txBytes items q) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨⟨hsuccess, hcopyFlag, hge, hdecL, hshort, hge7⟩, hq_align, hq⟩ := hpath
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
    extractAssumed_copy_shortConcrete_pureHvalid_region_fullCode
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items q
      hspC hret htalign htover htvalid hq_align hq hcover hcvalid
      hlen hsuccess hcopyFlag hge hdecL hshort
      halign hover hvalidBuf hge7

#print axioms extractAssumed_success_flat_copy_type234_short

/-- Path refinements for the packaged short legacy creation arm. -/
def extractCreationLegacyShortPath
    (txBytes : List (BitVec 8)) (items : List EL.RLP.RLPItem) : Prop :=
  extractSuccess txBytes ∧
    (teerExtractToAddress txBytes).2.2 = (1 : Word) ∧
    (teerTxTypeDispatch txBytes).2.1 = (0 : Word) ∧
    decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items ∧
    (encode.encodeItems items).length ≤ 55 ∧
    5 ≤ items.length

set_option maxRecDepth 8000 in
/-- Assumed footprint under short legacy creation path (statics + path). classical-3. -/
theorem extractAssumed_success_flat_creation_legacy_short
    (ret spVal txBase lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hpath : extractCreationLegacyShortPath txBytes items) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨hsuccess, hcreFlag, htype0, hdecL, hshort, hge5⟩ := hpath
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
    extractAssumed_creation_shortConcrete_pureHvalid_legacy_fullCode
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag htype0 hdecL hshort
      halign hover hvalidBuf hge5

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_creation_legacy_short_linked
    (ret spVal txBase lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hpath : extractCreationLegacyShortPath txBytes items) :
    cpsTripleWithin nExtractSteps E ret extractLinkedCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨hsuccess, hcreFlag, htype0, hdecL, hshort, hge5⟩ := hpath
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
    extractAssumed_creation_shortConcrete_pureHvalid_legacy
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag htype0 hdecL hshort
      halign hover hvalidBuf hge5

#print axioms extractAssumed_success_flat_creation_legacy_short
#print axioms extractAssumed_success_flat_creation_legacy_short_linked


/-- Path refinements for the packaged short t1 creation arm. -/
def extractCreationT1ShortPath
    (txBytes : List (BitVec 8)) (items : List EL.RLP.RLPItem) : Prop :=
  extractSuccess txBytes ∧
    (teerExtractToAddress txBytes).2.2 = (1 : Word) ∧
    (teerTxTypeDispatch txBytes).2.1 = (1 : Word) ∧
    decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items ∧
    (encode.encodeItems items).length ≤ 55 ∧
    6 ≤ items.length

set_option maxRecDepth 8000 in
/-- Assumed footprint under short t1 creation path (statics + path). classical-3. -/
theorem extractAssumed_success_flat_creation_t1_short
    (ret spVal txBase lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hpath : extractCreationT1ShortPath txBytes items) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨hsuccess, hcreFlag, htype1, hdecL, hshort, hge6⟩ := hpath
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
    extractAssumed_creation_shortConcrete_pureHvalid_t1_fullCode
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag htype1 hdecL hshort
      halign hover hvalidBuf hge6

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_creation_t1_short_linked
    (ret spVal txBase lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hpath : extractCreationT1ShortPath txBytes items) :
    cpsTripleWithin nExtractSteps E ret extractLinkedCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨hsuccess, hcreFlag, htype1, hdecL, hshort, hge6⟩ := hpath
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
    extractAssumed_creation_shortConcrete_pureHvalid_t1
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag htype1 hdecL hshort
      halign hover hvalidBuf hge6

#print axioms extractAssumed_success_flat_creation_t1_short
#print axioms extractAssumed_success_flat_creation_t1_short_linked




/-- Path refinements for bare short legacy copy with dword-aligned content. -/
def extractCopyLegacyShortPathRegion
    (txBytes : List (BitVec 8)) (items : List EL.RLP.RLPItem) (q : Nat) : Prop :=
  extractSuccess txBytes ∧
    (teerExtractToAddress txBytes).2.2 = (0 : Word) ∧
    (teerTxTypeDispatch txBytes).2.1 = (0 : Word) ∧
    decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items ∧
    (encode.encodeItems items).length ≤ 55 ∧
    5 ≤ items.length ∧
    shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3 + 1 = 8 * q ∧
    8 * q + 16 < txBytes.length

set_option maxRecDepth 8000 in
/-- Bare Assumed footprint under short legacy copy + aligned content. classical-3. -/
theorem extractAssumed_success_flat_copy_legacy_short
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
    (hpath : extractCopyLegacyShortPathRegion txBytes items q) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨hsuccess, hcopyFlag, htype0, hdecL, hshort, hge5, hq_align, hq⟩ := hpath
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
    extractAssumed_copy_shortConcrete_pureHvalid_legacy_region_fullCode
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items q
      hspC hret htalign htover htvalid hq_align hq hcover hcvalid
      hlen hsuccess hcopyFlag htype0 hdecL hshort
      halign hover hvalidBuf hge5

/-- Path refinements for bare short t1 copy with dword-aligned content. -/
def extractCopyT1ShortPathRegion
    (txBytes : List (BitVec 8)) (items : List EL.RLP.RLPItem) (q : Nat) : Prop :=
  extractSuccess txBytes ∧
    (teerExtractToAddress txBytes).2.2 = (0 : Word) ∧
    (teerTxTypeDispatch txBytes).2.1 = (1 : Word) ∧
    decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items ∧
    (encode.encodeItems items).length ≤ 55 ∧
    6 ≤ items.length ∧
    shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4 + 1 = 8 * q ∧
    8 * q + 16 < txBytes.length

set_option maxRecDepth 8000 in
/-- Bare Assumed footprint under short t1 copy + aligned content. classical-3. -/
theorem extractAssumed_success_flat_copy_t1_short
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
    (hpath : extractCopyT1ShortPathRegion txBytes items q) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨hsuccess, hcopyFlag, htype1, hdecL, hshort, hge6, hq_align, hq⟩ := hpath
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
    extractAssumed_copy_shortConcrete_pureHvalid_t1_region_fullCode
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items q
      hspC hret htalign htover htvalid hq_align hq hcover hcvalid
      hlen hsuccess hcopyFlag htype1 hdecL hshort
      halign hover hvalidBuf hge6

#print axioms extractAssumed_success_flat_copy_legacy_short
#print axioms extractAssumed_success_flat_copy_t1_short


/-- Path refinements for the packaged long type234 creation arm.
    Item short-encode bounds are additional path hyps at the discharge theorem. -/
def extractCreationType234LongPath
    (txBytes : List (BitVec 8)) (items : List EL.RLP.RLPItem) : Prop :=
  extractSuccess txBytes ∧
    (teerExtractToAddress txBytes).2.2 = (1 : Word) ∧
    2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat ∧
    decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items ∧
    55 < (encode.encodeItems items).length ∧
    7 ≤ items.length

set_option maxRecDepth 8000 in
/-- Assumed footprint under long type234 creation path (statics + path + item bounds).
    classical-3. Residual: long copy / multi-tx Option A. -/
theorem extractAssumed_success_flat_creation_type234_long
    (ret spVal txBase lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hpath : extractCreationType234LongPath txBytes items)
    (hitem0 : (encode (items[0]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55)
    (hitem5 : (encode (items[5]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret fullCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨hsuccess, hcreFlag, hge, hdecL, hlong, hge7⟩ := hpath
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
    extractAssumed_creation_longConcrete_pureHvalid_fullCode
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag hge hdecL hlong
      halign hover hvalidBuf
      hitem0 hitem1 hitem2 hitem3 hitem4 hitem5 hge7

set_option maxRecDepth 8000 in
theorem extractAssumed_success_flat_creation_type234_long_linked
    (ret spVal txBase lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hpath : extractCreationType234LongPath txBytes items)
    (hitem0 : (encode (items[0]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55)
    (hitem4 : (encode (items[4]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55)
    (hitem5 : (encode (items[5]'(by
        have := hpath.2.2.2.2.2; omega))).length ≤ 55) :
    cpsTripleWithin nExtractSteps E ret extractLinkedCode
      (extractAssumedPre ret spVal txBase lenW toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes)
      (extractAssumedPost ret spVal txBase toBuf isCreationPtr
        s0 s1 s2 s3 s4 s5 s6 s7 txBytes) := by
  obtain ⟨hsuccess, hcreFlag, hge, hdecL, hlong, hge7⟩ := hpath
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
    extractAssumed_creation_longConcrete_pureHvalid
      spVal spC s txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag hge hdecL hlong
      halign hover hvalidBuf
      hitem0 hitem1 hitem2 hitem3 hitem4 hitem5 hge7

#print axioms extractAssumed_success_flat_creation_type234_long
#print axioms extractAssumed_success_flat_creation_type234_long_linked




end EvmAsm.Codegen.TxExtractToAddressSpec
