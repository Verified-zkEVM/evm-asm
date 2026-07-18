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
  (nExtractSteps fullCode ExtractAssumed extractLinked_mono)
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

end EvmAsm.Codegen.TxExtractToAddressSpec
