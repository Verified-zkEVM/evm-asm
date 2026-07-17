/-
  Packaging substrate for `tx_extract_to_address` → ExtractAssumed.

  Residual (body Hoare): type_dispatch call + rlp_walk_init + walk_next
  field loops + 20B copy under extractSuccess (frame save/restore in
  Prologue/Epilogue). Callees verified; this file holds linked CodeReq + frame.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxExtractToAddressModel
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps nExtractStackDwords ExtractAssumed fullCode typeCode type_length')
open EvmAsm.Rv64.SAsm (stackFree)

abbrev E : Word := BitVec.ofNat 64 GuestAddrs.tx_extract_to_address
abbrev WI : Word := BitVec.ofNat 64 GuestAddrs.rlp_walk_init
abbrev WN : Word := BitVec.ofNat 64 GuestAddrs.rlp_walk_next

abbrev extractProg : Program := txExtractToAddress_prog
abbrev extractCode : CodeReq := CodeReq.ofProg E extractProg
abbrev walkInitCode : CodeReq := rlp_walk_init_code WI
abbrev walkNextCode : CodeReq := rlp_walk_next_code WN

set_option maxRecDepth 8000 in
theorem extract_length : extractProg.length = 150 := rfl

/-- Linked code for extract body + verified callees (type + walks). -/
def extractLinkedCode : CodeReq :=
  ((extractCode.union typeCode).union walkInitCode).union walkNextCode

private theorem extract_type_disjoint : extractCode.Disjoint typeCode := by
  unfold extractCode typeCode E
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [extract_length]; decide
  · rw [type_length']; decide
  · rw [extract_length, type_length']; decide

theorem extract_mono :
    ∀ a i, extractCode a = some i → extractLinkedCode a = some i := by
  intro a i hi
  unfold extractLinkedCode
  have h1 := CodeReq.union_mono_left (cr1 := extractCode) (cr2 := typeCode) a i hi
  have h2 :=
    CodeReq.union_mono_left (cr1 := extractCode.union typeCode) (cr2 := walkInitCode) a i h1
  exact CodeReq.union_mono_left
    (cr1 := (extractCode.union typeCode).union walkInitCode) (cr2 := walkNextCode) a i h2

theorem type_in_extractLinked :
    ∀ a i, typeCode a = some i → extractLinkedCode a = some i := by
  intro a i hi
  unfold extractLinkedCode
  have h1 := CodeReq.mono_union_right extract_type_disjoint (fun _ _ h => h) a i hi
  have h2 :=
    CodeReq.union_mono_left (cr1 := extractCode.union typeCode) (cr2 := walkInitCode) a i h1
  exact CodeReq.union_mono_left
    (cr1 := (extractCode.union typeCode).union walkInitCode) (cr2 := walkNextCode) a i h2

/-- 9-slot frame in 80B stack: ra, s0–s7 (x8,x9,x18–x23). -/
def extractFrame : FrameDesc :=
  [(.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)),
   (.x18, (24 : BitVec 12)), (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)),
   (.x21, (48 : BitVec 12)), (.x22, (56 : BitVec 12)), (Reg.x23, (64 : BitVec 12))]

theorem extractFrame_length : extractFrame.length = 9 := by decide

structure ExtractSaved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word
  s6 : Word
  s7 : Word

def extractSavedVals (s : ExtractSaved) : Reg → Word
  | .x1  => s.ra
  | .x8  => s.s0
  | .x9  => s.s1
  | .x18 => s.s2
  | .x19 => s.s3
  | .x20 => s.s4
  | .x21 => s.s5
  | .x22 => s.s6
  | Reg.x23 => s.s7
  | _ => 0

/-- Assumed-shaped success pre (sp + free stack + scratch owns; RO blob). -/
def extractAssumedPre (ret spVal txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) ** stackFree spVal nExtractStackDwords **
    (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
    (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
    bytesRegion txBase txBytes **
    memOwn toBuf ** memOwn isCreationPtr **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word))

/-- Assumed-shaped success post (a0=0; sp restored; scratch owns; RO blob). -/
def extractAssumedPost (ret spVal txBase toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) ** stackFree spVal nExtractStackDwords **
    (.x10 ↦ᵣ (0 : Word)) **
    bytesRegion txBase txBytes **
    memOwn toBuf ** memOwn isCreationPtr **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
    regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word))

theorem extractSuccess_implies_type
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes) :
    (TxTypeDispatchSpec.teerTxTypeDispatch txBytes).1 = (0 : Word) :=
  extractSuccess_type_ok txBytes h

#print axioms extractSuccess_type_ok
#print axioms extract_mono
#print axioms extractFrame_length
#print axioms extractSuccess_implies_type

end EvmAsm.Codegen.TxExtractToAddressSpec
