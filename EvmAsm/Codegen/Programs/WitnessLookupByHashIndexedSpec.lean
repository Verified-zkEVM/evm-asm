/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedSpec

  Whole-routine domain + CodeReq for `witness_lookup_by_hash_indexed`
  (binary search over the sorted `widx_*` arena).

  **Depends on PR #12169** (`witnessLookupByHashIndexed_prog` lives only there).
  This file is NEW and does not edit any #12169 path.

  Reachability (#12144 / #12183): production mpt_walk → wl sites always have
  `widx_enabled = 1` after a successful `witness_index_build`. The indexed arm
  is the only informative discharge domain for the walk residual.

  Machine triple body lands in sibling files; this file locks geometry,
  domain, coverRef, and the CodeReq that includes both callees
  (`widx_record_ptr`, `widx_cmp32`).
-/
import EvmAsm.Codegen.Programs.MptWitnessIndex
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Proofs.MptWitnessIndexSpec
import EvmAsm.Evm64.WitnessAssertions
import EvmAsm.Codegen.Programs.U256MinSAsm
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Codegen.WitnessLookupByHashIndexedSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Evm64
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.U256MinSAsm
open EvmAsm.Crypto

/-! ## Geometry (guest-linked PCs and BSS cells) -/

abbrev IndexedB : Nat := GuestAddrs.witness_lookup_by_hash_indexed
abbrev RecordPtrB : Nat := GuestAddrs.widx_record_ptr
abbrev Cmp32B : Nat := GuestAddrs.widx_cmp32
abbrev WidxCountLoc : Word := (GuestAddrs.widx_count : Word)
abbrev WidxRecordsBase : Word := (GuestAddrs.widx_records : Word)

private abbrev indexedProg : List Instr := witnessLookupByHashIndexed_prog
private abbrev recordPtrProg : List Instr := widxRecordPtr_prog
private abbrev cmp32Prog : List Instr := widxCmp32_prog

set_option maxRecDepth 8000 in
theorem indexed_prog_length : indexedProg.length = 50 := by decide

set_option maxRecDepth 8000 in
theorem record_ptr_prog_length : recordPtrProg.length = 7 := by decide

set_option maxRecDepth 8000 in
theorem cmp32_prog_length : cmp32Prog.length = 16 := by decide

/-! Byte-tie: Spec's parameterized cmp list is the guest Program. -/
set_option maxRecDepth 8000 in
theorem widxCmp32Prog_eq_guest : widxCmp32Prog = cmp32Prog := by decide

/-! ## Frame (sp-64, 8 saved regs: ra + s0..s6 = x1,x8,x9,x18..x22) -/

def indexedFrame : FrameDesc :=
  [ (.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12))
  , (.x18, (24 : BitVec 12)), (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12))
  , (.x21, (48 : BitVec 12)), (.x22, (56 : BitVec 12)) ]

theorem indexedFrame_length : indexedFrame.length = 8 := by decide

/-- Body starts after ADDI-64 + 8×SD = 9 instructions → +36. -/
abbrev bodyEntryPc : Word := (IndexedB : Word) + 36
/-- Loop header `bgeu lo, hi` at prog idx 16 → +64. -/
abbrev loopHdrPc : Word := (IndexedB : Word) + 64
/-- Hit arm (ld off/len) at prog idx 33 → +132. -/
abbrev hitPc : Word := (IndexedB : Word) + 132
/-- Miss `li a0,1` at prog idx 39 → +156. -/
abbrev missPc : Word := (IndexedB : Word) + 156
/-- Epilogue restore at prog idx 40 → +160. -/
abbrev epiPc : Word := (IndexedB : Word) + 160

/-! ## CodeReq: indexed wrapper ∪ record_ptr ∪ cmp32 -/

def wrapperCode : CodeReq := CodeReq.ofProg (IndexedB : Word) indexedProg
def recordPtrCode : CodeReq := CodeReq.ofProg (RecordPtrB : Word) recordPtrProg
def cmp32Code : CodeReq := CodeReq.ofProg (Cmp32B : Word) cmp32Prog

def fullCode : CodeReq :=
  (wrapperCode.union recordPtrCode).union cmp32Code

set_option maxRecDepth 8000 in
theorem wrapper_record_ptr_disjoint : wrapperCode.Disjoint recordPtrCode := by
  unfold wrapperCode recordPtrCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [indexed_prog_length]; decide
  · rw [record_ptr_prog_length]; decide
  · rw [indexed_prog_length, record_ptr_prog_length]; decide

set_option maxRecDepth 8000 in
theorem wrapper_cmp32_disjoint : wrapperCode.Disjoint cmp32Code := by
  unfold wrapperCode cmp32Code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [indexed_prog_length]; decide
  · rw [cmp32_prog_length]; decide
  · rw [indexed_prog_length, cmp32_prog_length]; decide

set_option maxRecDepth 8000 in
theorem record_ptr_cmp32_disjoint : recordPtrCode.Disjoint cmp32Code := by
  unfold recordPtrCode cmp32Code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [record_ptr_prog_length]; decide
  · rw [cmp32_prog_length]; decide
  · rw [record_ptr_prog_length, cmp32_prog_length]; decide

theorem wrapper_in_fullCode :
    ∀ a i, wrapperCode a = some i → fullCode a = some i := by
  intro a i h
  simp only [fullCode, CodeReq.union, h]

theorem record_ptr_in_fullCode :
    ∀ a i, recordPtrCode a = some i → fullCode a = some i := by
  intro a i h
  simp only [fullCode, CodeReq.union]
  cases h1 : wrapperCode a with
  | some _ =>
    rcases wrapper_record_ptr_disjoint a with hnone | hnone
    · simp [h1] at hnone
    · simp [h] at hnone
  | none => simp only [h]

theorem cmp32_in_fullCode :
    ∀ a i, cmp32Code a = some i → fullCode a = some i := by
  intro a i h
  have hd :
      (wrapperCode.union recordPtrCode).Disjoint cmp32Code :=
    CodeReq.Disjoint.union_left wrapper_cmp32_disjoint record_ptr_cmp32_disjoint
  change ((wrapperCode.union recordPtrCode).union cmp32Code) a = some i
  change (match (wrapperCode.union recordPtrCode) a with
    | some j => some j
    | none => cmp32Code a) = some i
  cases h1 : (wrapperCode.union recordPtrCode) a with
  | some _ =>
    rcases hd a with hnone | hnone
    · simp [h1] at hnone
    · simp [h] at hnone
  | none =>
    exact h

/-! ## Domain (static preconditions only)

Production ambient after successful `witness_index_build`:
* `widx_count` holds `records.length`
* arena at `widx_records` is `witnessIndexIs` for those records
* records are hash-sorted (BE) — builder heapsort post
* target hash is 32 bytes at `a2`
* out-offset / out-length cells at `a3` / `a4` are writable dwords

Outcomes in the post (disjunction), not in the pre:
* hit: `a0 = 0`, cells hold some matching record's offset/len
* miss: `a0 = 1`
-/

/-- Big-endian hash order used by `widx_cmp32`. -/
def hashLe (a b : List (BitVec 8)) : Prop :=
  beBytesToNat a ≤ beBytesToNat b

/-- Strict BE order. -/
def hashLt (a b : List (BitVec 8)) : Prop :=
  beBytesToNat a < beBytesToNat b

/-- Sorted ascending by stored hash (builder heapsort post). -/
def recordsSorted (records : List WitnessIndexRecord) : Prop :=
  ∀ (i j : Nat) (hi : i < records.length) (hj : j < records.length),
    i < j → hashLe records[i].hash records[j].hash

/-- Static domain for the indexed lookup triple. -/
structure IndexedDomain where
  records : List WitnessIndexRecord
  target  : List (BitVec 8)
  htarget_len : target.length = 32
  hsorted : recordsSorted records
  hwf : ∀ r ∈ records, r.WF

/-- Semantic result = first matching record (same as linear `witnessLookupSpec`).
    Under `recordsSorted`, binary search returns the same Option. -/
def indexedLookupSpec (d : IndexedDomain) : Option (Nat × Nat) :=
  witnessLookupSpec d.records d.target

/-! ## coverRef (anti-vacuity)

Two decide-closed instances: empty miss, and a one-record hit.
-/

/-- Empty index: miss. -/
def coverEmpty : IndexedDomain where
  records := []
  target := List.replicate 32 (0 : BitVec 8)
  htarget_len := by decide
  hsorted := by
    intro i j hi hj
    simp at hi
  hwf := by intro r hr; cases hr

theorem coverEmpty_lookup_none :
    indexedLookupSpec coverEmpty = none := by
  simp [indexedLookupSpec, witnessLookupSpec, coverEmpty]

/-- One-record hit: hash = target, offset/len concrete. -/
def coverHitRecord : WitnessIndexRecord where
  hash := List.replicate 32 (1 : BitVec 8)
  offset := 0
  len := 32

theorem coverHitRecord_wf : coverHitRecord.WF := by
  unfold WitnessIndexRecord.WF coverHitRecord
  decide

def coverHit : IndexedDomain where
  records := [coverHitRecord]
  target := List.replicate 32 (1 : BitVec 8)
  htarget_len := by decide
  hsorted := by
    intro i j hi hj hij
    have : j < 1 := by simpa using hj
    omega
  hwf := by
    intro r hr
    simp at hr
    subst hr
    exact coverHitRecord_wf

theorem coverHit_lookup_some :
    indexedLookupSpec coverHit = some (0, 32) := by
  unfold indexedLookupSpec witnessLookupSpec coverHit coverHitRecord
  -- find? on [r] with r.hash == target
  simp [List.find?]

/-- Non-vacuity: both hit and miss domains are inhabited. -/
theorem witness_lookup_by_hash_indexed_precondition_reachable :
    (∃ d : IndexedDomain, indexedLookupSpec d = none) ∧
    (∃ d : IndexedDomain, ∃ off len, indexedLookupSpec d = some (off, len)) :=
  ⟨⟨coverEmpty, coverEmpty_lookup_none⟩,
   ⟨coverHit, 0, 32, coverHit_lookup_some⟩⟩

/-! ## ABI / ambient sketch (for the forthcoming machine triple)

Entry (body after frame):
* `x8` = target hash ptr (`a2`)
* `x9` = out-offset cell (`a3`)
* `x18` = out-length cell (`a4`)
* `x19` = lo = 0
* `x20` = hi = `*widx_count`
* `bytesRegion` target (32)
* `witnessIndexIs WidxRecordsBase records`
* `WidxCountLoc ↦ₘ ofNat records.length`
* out cells writable dwords

Post (disjunction via `indexedLookupSpec`):
* hit some: `a0=0`, `*outOff=off`, `*outLen=len`
* miss: `a0=1`
-/

/-- Static upper fuel bound for `cpsTripleWithin`: frame + loop iterations
    each calling record_ptr (7) + cmp32 (293) + branches, plus epi.
    `n` = `records.length` (worst-case linear iterations of a broken search;
    real binary search is log — this is only an upper bound). -/
def indexedFuel (n : Nat) : Nat :=
  50 + n * (20 + 7 + 293)

end EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
