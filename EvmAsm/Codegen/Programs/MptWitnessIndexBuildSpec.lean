/-
  EvmAsm.Codegen.Programs.MptWitnessIndexBuildSpec

  The builder-side contract boundary for `witness_index_build`.

  The indexed-search proof consumes `recordsSorted`, while the guest builder
  computes records in section order and then mutates that arena in place.  This
  module records the intermediate, unsorted contract explicitly: the record
  list is a permutation of the section-derived list and every record is bound
  to a real section slice.  A small composition theorem then joins explicit
  record-fill, sift-down, and swap triples without hiding any missing machine
  premise.  The sift-down and record/keccak loop triples are deliberately
  parameters for this first tranche; there is no such machine triple in the
  tree yet, so the obligation remains visible at the call site.
-/

import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedSpec
import EvmAsm.Codegen.Proofs.MptWitnessIndexSpec
import EvmAsm.Evm64.WitnessAssertions
import EvmAsm.Crypto.BeBytesBridge
import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Codegen.WitnessIndexBuildSpec

open EvmAsm
open EvmAsm.Rv64
open EvmAsm.Evm64
open EvmAsm.Crypto
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec

/-! ## The list produced by the record/keccak loop -/

/-- The record corresponding to section element `i`.  Its hash is the
    reference keccak digest; the machine loop obtains the same value through
    `zkvm_keccak256` before writing the record header. -/
def recordFillRecord (sectionBytes : List (BitVec 8)) (i : Nat) : WitnessIndexRecord :=
  { hash := Stateless.SpecRef.keccak256 (sszElement sectionBytes i)
    offset := sszSectionOffset sectionBytes i
    len := sszSectionEnd sectionBytes i - sszSectionOffset sectionBytes i }

/-- A finite prefix of the records written by the count-up loop. -/
def recordFillRecords (sectionBytes : List (BitVec 8)) (n : Nat) :
    List WitnessIndexRecord :=
  (List.range n).map (recordFillRecord sectionBytes)

theorem recordFillRecords_eq_indexOfSection (sectionBytes : List (BitVec 8)) :
    recordFillRecords sectionBytes (sszSectionCount sectionBytes) =
      indexOfSection sectionBytes := by
  rfl

/-- The functional post of the record/keccak loop.  The permutation is kept
    even though the initial list is in section order: it is the fact that the
    later in-place heap operations must preserve. -/
def recordFillPost (idxBase sectionPtr : Word)
    (sectionBytes : List (BitVec 8)) (records : List WitnessIndexRecord) : Assertion :=
  assertPure
    (records.Perm (indexOfSection sectionBytes) ∧
      ∀ r ∈ records, r.matchesSection sectionBytes)
    (witnessSectionIs sectionPtr sectionBytes ** witnessIndexIs idxBase records)

theorem recordFillFunctionalPost
    (sectionBytes : List (BitVec 8)) (hwf : sszSectionWF sectionBytes) :
    (recordFillRecords sectionBytes (sszSectionCount sectionBytes)).Perm
        (indexOfSection sectionBytes) ∧
      (∀ r ∈ recordFillRecords sectionBytes (sszSectionCount sectionBytes),
        r.matchesSection sectionBytes) := by
  rw [recordFillRecords_eq_indexOfSection]
  exact ⟨List.Perm.refl _, indexOfSection_matchesSection sectionBytes hwf⟩

theorem recordFillPost_index_holds (idxBase sectionPtr : Word)
    (sectionBytes : List (BitVec 8)) (hwf : sszSectionWF sectionBytes)
    (ps : PartialState)
    (hresource : (witnessSectionIs sectionPtr sectionBytes **
      witnessIndexIs idxBase (indexOfSection sectionBytes)) ps) :
    recordFillPost idxBase sectionPtr sectionBytes (indexOfSection sectionBytes) ps := by
  exact ⟨⟨List.Perm.refl _, indexOfSection_matchesSection sectionBytes hwf⟩, hresource⟩

theorem recordFillPost_perm {idxBase sectionPtr : Word}
    {sectionBytes : List (BitVec 8)} {records : List WitnessIndexRecord}
    {ps : PartialState} (h : recordFillPost idxBase sectionPtr sectionBytes records ps) :
    records.Perm (indexOfSection sectionBytes) := h.1.1

theorem recordFillPost_matches {idxBase sectionPtr : Word}
    {sectionBytes : List (BitVec 8)} {records : List WitnessIndexRecord}
    {ps : PartialState} (h : recordFillPost idxBase sectionPtr sectionBytes records ps) :
    ∀ r ∈ records, r.matchesSection sectionBytes := h.1.2

/-! ## Exact sortedness bridge consumed by indexed search -/

theorem recordsSorted_of_witnessIndexSorted
    {records : List WitnessIndexRecord}
    (h : EvmAsm.Evm64.witnessIndexSorted records) :
    EvmAsm.Codegen.WitnessLookupByHashIndexedSpec.recordsSorted records := by
  unfold EvmAsm.Codegen.WitnessLookupByHashIndexedSpec.recordsSorted
  intro i j hi hj hij
  have hp := (List.pairwise_iff_getElem.mp h) i j hi hj hij
  change EvmAsm.EL.RLP.Nat.fromBytesBE records[i].hash ≤
    EvmAsm.EL.RLP.Nat.fromBytesBE records[j].hash at hp
  change beBytesToNat records[i].hash ≤ beBytesToNat records[j].hash
  rw [EvmAsm.Crypto.fromBytesBE_eq_beBytesToNat,
      EvmAsm.Crypto.fromBytesBE_eq_beBytesToNat] at hp
  exact hp

theorem witnessIndexSorted_of_recordsSorted
    {records : List WitnessIndexRecord}
    (h : EvmAsm.Codegen.WitnessLookupByHashIndexedSpec.recordsSorted records) :
    EvmAsm.Evm64.witnessIndexSorted records := by
  unfold EvmAsm.Evm64.witnessIndexSorted
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hs := h i j hi hj hij
  change beBytesToNat records[i].hash ≤ beBytesToNat records[j].hash at hs
  change EvmAsm.EL.RLP.Nat.fromBytesBE records[i].hash ≤
    EvmAsm.EL.RLP.Nat.fromBytesBE records[j].hash
  rw [EvmAsm.Crypto.beBytesToNat_eq_fromBytesBE,
      EvmAsm.Crypto.beBytesToNat_eq_fromBytesBE] at hs
  exact hs

/-- The final builder post.  Its `codeDbIs` component is intentionally the
    same predicate consumed by `WitnessLookupByHashIndexedSpec`; in particular
    its sortedness field is not a weaker local ordering notion. -/
def builderPost (idxBase sectionPtr : Word)
    (sectionBytes : List (BitVec 8)) (records : List WitnessIndexRecord) : Assertion :=
  assertPure (records.Perm (indexOfSection sectionBytes))
    (codeDbIs idxBase sectionPtr sectionBytes records)

theorem builderPost_recordsSorted {idxBase sectionPtr : Word}
    {sectionBytes : List (BitVec 8)} {records : List WitnessIndexRecord}
    {ps : PartialState} (h : builderPost idxBase sectionPtr sectionBytes records ps) :
    EvmAsm.Codegen.WitnessLookupByHashIndexedSpec.recordsSorted records := by
  exact recordsSorted_of_witnessIndexSorted (codeDbIs_sorted h.2)

/-! ## Explicit phase contracts and their composition -/

/-- The record-fill phase contract.  The phase's machine precondition is left
    as `pre`: it must own the input section, output arena, and all scratch
    state the loop writes.  The result list is explicit, so the permutation and
    hash binding cannot be hidden in an existential post. -/
def recordFillContract (entry exit : Word) (cr : CodeReq)
    (pre : Assertion) (idxBase sectionPtr : Word)
    (sectionBytes : List (BitVec 8)) (records : List WitnessIndexRecord) : Prop :=
  ∃ nSteps : Nat,
    cpsTripleWithin nSteps entry exit cr pre
      (recordFillPost idxBase sectionPtr sectionBytes records)

/-! These names mirror the machine routines.  Keeping the aliases next to the
contracts makes an eventual linked instantiation a replacement of a type
parameter, not a second contract vocabulary. -/

abbrev widxRecordKeccakLoopContract := recordFillContract

/-- A sift-down phase contract, expressed against the same intermediate post.
    A real instantiation must prove that the returned list is still a
    permutation of the section records and that every record remains bound to
    its source slice. -/
def siftDownContract (entry exit : Word) (cr : CodeReq)
    (idxBase sectionPtr : Word) (sectionBytes : List (BitVec 8))
    (before after : List WitnessIndexRecord) : Prop :=
  ∃ nSteps : Nat,
    cpsTripleWithin nSteps entry exit cr
      (recordFillPost idxBase sectionPtr sectionBytes before)
      (recordFillPost idxBase sectionPtr sectionBytes after)

abbrev widxSiftDownContract := siftDownContract

/-- A swap phase contract over the intermediate builder post. -/
def swapContract (entry exit : Word) (cr : CodeReq)
    (idxBase sectionPtr : Word) (sectionBytes : List (BitVec 8))
    (before after : List WitnessIndexRecord) : Prop :=
  ∃ nSteps : Nat,
    cpsTripleWithin nSteps entry exit cr
      (recordFillPost idxBase sectionPtr sectionBytes before)
      (recordFillPost idxBase sectionPtr sectionBytes after)

abbrev widxSwapContract := swapContract

/-- Compose the phases in the order emitted by `witnessIndexBuild_prog`:
    record fill, heapify sift, extraction swap, and extraction sift.  The
    theorem does not manufacture a sift or loop proof: those are explicit
    hypotheses, while the resulting post is the permutation-plus-
    `matchesSection` post consumed by the later heap/sortedness proof. -/
theorem compose_record_fill_heapify_extract
    {entry fillExit heapExit swapExit extractExit : Word} {cr : CodeReq}
    {pre : Assertion} {idxBase sectionPtr : Word}
    {sectionBytes : List (BitVec 8)}
    {records0 records1 records2 records3 : List WitnessIndexRecord}
    (hfill : recordFillContract entry fillExit cr pre idxBase sectionPtr
      sectionBytes records0)
    (hheapify : siftDownContract fillExit heapExit cr idxBase sectionPtr
      sectionBytes records0 records1)
    (hswap : swapContract heapExit swapExit cr idxBase sectionPtr
      sectionBytes records1 records2)
    (hextract : siftDownContract swapExit extractExit cr idxBase sectionPtr
      sectionBytes records2 records3) :
    ∃ nSteps : Nat,
      cpsTripleWithin nSteps entry extractExit cr pre
        (recordFillPost idxBase sectionPtr sectionBytes records3) := by
  rcases hfill with ⟨nFill, hFill⟩
  rcases hheapify with ⟨nHeapify, hHeapify⟩
  rcases hswap with ⟨nSwap, hSwap⟩
  rcases hextract with ⟨nExtract, hExtract⟩
  have h12 := cpsTripleWithin_seq_same_cr hFill hHeapify
  have h123 := cpsTripleWithin_seq_same_cr h12 hSwap
  have h1234 := cpsTripleWithin_seq_same_cr h123 hExtract
  exact ⟨nFill + nHeapify + nSwap + nExtract, h1234⟩

end EvmAsm.Codegen.WitnessIndexBuildSpec
