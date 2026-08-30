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
import EvmAsm.Codegen.Programs.WcidxSwapRecordsSAsm
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterFold
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
open EvmAsm.Codegen.WcidxSwapRecordsSAsm

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

/-! ## Flat arena bridge for record-level reasoning

`witnessIndexIs` is the structured, recursive assertion used by the builder
contract, while `widx_swap_records` receives one flat byte arena.  The bridge
below makes that representation change explicit.  It is deliberately stated
only for well-formed records: the machine writes exactly a 32-byte hash and
two eight-byte little-endian fields, so a malformed record is not a valid
instantiation of the arena contract.
-/

/-- The byte concatenation represented by a list of witness-index records. -/
def flatRecordBytes : List WitnessIndexRecord → List (BitVec 8)
  | [] => []
  | r :: rest => r.bytes ++ flatRecordBytes rest

theorem setBytes_same_length
    (a b : List (BitVec 8)) (h : a.length = b.length) :
    setBytes a 0 b = b := by
  apply List.ext_getElem
  · rw [length_setBytes, h]
  · intro k hk1 hk2
    have hg := getByteAt_setBytes b a 0 k (by omega)
    rw [if_pos ⟨by omega, by omega⟩] at hg
    have hgl : getByteAt (setBytes a 0 b) k =
        (setBytes a 0 b)[k]'hk1 := by
      unfold getByteAt
      rw [dif_pos]
    have hgr : getByteAt b (k - 0) = b[k]'hk2 := by
      unfold getByteAt
      rw [show k - 0 = k from by omega, dif_pos hk2]
    rw [hgl, hgr] at hg
    exact hg

theorem flatRecordBytes_set
    (records : List WitnessIndexRecord) (i : Nat)
    (r : WitnessIndexRecord)
    (hall : ∀ q ∈ records, q.WF) (hr : r.WF)
    (hi : i < records.length) :
    flatRecordBytes (records.set i r) =
      setBytes (flatRecordBytes records)
        (WITNESS_INDEX_RECORD_BYTES * i) r.bytes := by
  induction records generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
      by_cases hz : i = 0
      · subst i
        have ha_len := a.bytes_length (hall a (by simp))
        have hr_len := r.bytes_length hr
        simp only [List.set, flatRecordBytes, Nat.mul_zero]
        rw [EvmAsm.Rv64.SAsm.setBytes_append_left a.bytes
          (flatRecordBytes rest) r.bytes 0 (by omega),
          setBytes_same_length a.bytes r.bytes (ha_len.trans hr_len.symm)]
      · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
        have hi' : i' < rest.length := by
          simp only [List.length_cons] at hi
          omega
        have hs := ih i' (fun q hq => hall q (by simp [hq])) hi'
        have ha_len := a.bytes_length (hall a (by simp))
        simp only [List.set, flatRecordBytes, Nat.mul_succ]
        rw [EvmAsm.Rv64.SAsm.setBytes_append_right a.bytes
          (flatRecordBytes rest) r.bytes
          (WITNESS_INDEX_RECORD_BYTES * i' + WITNESS_INDEX_RECORD_BYTES)
          (by rw [ha_len]; omega)]
        rw [ha_len]
        rw [show WITNESS_INDEX_RECORD_BYTES * i' + WITNESS_INDEX_RECORD_BYTES -
          WITNESS_INDEX_RECORD_BYTES = WITNESS_INDEX_RECORD_BYTES * i' by omega]
        rw [hs]

theorem flatRecordBytes_swap
    (records : List WitnessIndexRecord) (i j : Nat)
    (hall : ∀ q ∈ records, q.WF)
    (hi : i < records.length) (hj : j < records.length) :
    flatRecordBytes (records.swap i j) =
      setBytes (setBytes (flatRecordBytes records)
        (WITNESS_INDEX_RECORD_BYTES * i) (records[j].bytes))
        (WITNESS_INDEX_RECORD_BYTES * j) (records[i].bytes) := by
  rw [List.swap_eq_of_lt hi hj]
  have hsi : records[i].WF := hall _ (List.getElem_mem hi)
  have hsj : records[j].WF := hall _ (List.getElem_mem hj)
  have hfirst := flatRecordBytes_set records i records[j] hall hsj hi
  have hall_set : ∀ q ∈ records.set i records[j], q.WF := by
    intro q hq
    obtain hq' | hq' := List.mem_or_eq_of_mem_set hq
    · exact hall q hq'
    · simpa [hq'] using hsj
  have hsecond := flatRecordBytes_set (records.set i records[j]) j
    records[i] hall_set hsi (by simpa using hj)
  rw [hsecond, hfirst]

theorem witnessIndexRecordIs_eq_bytesRegion
    {base : Word} {r : WitnessIndexRecord} (hwf : r.WF) :
    witnessIndexRecordIs base r = bytesRegion base r.bytes := by
  funext ps
  exact propext ⟨fun h => h.2, fun h => ⟨hwf, h⟩⟩

theorem bytesRegion_record_append
    (base : Word) (r : WitnessIndexRecord)
    (rest : List WitnessIndexRecord) (hwf : r.WF) :
    bytesRegion base (r.bytes ++ flatRecordBytes rest) =
      (bytesRegion base r.bytes **
        bytesRegion (base + BitVec.ofNat 64 (WITNESS_INDEX_RECORD_BYTES))
          (flatRecordBytes rest)) := by
  have hlen : r.bytes.length = WITNESS_INDEX_RECORD_BYTES :=
    r.bytes_length hwf
  have h8 : WITNESS_INDEX_RECORD_BYTES % 8 = 0 := by decide
  have hn : WITNESS_INDEX_RECORD_BYTES ≤
      (r.bytes ++ flatRecordBytes rest).length := by
    simp [hlen]
  rw [EvmAsm.Evm64.bytesRegion_split base (r.bytes ++ flatRecordBytes rest)
    WITNESS_INDEX_RECORD_BYTES h8 hn]
  simp [hlen]

theorem witnessIndexIs_eq_flatRecordBytes
    (base : Word) (records : List WitnessIndexRecord)
    (hwf : ∀ r ∈ records, r.WF) :
    witnessIndexIs base records = bytesRegion base (flatRecordBytes records) := by
  induction records generalizing base with
  | nil => rfl
  | cons r rest ih =>
      rw [witnessIndexIs_cons, witnessIndexRecordIs_eq_bytesRegion
        (hwf r (by simp)), ih (base := base + BitVec.ofNat 64
          WITNESS_INDEX_RECORD_BYTES) (fun r hr => hwf r (by simp [hr]))]
      rw [← bytesRegion_record_append base r rest (hwf r (by simp))]
      rfl

/-! ## Raw six-dword swap and its byte-level loop model

The older flat triple names the six-dword memory image `widxSwapMem`, while
the deployed SAsm derivation names the same image `swapK` and writes the
source chunks explicitly.  The following lemma discharges that small
representation mismatch.  The layout hypothesis is the same two-record
disjointness needed by the machine swap: it ensures that an earlier dword
round cannot change the source chunk of a later round.
-/

theorem widxSwapMem_succ_eq_swapK_succ
    (arena : List (BitVec 8)) (qa qb n : Nat)
    (hlay : recLayout arena.length (8 * qa) (8 * qb))
    (hn : n < 6)
    (hrec : widxSwapMem arena qa qb n =
      swapK arena (8 * qa) (8 * qb) n) :
    widxSwapMem arena qa qb (n + 1) =
      swapK arena (8 * qa) (8 * qb) (n + 1) := by
  rw [widxSwapMem_succ, swapK, hrec]
  have hA : 8 * (qa + n) + 8 ≤ arena.length := by
    obtain ⟨_, _, hoa, hob, _⟩ := hlay
    omega
  have hB : 8 * (qb + n) + 8 ≤ arena.length := by
    obtain ⟨_, _, hoa, hob, _⟩ := hlay
    omega
  have hca :
      ((swapK arena (8 * qa) (8 * qb) n).drop (8 * (qa + n))).take 8 =
        ((arena.drop (8 * (qa + n))).take 8) := by
    apply chunk_swapK arena (8 * qa) (8 * qb) n n (8 * (qa + n))
      hlay (Nat.le_refl n) hn
    left
    simp [Nat.mul_add]
  have hcb :
      ((swapK arena (8 * qa) (8 * qb) n).drop (8 * (qb + n))).take 8 =
        ((arena.drop (8 * (qb + n))).take 8) := by
    apply chunk_swapK arena (8 * qa) (8 * qb) n n (8 * (qb + n))
      hlay (Nat.le_refl n) hn
    right
    simp [Nat.mul_add]
  have hpa : dwordBytes (packBytes
      (((swapK arena (8 * qa) (8 * qb) n).drop (8 * (qa + n))).take 8)) =
      ((arena.drop (8 * (qa + n))).take 8) := by
    rw [hca]
    apply dwordBytes_packBytes
    simp only [List.length_take, List.length_drop]
    omega
  have hpb : dwordBytes (packBytes
      (((swapK arena (8 * qa) (8 * qb) n).drop (8 * (qb + n))).take 8)) =
      ((arena.drop (8 * (qb + n))).take 8) := by
    rw [hcb]
    apply dwordBytes_packBytes
    simp only [List.length_take, List.length_drop]
    omega
  dsimp only
  rw [hpa, hpb]
  simp [chunk, Nat.mul_add]

theorem widxSwapMem_eq_swapK
    (arena : List (BitVec 8)) (qa qb n : Nat)
    (hlay : recLayout arena.length (8 * qa) (8 * qb))
    (hn : n ≤ 6) :
    widxSwapMem arena qa qb n =
      swapK arena (8 * qa) (8 * qb) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      apply widxSwapMem_succ_eq_swapK_succ arena qa qb n hlay (by omega)
        (ih (by omega))

/-! ## Final transposition of the two records

`swapK` is deliberately expressed as six dword writes.  The builder post,
however, wants the two 48-byte records exchanged as two contiguous slices.
The prefix model below makes that transposition explicit; its induction uses
only the disjointness in `recLayout`, so the machine adapter does not acquire
an unproved heap-specific premise.
-/

/-- The first `k` dwords of a record at byte offset `p`. -/
def recordPrefixBytes (arena : List (BitVec 8)) (p k : Nat) :
    List (BitVec 8) :=
  (arena.drop p).take (8 * k)

theorem recordPrefixBytes_succ (arena : List (BitVec 8)) (p k : Nat) :
    recordPrefixBytes arena p (k + 1) =
      recordPrefixBytes arena p k ++ chunk arena (p + 8 * k) := by
  unfold recordPrefixBytes chunk
  rw [show 8 * (k + 1) = 8 * k + 8 by omega, List.take_add]
  rw [List.drop_drop]

theorem recordPrefixBytes_length (arena : List (BitVec 8)) (p k : Nat)
    (h : p + 8 * k ≤ arena.length) :
    (recordPrefixBytes arena p k).length = 8 * k := by
  simp only [recordPrefixBytes, List.length_take, List.length_drop]
  omega

theorem setBytes_recordPrefix_self (arena : List (BitVec 8)) (p k : Nat)
    (h : p + 8 * k ≤ arena.length) :
    setBytes arena p (recordPrefixBytes arena p k) = arena := by
  simpa [recordPrefixBytes] using setBytes_chunk_self arena p (8 * k) h

theorem setBytes_append_local (xs ys arena : List (BitVec 8)) (k : Nat) :
    setBytes arena k (xs ++ ys) =
      setBytes (setBytes arena k xs) (k + xs.length) ys := by
  induction xs generalizing arena k with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, setBytes_cons, List.length_cons]
      rw [ih]
      congr 1
      omega

/-- Splices into separated windows commute.  The one-sided theorem is kept
    private to this bridge so callers only need the disjunction supplied by
    `recLayout`. -/
theorem setBytes_commute_disjoint
    (arena ns ms : List (BitVec 8)) (i j : Nat)
    (hij : i + ns.length ≤ j)
    (hms : j + ms.length ≤ arena.length) :
    setBytes (setBytes arena i ns) j ms =
      setBytes (setBytes arena j ms) i ns := by
  apply List.ext_getElem
  · simp only [length_setBytes]
  · intro k hk1 hk2
    have hbase : k < arena.length := by
      simpa only [length_setBytes] using hk1
    have hns : i + ns.length ≤ arena.length := by omega
    have hleft := getByteAt_setBytes ns arena i k hns
    have hright := getByteAt_setBytes ms arena j k hms
    have hright' := getByteAt_setBytes ms (setBytes arena i ns) j k (by
      rw [length_setBytes]
      exact hms)
    have hleft' := getByteAt_setBytes ns (setBytes arena j ms) i k (by
      rw [length_setBytes]
      exact hns)
    have hL : getByteAt (setBytes (setBytes arena i ns) j ms) k =
        (setBytes (setBytes arena i ns) j ms)[k]'hk1 := by
      unfold getByteAt
      rw [dif_pos]
    have hR : getByteAt (setBytes (setBytes arena j ms) i ns) k =
        (setBytes (setBytes arena j ms) i ns)[k]'hk2 := by
      unfold getByteAt
      rw [dif_pos]
    rw [← hL, ← hR, hright', hleft', hright, hleft]
    by_cases hki : i ≤ k ∧ k < i + ns.length
    · have hkj : ¬ (j ≤ k ∧ k < j + ms.length) := by omega
      simp [hki, hkj]
    · by_cases hkj : j ≤ k ∧ k < j + ms.length
      · simp [hki, hkj]
      · simp [hki, hkj]

theorem setBytes_commute_separated
    (arena ns ms : List (BitVec 8)) (i j : Nat)
    (hns : i + ns.length ≤ arena.length)
    (hms : j + ms.length ≤ arena.length)
    (hsep : i + ns.length ≤ j ∨ j + ms.length ≤ i) :
    setBytes (setBytes arena i ns) j ms =
      setBytes (setBytes arena j ms) i ns := by
  rcases hsep with hsep | hsep
  · exact setBytes_commute_disjoint arena ns ms i j hsep hms
  · symm
    exact setBytes_commute_disjoint arena ms ns j i hsep hns

theorem swapK_eq_two_setBytes
    (arena : List (BitVec 8)) (oa ob k : Nat)
    (hlay : recLayout arena.length oa ob) (hk : k ≤ 6) :
    swapK arena oa ob k =
      setBytes (setBytes arena oa (recordPrefixBytes arena ob k))
        ob (recordPrefixBytes arena oa k) := by
  obtain ⟨hda, hdb, hoa, hob, hdisj⟩ := hlay
  rcases hdisj with heq | hsep
  · subst ob
    rw [swapK_self arena oa k hk hoa,
      setBytes_recordPrefix_self arena oa k (by omega),
      setBytes_recordPrefix_self arena oa k (by omega)]
  · induction k with
    | zero => simp [swapK, recordPrefixBytes]
    | succ k ih =>
      have hA : ob + 8 * k ≤ arena.length := by omega
      have hB : oa + 8 * k ≤ arena.length := by omega
      have hA_len : (recordPrefixBytes arena ob k).length = 8 * k :=
        recordPrefixBytes_length arena ob k hA
      have hB_len : (recordPrefixBytes arena oa k).length = 8 * k :=
        recordPrefixBytes_length arena oa k hB
      have hC_len : (chunk arena (ob + 8 * k)).length = 8 :=
        length_chunk arena (ob + 8 * k) (by omega)
      have hbase :
          (setBytes arena oa (recordPrefixBytes arena ob k)).length =
            arena.length := length_setBytes _ _ _
      have hAfit : ob + (recordPrefixBytes arena oa k).length ≤
          (setBytes arena oa (recordPrefixBytes arena ob k)).length := by
        rw [hB_len, hbase]
        omega
      have hCfit : oa + 8 * k + (chunk arena (ob + 8 * k)).length ≤
          (setBytes arena oa (recordPrefixBytes arena ob k)).length := by
        rw [hC_len, hbase]
        omega
      have hsep' :
          ob + (recordPrefixBytes arena oa k).length ≤ oa + 8 * k ∨
            oa + 8 * k + (chunk arena (ob + 8 * k)).length ≤ ob := by
        rcases hsep with h | h
        · right
          rw [hC_len]
          omega
        · left
          rw [hB_len]
          omega
      have hcomm := setBytes_commute_separated
          (setBytes arena oa (recordPrefixBytes arena ob k))
          (recordPrefixBytes arena oa k) (chunk arena (ob + 8 * k))
          ob (oa + 8 * k) hAfit hCfit hsep'
      have hAgroup :
          setBytes (setBytes arena oa (recordPrefixBytes arena ob k))
              (oa + 8 * k) (chunk arena (ob + 8 * k)) =
            setBytes arena oa (recordPrefixBytes arena ob (k + 1)) := by
        calc
          _ = setBytes (setBytes arena oa (recordPrefixBytes arena ob k))
                (oa + (recordPrefixBytes arena ob k).length)
                (chunk arena (ob + 8 * k)) := by rw [hA_len]
          _ = setBytes arena oa
                (recordPrefixBytes arena ob k ++ chunk arena (ob + 8 * k)) :=
            (setBytes_append_local (recordPrefixBytes arena ob k)
              (chunk arena (ob + 8 * k)) arena oa).symm
          _ = _ := by
            exact congrArg (fun t => setBytes arena oa t)
              (recordPrefixBytes_succ arena ob k).symm
      have hBgroup :
          setBytes
              (setBytes (setBytes arena oa
                (recordPrefixBytes arena ob (k + 1)))
                ob (recordPrefixBytes arena oa k))
              (ob + 8 * k) (chunk arena (oa + 8 * k)) =
            setBytes (setBytes arena oa
              (recordPrefixBytes arena ob (k + 1)))
              ob (recordPrefixBytes arena oa (k + 1)) := by
        calc
          _ = setBytes
              (setBytes (setBytes arena oa
                (recordPrefixBytes arena ob (k + 1)))
                ob (recordPrefixBytes arena oa k))
              (ob + (recordPrefixBytes arena oa k).length)
              (chunk arena (oa + 8 * k)) := by rw [hB_len]
          _ = setBytes (setBytes arena oa
              (recordPrefixBytes arena ob (k + 1))) ob
              (recordPrefixBytes arena oa k ++ chunk arena (oa + 8 * k)) :=
            (setBytes_append_local (recordPrefixBytes arena oa k)
              (chunk arena (oa + 8 * k))
              (setBytes arena oa (recordPrefixBytes arena ob (k + 1))) ob).symm
          _ = _ := by
            exact congrArg (fun t =>
              setBytes (setBytes arena oa
                (recordPrefixBytes arena ob (k + 1))) ob t)
              (recordPrefixBytes_succ arena oa k).symm
      calc
        swapK arena oa ob (k + 1) =
            setBytes
              (setBytes (setBytes (setBytes arena oa
                (recordPrefixBytes arena ob k))
                ob (recordPrefixBytes arena oa k))
                (oa + 8 * k) (chunk arena (ob + 8 * k)))
              (ob + 8 * k) (chunk arena (oa + 8 * k)) := by
          rw [swapK, ih (by omega)]
        _ = setBytes
              (setBytes
                (setBytes (setBytes arena oa
                  (recordPrefixBytes arena ob k))
                  (oa + 8 * k) (chunk arena (ob + 8 * k)))
                ob (recordPrefixBytes arena oa k))
              (ob + 8 * k) (chunk arena (oa + 8 * k)) := by
          rw [hcomm]
        _ = setBytes
              (setBytes
                (setBytes arena oa (recordPrefixBytes arena ob (k + 1)))
                ob (recordPrefixBytes arena oa k))
              (ob + 8 * k) (chunk arena (oa + 8 * k)) := by
          rw [hAgroup]
        _ = setBytes
              (setBytes arena oa (recordPrefixBytes arena ob (k + 1)))
              ob (recordPrefixBytes arena oa (k + 1)) := by
          exact hBgroup

theorem widxSwapMem_eq_record_transpose
    (arena : List (BitVec 8)) (qa qb : Nat)
    (hlay : recLayout arena.length (8 * qa) (8 * qb)) :
    widxSwapMem arena qa qb 6 =
      setBytes (setBytes arena (8 * qa)
        (recordPrefixBytes arena (8 * qb) 6))
        (8 * qb) (recordPrefixBytes arena (8 * qa) 6) := by
  rw [widxSwapMem_eq_swapK arena qa qb 6 hlay (by decide)]
  exact swapK_eq_two_setBytes arena (8 * qa) (8 * qb) 6 hlay (by decide)

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

/-! ## Finite sift-down fold

The sift loop has two independent quantities in its contract.  The round
count is a structural bound on the selected-child descent; `steps` is a
machine-step bound for one CPS round.  Keeping those quantities as separate
fields prevents a step-count maximum from being mistaken for a well-founded
descent measure.  The fold below supplies only the control-flow induction;
the round and tail records still have to be discharged by the concrete
framed machine proof.
-/

/-- A safe structural bound on child selections for the 131072-record arena.
    This is the heap-depth cap (`2^17 = 131072`), not a CPS instruction
    bound. -/
def widxSiftDownMaxRounds : Nat := 17

/-- Contract for one sift round.  `round` is the structural induction index;
    `steps` bounds only the machine execution of that round.  The terminal
    exits are supplied by the caller and the final exit is the loop back-edge
    carrying the next invariant. -/
structure WidxSiftRoundContract
    (hdr : Word) (cr : CodeReq) (inv : Nat → Assertion)
    (terminal : List (Word × Assertion)) (round : Nat) : Type where
  steps : Nat
  proof : cpsNBranchWithin steps hdr cr (inv round)
    (terminal ++ [(hdr, inv (round + 1))])

/-- Fold explicit per-round contracts through the finite sift-down loop.
    `roundSteps` is a common CPS bound, while `widxSiftDownMaxRounds` is the
    independent structural descent bound.  The terminal continuation is
    intentionally a separate hypothesis so a zero-round case cannot be
    mistaken for a successful terminal arm. -/
theorem widxSiftDown_finite_loop_of_rounds
    {hdr : Word} {cr : CodeReq} {inv : Nat → Assertion}
    {terminal : List (Word × Assertion)}
    (roundSteps : Nat)
    (hround : ∀ round, round < widxSiftDownMaxRounds →
      WidxSiftRoundContract hdr cr inv terminal round)
    (hbound : ∀ round (h_round : round < widxSiftDownMaxRounds),
      (hround round h_round).steps ≤ roundSteps)
    (tailSteps : Nat)
    (htail : cpsNBranchWithin tailSteps hdr cr
      (inv widxSiftDownMaxRounds) terminal) :
    cpsNBranchWithin
      (roundSteps * widxSiftDownMaxRounds + tailSteps)
      hdr cr (inv 0) terminal := by
  have hfold :=
    EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec.finite_nbranch_loop_spec
      (N := widxSiftDownMaxRounds) (m := roundSteps)
      (mLast := tailSteps) (hdr := hdr) (cr := cr)
      (inv := inv) (terminal := terminal)
      (fun round h_round =>
        cpsNBranchWithin_mono_nSteps
          (hbound round h_round)
          (hround round h_round).proof)
      htail
  exact hfold

/-! ## One-step functional leaf

The machine sift routine chooses a child and delegates the only arena write to
`widx_swap_records`.  The leaf-level functional fact needed by the builder is
independent of the heap-order predicate: swapping two slots is a permutation,
so a property quantified over records (such as `matchesSection`) is preserved.
The conversion from the flat `bytesRegion` used by `widx_swap_records` to the
structured `witnessIndexIs` assertion remains a separate machine adapter; this
lemma deliberately does not hide that obligation behind a premise.
-/

/-- The list model of one `widx_sift_down` step: exchange the root slot with
    the selected child.  Out-of-range indices are harmless for the functional
    permutation theorem (`List.swap` is total); the machine contract supplies
    the in-range/arena-validity facts when it is instantiated. -/
def widxSiftDownStep (records : List WitnessIndexRecord)
    (root child : Nat) : List WitnessIndexRecord :=
  records.swap root child

theorem widxSiftDownStep_perm (records : List WitnessIndexRecord)
    (root child : Nat) :
    (widxSiftDownStep records root child).Perm records := by
  exact List.swap_perm records root child

theorem perm_records_preserves_matches
    {sectionBytes : List (BitVec 8)}
    {source records : List WitnessIndexRecord}
    (hperm : records.Perm source)
    (hmatch : ∀ r ∈ source, r.matchesSection sectionBytes) :
    ∀ r ∈ records, r.matchesSection sectionBytes := by
  intro r hr
  apply hmatch r
  exact (hperm.mem_iff).mp hr

/-- **One sift-step functional contract.**  Given the intermediate builder
    facts for the current record list, the selected-child swap preserves both
    permutation of the section-derived records and the per-record
    `matchesSection` binding.  Heap ordering is intentionally absent: it is a
    caller/heapify obligation, not a property of this leaf. -/
theorem widxSiftDownStep_preserves_recordFillFacts
    {sectionBytes : List (BitVec 8)}
    {records : List WitnessIndexRecord}
    (root child : Nat)
    (hperm : records.Perm (indexOfSection sectionBytes))
    (hmatch : ∀ r ∈ records, r.matchesSection sectionBytes) :
    (widxSiftDownStep records root child).Perm (indexOfSection sectionBytes) ∧
      (∀ r ∈ widxSiftDownStep records root child,
        r.matchesSection sectionBytes) := by
  constructor
  · exact (widxSiftDownStep_perm records root child).trans hperm
  · apply perm_records_preserves_matches
      (sectionBytes := sectionBytes)
      (source := records)
      (widxSiftDownStep_perm records root child)
    exact hmatch

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
