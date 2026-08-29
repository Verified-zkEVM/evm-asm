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
import EvmAsm.Crypto.BeBytesArith
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

/-! ## Pure binary-search model

The linked routine returns an arbitrary matching record when equal hashes are
duplicated.  The model therefore proves membership of a returned match and
existence of a returned match when one is present; it deliberately does not
identify the first duplicate, which is the linear specification's stronger
tie-breaking behavior.
-/

/-- The key stored at an index, with an irrelevant default outside the list. -/
def searchKeyAt (records : List WitnessIndexRecord) (i : Nat) : Nat :=
  match records[i]? with
  | some r => beBytesToNat r.hash
  | none => 0

theorem searchKeyAt_eq (records : List WitnessIndexRecord) (i : Nat)
    (hi : i < records.length) :
    searchKeyAt records i = beBytesToNat (records[i]'hi).hash := by
  simp [searchKeyAt, List.getElem?_eq_getElem hi]

/-- The midpoint of a nonempty half-open interval stays in that interval. -/
theorem midpoint_bounds (lo hi : Nat) (hlo : lo < hi) :
    let mid := (lo + hi) / 2
    lo ≤ mid ∧ mid < hi ∧ mid + 1 ≤ hi := by
  dsimp
  constructor
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
    omega
  constructor
  · apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
    omega
  · apply Nat.succ_le_of_lt
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
    omega

/-- `recordsSorted` lifts to the key function used by the search model. -/
theorem recordsSorted_keyAt_le (records : List WitnessIndexRecord)
    (hs : recordsSorted records) (i j : Nat)
    (hi : i < records.length) (hj : j < records.length) (hij : i ≤ j) :
    searchKeyAt records i ≤ searchKeyAt records j := by
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · rw [searchKeyAt_eq records i hi, searchKeyAt_eq records j hj]
    exact hs i j hi hj hlt
  · rfl

private theorem beBytesToNat_eq_of_length_eq {a b : List (BitVec 8)}
    (hlen : a.length = b.length)
    (h : beBytesToNat a = beBytesToNat b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons bh bt => simp at hlen
  | cons ah atail ih =>
      cases b with
      | nil => simp at hlen
      | cons bh btail =>
          simp only [List.length_cons] at hlen
          have htlen : atail.length = btail.length := by omega
          have hat_lt_a : beBytesToNat atail < 256 ^ atail.length := by
            rw [show (256 : Nat) ^ atail.length = 2 ^ (8 * atail.length) by
              rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]]
            exact beBytesToNat_lt atail
          have hat_lt : beBytesToNat atail < 256 ^ btail.length := by
            rw [← htlen]
            exact hat_lt_a
          have hbt_lt : beBytesToNat btail < 256 ^ btail.length := by
            rw [show (256 : Nat) ^ btail.length = 2 ^ (8 * btail.length) by
              rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]]
            exact beBytesToNat_lt btail
          have hpow : 0 < 256 ^ btail.length := by positivity
          have haquot :
              (ah.toNat * 256 ^ btail.length + beBytesToNat atail) /
                  256 ^ btail.length = ah.toNat := by
            calc
              _ = (beBytesToNat atail + 256 ^ btail.length * ah.toNat) /
                    256 ^ btail.length := by
                      rw [Nat.mul_comm ah.toNat, Nat.add_comm]
              _ = beBytesToNat atail / 256 ^ btail.length + ah.toNat :=
                Nat.add_mul_div_left _ _ hpow
              _ = ah.toNat := by
                rw [Nat.div_eq_of_lt hat_lt]
                simp
          have hbquot :
              (bh.toNat * 256 ^ btail.length + beBytesToNat btail) /
                  256 ^ btail.length = bh.toNat := by
            calc
              _ = (beBytesToNat btail + 256 ^ btail.length * bh.toNat) /
                    256 ^ btail.length := by
                      rw [Nat.mul_comm bh.toNat, Nat.add_comm]
              _ = beBytesToNat btail / 256 ^ btail.length + bh.toNat :=
                Nat.add_mul_div_left _ _ hpow
              _ = bh.toNat := by
                rw [Nat.div_eq_of_lt hbt_lt]
                simp
          have hq := congrArg (fun n => n / 256 ^ btail.length) h
          rw [beBytesToNat_cons, beBytesToNat_cons, htlen] at hq
          rw [haquot, hbquot] at hq
          have hah : ah.toNat = bh.toNat := hq
          have hab : ah = bh := BitVec.eq_of_toNat_eq hah
          subst bh
          have htail : beBytesToNat atail = beBytesToNat btail := by
            rw [beBytesToNat_cons, beBytesToNat_cons] at h
            rw [htlen] at h
            omega
          exact congrArg (fun xs => ah :: xs) (ih htlen htail)

/-- Pure model of `witness_lookup_by_hash_indexed`'s interval search. -/
def searchIndex (records : List WitnessIndexRecord)
    (target : List (BitVec 8)) (lo hi : Nat) : Option Nat :=
  if _h : lo < hi then
    let mid := (lo + hi) / 2
    match records[mid]? with
    | none => none
    | some r =>
      let k := beBytesToNat r.hash
      let t := beBytesToNat target
      if k < t then
        searchIndex records target (mid + 1) hi
      else if t < k then
        searchIndex records target lo mid
      else
        some mid
  else
    none
termination_by hi - lo

theorem searchIndex_sound_aux :
    ∀ d : Nat, ∀ (records : List WitnessIndexRecord)
      (target : List (BitVec 8)) (lo hi i : Nat),
      hi - lo = d →
      lo ≤ hi →
      hi ≤ records.length →
      searchIndex records target lo hi = some i →
      lo ≤ i ∧ i < hi ∧ searchKeyAt records i = beBytesToNat target := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro records target lo hi i hd hle hhi hres
      by_cases hlo : lo < hi
      · rw [searchIndex.eq_def, dif_pos hlo] at hres
        let mid := (lo + hi) / 2
        have hmid : lo ≤ mid ∧ mid < hi ∧ mid + 1 ≤ hi :=
          midpoint_bounds lo hi hlo
        have hmidlo : lo ≤ mid := hmid.1
        have hmidhi : mid < hi := hmid.2.1
        have hmidlen : mid < records.length := by omega
        have hres' : (match records[mid]? with
            | none => none
            | some r =>
              let k := beBytesToNat r.hash
              let t := beBytesToNat target
              if k < t then
                searchIndex records target (mid + 1) hi
              else if t < k then
                searchIndex records target lo mid
              else
                some mid) = some i := by
          simpa [mid] using hres
        rw [List.getElem?_eq_getElem hmidlen] at hres'
        dsimp only at hres'
        have hmidkey : searchKeyAt records mid =
            beBytesToNat (records[mid]'hmidlen).hash :=
          searchKeyAt_eq records mid hmidlen
        by_cases hlt : beBytesToNat (records[mid]'hmidlen).hash <
            beBytesToNat target
        · simp only [if_pos hlt] at hres'
          have hmeasure : hi - (mid + 1) < d := by omega
          have hrec := ih (hi - (mid + 1)) hmeasure records target
            (mid + 1) hi i (by omega) (by omega) hhi hres'
          exact ⟨by omega, hrec.2.1, hrec.2.2⟩
        · simp only [if_neg hlt] at hres'
          by_cases hgt : beBytesToNat target <
              beBytesToNat (records[mid]'hmidlen).hash
          · simp only [if_pos hgt] at hres'
            have hmeasure : mid - lo < d := by omega
            have hrec := ih (mid - lo) hmeasure records target lo mid i
              (by omega) hmidlo (by omega) hres'
            exact ⟨hrec.1, by omega, hrec.2.2⟩
          · simp only [if_neg hgt] at hres'
            have hkey : searchKeyAt records mid = beBytesToNat target := by
              rw [hmidkey]
              omega
            have hi_eq : mid = i := by simpa using hres'
            subst i
            exact ⟨hmidlo, hmidhi, hkey⟩
      · rw [searchIndex.eq_def, dif_neg hlo] at hres
        cases hres

theorem searchIndex_sound (records : List WitnessIndexRecord)
    (target : List (BitVec 8)) (lo hi i : Nat)
    (hle : lo ≤ hi) (hhi : hi ≤ records.length)
    (hres : searchIndex records target lo hi = some i) :
    lo ≤ i ∧ i < hi ∧ searchKeyAt records i = beBytesToNat target := by
  exact searchIndex_sound_aux (hi - lo) records target lo hi i rfl hle hhi hres

/-! A binary hit is useful to callers only after its numeric key is tied back
    to the fixed-width hash bytes.  This is the byte-level bridge from the
    search model to `WitnessIndexRecord.matchesSection`; it does not assume
    that the builder produced sorted records. -/

theorem searchIndex_hit_matchesSection
    (records : List WitnessIndexRecord)
    (target section_ : List (BitVec 8)) (i : Nat)
    (htarget_len : target.length = 32)
    (hwf : ∀ r ∈ records, r.WF)
    (hmatches : ∀ r ∈ records, r.matchesSection section_)
    (hres : searchIndex records target 0 records.length = some i) :
    ∃ r, r ∈ records ∧ r.hash = target ∧
      r.offset + r.len ≤ section_.length ∧
      Stateless.SpecRef.keccak256 ((section_.drop r.offset).take r.len) = target := by
  have hsound := searchIndex_sound records target 0 records.length i
    (by omega) (by rfl) hres
  have hi : i < records.length := hsound.2.1
  let r := records[i]'hi
  have hrmem : r ∈ records := by
    dsimp [r]
    exact List.getElem_mem hi
  have hrwf := hwf r hrmem
  have hkey : beBytesToNat r.hash = beBytesToNat target := by
    rw [← searchKeyAt_eq records i hi]
    exact hsound.2.2
  have hhash : r.hash = target := by
    apply beBytesToNat_eq_of_length_eq
    · simpa [r] using hrwf.1.trans htarget_len.symm
    · exact hkey
  have hmatch := hmatches r hrmem
  exact ⟨r, hrmem, hhash, hmatch.1, by rw [← hmatch.2, hhash]⟩

theorem searchIndex_complete_aux :
    ∀ d : Nat, ∀ (records : List WitnessIndexRecord)
      (target : List (BitVec 8)) (lo hi : Nat),
      hi - lo = d →
      lo ≤ hi →
      hi ≤ records.length →
      recordsSorted records →
      (∃ j, lo ≤ j ∧ j < hi ∧
        searchKeyAt records j = beBytesToNat target) →
      ∃ i, searchIndex records target lo hi = some i := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro records target lo hi hd hle hhi hs hmatch
      by_cases hlo : lo < hi
      · rw [searchIndex.eq_def, dif_pos hlo]
        let mid := (lo + hi) / 2
        have hmid : lo ≤ mid ∧ mid < hi ∧ mid + 1 ≤ hi :=
          midpoint_bounds lo hi hlo
        have hmidlo : lo ≤ mid := hmid.1
        have hmidhi : mid < hi := hmid.2.1
        have hmidlen : mid < records.length := by omega
        change ∃ i, (match records[mid]? with
            | none => none
            | some r =>
              let k := beBytesToNat r.hash
              let t := beBytesToNat target
              if k < t then searchIndex records target (mid + 1) hi
              else if t < k then searchIndex records target lo mid
              else some mid) = some i
        rw [List.getElem?_eq_getElem hmidlen]
        dsimp only
        rcases hmatch with ⟨j, hjlo, hjhi, hjkey⟩
        have hjlen : j < records.length := by omega
        have hmidkey : searchKeyAt records mid =
            beBytesToNat (records[mid]'hmidlen).hash :=
          searchKeyAt_eq records mid hmidlen
        by_cases hlt : beBytesToNat (records[mid]'hmidlen).hash <
            beBytesToNat target
        · have hjnotle : ¬ j ≤ mid := by
            intro hjmid
            have hkeys := recordsSorted_keyAt_le records hs j mid hjlen hmidlen hjmid
            rw [hjkey, hmidkey] at hkeys
            omega
          have hjright : mid + 1 ≤ j := by omega
          have hmatch_right :
              ∃ k, mid + 1 ≤ k ∧ k < hi ∧
                searchKeyAt records k = beBytesToNat target :=
            ⟨j, hjright, hjhi, hjkey⟩
          have hmeasure : hi - (mid + 1) < d := by omega
          have hrec := ih (hi - (mid + 1)) hmeasure records target
            (mid + 1) hi (by omega) (by omega) hhi hs hmatch_right
          simp only [if_pos hlt]
          exact hrec
        · by_cases hgt : beBytesToNat target <
              beBytesToNat (records[mid]'hmidlen).hash
          · have hjnotge : ¬ mid ≤ j := by
              intro hmidj
              have hkeys := recordsSorted_keyAt_le records hs mid j hmidlen hjlen hmidj
              rw [hmidkey, hjkey] at hkeys
              omega
            have hjleft : j < mid := by omega
            have hmatch_left :
                ∃ k, lo ≤ k ∧ k < mid ∧
                  searchKeyAt records k = beBytesToNat target :=
              ⟨j, hjlo, hjleft, hjkey⟩
            have hmeasure : mid - lo < d := by omega
            have hrec := ih (mid - lo) hmeasure records target lo mid
              (by omega) (by omega) (by omega) hs hmatch_left
            simp only [if_neg hlt, if_pos hgt]
            exact hrec
          · refine ⟨mid, ?_⟩
            simp only [if_neg hlt, if_neg hgt]
      · have h_eq : lo = hi := by omega
        subst h_eq
        rcases hmatch with ⟨j, hjlo, hjhi, hjkey⟩
        omega

theorem searchIndex_complete (records : List WitnessIndexRecord)
    (target : List (BitVec 8)) (hs : recordsSorted records)
    (hmatch : ∃ j, j < records.length ∧
      searchKeyAt records j = beBytesToNat target) :
    ∃ i, searchIndex records target 0 records.length = some i := by
  exact searchIndex_complete_aux records.length records target 0 records.length
    (by simp) (by omega) (by rfl) hs (by simpa using hmatch)

/-- Static domain for the indexed lookup triple. -/
structure IndexedDomain where
  records : List WitnessIndexRecord
  target  : List (BitVec 8)
  htarget_len : target.length = 32
  hsorted : recordsSorted records
  hwf : ∀ r ∈ records, r.WF

/-- The linear reference result retained for the existing cover instances.
    The pure binary-search model above intentionally proves a matching result,
    not equality with this first-match result when duplicate hashes occur. -/
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

/-- Two-record hit: the midpoint is the second record, exercising the
    nontrivial indexed-search branch rather than the one-record cover. -/
def coverTwoRecord0 : WitnessIndexRecord where
  hash := List.replicate 32 (0 : BitVec 8)
  offset := 0
  len := 32

def coverTwoRecord1 : WitnessIndexRecord where
  hash := List.replicate 32 (1 : BitVec 8)
  offset := 32
  len := 32

theorem coverTwoRecord0_wf : coverTwoRecord0.WF := by
  unfold WitnessIndexRecord.WF coverTwoRecord0
  decide

theorem coverTwoRecord1_wf : coverTwoRecord1.WF := by
  unfold WitnessIndexRecord.WF coverTwoRecord1
  decide

def coverTwo : IndexedDomain where
  records := [coverTwoRecord0, coverTwoRecord1]
  target := List.replicate 32 (1 : BitVec 8)
  htarget_len := by decide
  hsorted := by
    intro i j hi hj hij
    have hi_len : i < 2 := by simpa using hi
    have hj_len : j < 2 := by simpa using hj
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl
    · rcases hj' with rfl | rfl
      · omega
      · change beBytesToNat (List.replicate 32 (0 : BitVec 8)) ≤
          beBytesToNat (List.replicate 32 (1 : BitVec 8))
        decide
    · rcases hj' with rfl | rfl
      · omega
      · omega
  hwf := by
    intro r hr
    have hr' : r = coverTwoRecord0 ∨ r = coverTwoRecord1 := by
      simpa using hr
    rcases hr' with rfl | rfl
    · exact coverTwoRecord0_wf
    · exact coverTwoRecord1_wf

theorem coverTwo_search_hit :
    searchIndex coverTwo.records coverTwo.target 0 coverTwo.records.length = some 1 := by
  change searchIndex [coverTwoRecord0, coverTwoRecord1]
      (List.replicate 32 (1 : BitVec 8)) 0 2 = some 1
  simp [searchIndex, coverTwoRecord0, coverTwoRecord1]

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

#print axioms searchIndex_sound
#print axioms searchIndex_complete

end EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
