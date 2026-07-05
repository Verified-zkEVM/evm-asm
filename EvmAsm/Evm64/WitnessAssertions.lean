/-
  EvmAsm.Evm64.WitnessAssertions

  Separation-logic assertions for the guest's execution-witness data:
  the in-place SSZ `List[ByteList]` sections (state / codes / headers)
  and the sorted hash indexes built over them — including the real
  "code DB".

  ## Layout faithfulness — what the guest ACTUALLY keeps

  **Important**: the reserved scheme-A anchors `EXECUTION_WITNESS_AREA =
  0xa0030000`, `SSZ_INPUT_DECODED = 0xa0020000` and `CODE_DB_BUCKETS =
  0xa0530000` (`EvmAsm/Stateless/MemoryLayout.lean`) are *aspirational*:
  no emitted guest instruction references them, and the live RV64 call
  stack occupies `[0xa0020000, 0xa0050000)` — colliding with the first
  two. That collision is kernel-checked in
  `EvmAsm/Codegen/RegionMap.lean` (`guestStack_overlaps_executionWitnessArea`,
  `guestStack_not_disjoint_from_schemeA`) and filed as a P1 divergence;
  the emitted-reality `guestRegionMap` deliberately excludes those
  anchors. So there is nothing at those addresses to assert over.

  What the guest actually keeps:

  1. **In-place witness sections.** Nothing is decoded *into* a region:
     the SSZ input blob stays at `SSZ_BASE = INPUT + 18` and the guest
     computes `(ptr, len)` views of the `witness.state` /
     `witness.codes` / `witness.headers` sections over it
     (`extract_witness_state_section`,
     `EvmAsm/Codegen/Programs/SszWitnessState.lean:61-104`; codes /
     headers inline in `stateless_verdict_v2`,
     `BlockVerdictStateRoot.lean:341-361`). Each section is a standard
     SSZ `List[ByteList]`: a leading table of little-endian u32 offsets
     (first = `4*N`), then the element bytes. `witnessSectionIs` below
     is that section view, with the exact well-formedness the index
     builder validates.

  2. **The sorted witness hash indexes** — the real "code DB"
     (`EvmAsm/Codegen/Programs/MptWitnessIndex.lean`, state flavour
     `widx_*`; codes flavour `wcidx_*` by systematic rename in
     `WitnessCodeLookup.lean:29-38`): 48-byte records
     `keccak256(element)[32] | offset:u64 LE | len:u64 LE` in a 6 MiB
     `.data` arena, capacity 131072 records, heapsorted by full 32-byte
     hash (bytewise big-endian compare, `widx_cmp32`), binary-searched
     by `witness_lookup_by_hash_indexed`. `witness_codes_lookup_by_hash`
     (guest `0x80003998`) dispatches to the index when the queried
     `(ptr, len)` matches the registered section, else falls back to an
     **uncapped** linear scan — the 64 KiB scan cap was a bug (silent
     false misses on > 64 KiB codes sections) removed by commit
     `7bc58c8ef`; the model here scans/indexes the whole section, per
     the invariant documented at `MptWitnessLookup.lean:47-51`.
     Lookups return the element's `(offset, len)` **into the section**
     — code bytes are never copied.

  3. **Registration cells** (`wcidx_count` / `wcidx_enabled` /
     `wcidx_section_ptr` / `wcidx_section_len`, and the `widx_*`
     twins): u64 `.data` cells binding the index to its section.
     Populated by `witness_codes_index_build` from
     `stateless_verdict_v2` (`BlockVerdictStateRoot.lean:344-355`),
     which validates the offsets table (first u32 = `4*N`, monotone,
     all ≤ section length) and fails conservatively over capacity.

  ## Static sizing

  Index arena: fixed 131072 × 48 B = 6 MiB (pinned to the Codegen
  constants by `#guard` below). The SSZ spec-side envelope allows up to
  `MAX_WITNESS_NODES = 2^20` state entries (`SpecRef/Ssz.lean`) — more
  than the 2^17 index capacity; the builder returns failure (falling
  back to linear scan) rather than truncating, so the capacity bound
  appears here as `records.length ≤ WITNESS_INDEX_CAPACITY` inside
  `codeDbIs`. The `.data` arena addresses are link-layout-dependent, so
  assertions are base-parametrized.

  ## Faithfulness ties in this module

  * `witnessLookupSpec_correct` — a hit returns a slice whose keccak IS
    the queried hash (code-as-resource keyed by code hash).
  * `indexOfSection_hashes_eq_build_code_db` — the index the builder
    computes carries exactly the hashes of the spec-reference
    `build_code_db` (the `witness_state.py` port).
  * `#guard`s running the whole pipeline on a concrete two-code section
    (also cross-checked against the spec-level SSZ serializer) and
    pinning the record/capacity constants to the Codegen ones.
  * An `LBU` example consuming `witnessSectionIs` through the proven
    `bytesRegion_lbu_within` triple (the byte-read primitive the
    linear-scan keccak loop is built from).

  `witness_lookup_by_hash` / `witness_codes_lookup_by_hash` have no
  functional `cpsTripleWithin` specs yet (they are raw asm strings with
  whole-guest byte-identity pins); this module fixes the vocabulary
  those specs will be stated in.
-/

import EvmAsm.Evm64.StateAssertions
import EvmAsm.Stateless.SpecRef.WitnessState
import EvmAsm.Stateless.SpecRef.SszCodec
import EvmAsm.Codegen.Programs.MptWitnessIndex

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-! ## Constants (pinned to the Codegen source of truth) -/

/-- 48-byte index records: `hash[32] | offset:u64 | len:u64`. -/
def WITNESS_INDEX_RECORD_BYTES : Nat := 48

/-- 131072-record capacity (6 MiB arena). -/
def WITNESS_INDEX_CAPACITY : Nat := 131072

#guard WITNESS_INDEX_RECORD_BYTES = EvmAsm.Codegen.mptWitnessIndexRecordBytes
#guard WITNESS_INDEX_CAPACITY = EvmAsm.Codegen.mptWitnessIndexCapacity
#guard WITNESS_INDEX_CAPACITY * WITNESS_INDEX_RECORD_BYTES =
  EvmAsm.Codegen.mptWitnessIndexArenaBytes

/-! ## SSZ `List[ByteList]` section navigation

Exactly the arithmetic `witness_index_build` / the lookups perform:
little-endian u32 reads over the raw section bytes
(`MptWitnessIndex.lean:140-168`). -/

/-- The little-endian u32 at byte offset `off`. -/
def sszU32At (bs : List (BitVec 8)) (off : Nat) : Nat :=
  Stateless.SpecRef.bytesLEtoNat ((bs.drop off).take 4)

/-- Element count: the first u32 is the offsets-table size `4 * N`. -/
def sszSectionCount (bs : List (BitVec 8)) : Nat := sszU32At bs 0 / 4

/-- Start offset of element `i` (u32 at `4*i`). -/
def sszSectionOffset (bs : List (BitVec 8)) (i : Nat) : Nat :=
  sszU32At bs (4 * i)

/-- End offset of element `i`: the next element's start, or the section
    end for the last element. -/
def sszSectionEnd (bs : List (BitVec 8)) (i : Nat) : Nat :=
  if i + 1 < sszSectionCount bs then sszSectionOffset bs (i + 1) else bs.length

/-- The bytes of element `i`. -/
def sszElement (bs : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  (bs.drop (sszSectionOffset bs i)).take (sszSectionEnd bs i - sszSectionOffset bs i)

/-- All elements, in order — the section as the spec-level
    `List Bytes` the `build_*_db` functions consume. -/
def sszSectionElements (bs : List (BitVec 8)) : List (List (BitVec 8)) :=
  (List.range (sszSectionCount bs)).map (sszElement bs)

/-- The offsets-table validity `witness_index_build` checks before
    indexing (`MptWitnessIndex.lean:140-168`): the first u32 is `4*N`,
    the offsets are monotone, and every offset is within the section.
    (An empty section — `bs.length = 0` — is handled by the lookups as
    an unconditional miss before any table read.) -/
def sszSectionWF (bs : List (BitVec 8)) : Prop :=
  sszU32At bs 0 = 4 * sszSectionCount bs ∧
  (∀ i, i < sszSectionCount bs → i + 1 < sszSectionCount bs →
    sszSectionOffset bs i ≤ sszSectionOffset bs (i + 1)) ∧
  (∀ i, i < sszSectionCount bs → sszSectionOffset bs i ≤ bs.length)

instance (bs : List (BitVec 8)) : Decidable (sszSectionWF bs) := by
  unfold sszSectionWF
  infer_instance

/-- `witnessSectionIs ptr bs` — ownership of one in-place SSZ
    `List[ByteList]` witness section (state / codes / headers) at
    (dword-aligned) `ptr`, with the offsets-table validity the index
    builder enforces. `ptr` is a *view into the input blob*
    (`SSZ_BASE`-derived), not a scheme-A anchor — see the header. -/
def witnessSectionIs (ptr : Word) (bs : List (BitVec 8)) : Assertion :=
  fun ps => sszSectionWF bs ∧ bytesRegion ptr bs ps

theorem witnessSectionIs_eq_bytesRegion {ptr : Word} {bs : List (BitVec 8)}
    (hwf : sszSectionWF bs) :
    witnessSectionIs ptr bs = bytesRegion ptr bs := by
  funext ps
  exact propext ⟨fun h => h.2, fun h => ⟨hwf, h⟩⟩

theorem witnessSectionIs_wf {ptr : Word} {bs : List (BitVec 8)} {ps : PartialState}
    (h : witnessSectionIs ptr bs ps) : sszSectionWF bs := h.1

theorem pcFree_witnessSectionIs {ptr : Word} {bs : List (BitVec 8)} :
    (witnessSectionIs ptr bs).pcFree :=
  fun ps h => bytesRegion_pcFree ptr bs ps h.2

instance (ptr : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (witnessSectionIs ptr bs) := ⟨pcFree_witnessSectionIs⟩

/-! ## The sorted witness hash index (the real "code DB") -/

/-- One 48-byte index record: the element's keccak, and its
    `(offset, len)` slice of the section. -/
structure WitnessIndexRecord where
  hash : List (BitVec 8)
  offset : Nat
  len : Nat
  deriving Repr, BEq, DecidableEq

namespace WitnessIndexRecord

def WF (r : WitnessIndexRecord) : Prop :=
  r.hash.length = 32 ∧ r.offset < 2 ^ 64 ∧ r.len < 2 ^ 64

instance (r : WitnessIndexRecord) : Decidable r.WF := by
  unfold WF; infer_instance

/-- The record's arena bytes, exactly as `witness_index_build` stores
    them (`sd s5, 32(s8); sd s7, 40(s8)`, `MptWitnessIndex.lean:175-176`). -/
def bytes (r : WitnessIndexRecord) : List (BitVec 8) :=
  r.hash ++ Stateless.SpecRef.natToBytesLE 8 r.offset ++
  Stateless.SpecRef.natToBytesLE 8 r.len

theorem bytes_length (r : WitnessIndexRecord) (hwf : r.WF) :
    r.bytes.length = WITNESS_INDEX_RECORD_BYTES := by
  unfold bytes
  simp only [List.length_append, hwf.1, Stateless.SpecRef.natToBytesLE,
    List.length_map, List.length_range]
  rfl

/-- Record `r` indexes a real slice of `section` whose keccak is the
    stored hash — what `witness_index_build` establishes for every
    record it writes. -/
def matchesSection (r : WitnessIndexRecord) (section_ : List (BitVec 8)) : Prop :=
  r.offset + r.len ≤ section_.length ∧
  r.hash = Stateless.SpecRef.keccak256 ((section_.drop r.offset).take r.len)

instance (r : WitnessIndexRecord) (section_ : List (BitVec 8)) :
    Decidable (r.matchesSection section_) := by
  unfold matchesSection; infer_instance

end WitnessIndexRecord

/-- `witnessIndexIs base records` — the 48-byte-stride record arena
    (`widx_records` / `wcidx_records`; link-layout-dependent base). -/
def witnessIndexIs (base : Word) (records : List WitnessIndexRecord) : Assertion :=
  match records with
  | [] => empAssertion
  | r :: rest =>
      (fun ps => r.WF ∧ bytesRegion base r.bytes ps) **
      witnessIndexIs (base + BitVec.ofNat 64 WITNESS_INDEX_RECORD_BYTES) rest

theorem witnessIndexIs_nil {base : Word} : witnessIndexIs base [] = empAssertion := rfl

theorem witnessIndexIs_cons {base : Word} {r : WitnessIndexRecord}
    {rest : List WitnessIndexRecord} :
    witnessIndexIs base (r :: rest) =
      ((fun ps => r.WF ∧ bytesRegion base r.bytes ps) **
       witnessIndexIs (base + BitVec.ofNat 64 WITNESS_INDEX_RECORD_BYTES) rest) := rfl

theorem pcFree_witnessIndexIs {base : Word} {records : List WitnessIndexRecord} :
    (witnessIndexIs base records).pcFree := by
  induction records generalizing base with
  | nil => exact pcFree_emp
  | cons r rest ih =>
    exact pcFree_sepConj (fun ps h => bytesRegion_pcFree _ _ ps h.2) ih

instance (base : Word) (records : List WitnessIndexRecord) :
    Assertion.PCFree (witnessIndexIs base records) := ⟨pcFree_witnessIndexIs⟩

/-- Split the arena: records of `xs ++ ys` are `xs`'s from `base` and
    `ys`'s from `base + 48 * xs.length` — the indexing arithmetic the
    binary search and the builder's insert both use. -/
theorem witnessIndexIs_append (base : Word) (xs ys : List WitnessIndexRecord) :
    witnessIndexIs base (xs ++ ys) =
      (witnessIndexIs base xs **
       witnessIndexIs
         (base + BitVec.ofNat 64 (WITNESS_INDEX_RECORD_BYTES * xs.length)) ys) := by
  induction xs generalizing base with
  | nil =>
    simp only [List.nil_append, witnessIndexIs_nil, sepConj_emp_left',
      List.length_nil, Nat.mul_zero]
    rw [show (BitVec.ofNat 64 0 : Word) = 0 from rfl,
        show base + (0 : Word) = base from by bv_omega]
  | cons r rest ih =>
    simp only [List.cons_append, witnessIndexIs_cons, List.length_cons]
    rw [ih (base + BitVec.ofNat 64 WITNESS_INDEX_RECORD_BYTES),
        add_ofNat_add_ofNat, sepConj_assoc',
        show WITNESS_INDEX_RECORD_BYTES + WITNESS_INDEX_RECORD_BYTES * rest.length =
          WITNESS_INDEX_RECORD_BYTES * (rest.length + 1) from by
            rw [Nat.mul_add, Nat.mul_one]
            omega]

/-- Isolate record `i` (0-indexed) at `base + 48 * i`, framing the rest —
    the probe shape of the binary search / linear scan. -/
theorem witnessIndexIs_split_at (base : Word) (records : List WitnessIndexRecord)
    (i : Nat) (hi : i < records.length) :
    witnessIndexIs base records =
      (witnessIndexIs base (records.take i) **
       (fun ps => (records[i]'hi).WF ∧
          bytesRegion (base + BitVec.ofNat 64 (WITNESS_INDEX_RECORD_BYTES * i))
            (records[i]'hi).bytes ps) **
       witnessIndexIs
         (base + BitVec.ofNat 64 (WITNESS_INDEX_RECORD_BYTES * (i + 1)))
         (records.drop (i + 1))) := by
  have hdrop : records.drop i = records[i]'hi :: records.drop (i + 1) :=
    List.drop_eq_getElem_cons hi
  have htake : records = records.take i ++ records[i]'hi :: records.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i records]
    rw [hdrop]
  conv_lhs => rw [htake]
  rw [witnessIndexIs_append, witnessIndexIs_cons]
  rw [List.length_take, Nat.min_eq_left (by omega)]
  rw [add_ofNat_add_ofNat,
      show WITNESS_INDEX_RECORD_BYTES * i + WITNESS_INDEX_RECORD_BYTES =
        WITNESS_INDEX_RECORD_BYTES * (i + 1) from by rw [Nat.mul_add, Nat.mul_one]]

/-- Sortedness by the full 32-byte hash, exactly the arena order the
    heapsort establishes: `widx_cmp32` compares bytewise big-endian,
    which on 32-byte hashes is the numeric big-endian order. -/
def witnessIndexSorted (records : List WitnessIndexRecord) : Prop :=
  List.Pairwise
    (fun a b => Stateless.SpecRef.bytesBEtoNat a.hash ≤
                Stateless.SpecRef.bytesBEtoNat b.hash) records

/-! ## Registration cells

The u64 `.data` cells binding an index to its section
(`wcidx_count` / `wcidx_enabled` / `wcidx_section_ptr` /
`wcidx_section_len`, `MptWitnessIndex.lean:252-273`; `widx_*` twins). -/

def witnessIndexCountIs (countLoc : Word) (records : List WitnessIndexRecord) :
    Assertion :=
  countLoc ↦ₘ BitVec.ofNat 64 records.length

def witnessIndexEnabledIs (enabledLoc : Word) (flag : Word) : Assertion :=
  enabledLoc ↦ₘ flag

def witnessIndexSectionPtrIs (ptrLoc sectionPtr : Word) : Assertion :=
  ptrLoc ↦ₘ sectionPtr

def witnessIndexSectionLenIs (lenLoc : Word) (bs : List (BitVec 8)) : Assertion :=
  lenLoc ↦ₘ BitVec.ofNat 64 bs.length

instance (countLoc : Word) (records : List WitnessIndexRecord) :
    Assertion.PCFree (witnessIndexCountIs countLoc records) := ⟨pcFree_memIs⟩

instance (enabledLoc flag : Word) :
    Assertion.PCFree (witnessIndexEnabledIs enabledLoc flag) := ⟨pcFree_memIs⟩

instance (ptrLoc sectionPtr : Word) :
    Assertion.PCFree (witnessIndexSectionPtrIs ptrLoc sectionPtr) := ⟨pcFree_memIs⟩

instance (lenLoc : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (witnessIndexSectionLenIs lenLoc bs) := ⟨pcFree_memIs⟩

/-! ## The composed code-DB resource -/

/-- `codeDbIs idxBase sectionPtr sectionBytes records` — the real code
    DB: the in-place SSZ codes section plus its sorted keccak index,
    with the invariants `witness_codes_index_build` establishes: the
    record count fits the fixed arena, the records are hash-sorted, and
    every record indexes a section slice hashing to its stored key.
    (The same shape at the `widx_*` bases is the state-witness index.) -/
def codeDbIs (idxBase sectionPtr : Word) (sectionBytes : List (BitVec 8))
    (records : List WitnessIndexRecord) : Assertion :=
  fun ps =>
    records.length ≤ WITNESS_INDEX_CAPACITY ∧
    witnessIndexSorted records ∧
    (∀ r ∈ records, r.matchesSection sectionBytes) ∧
    (witnessSectionIs sectionPtr sectionBytes ** witnessIndexIs idxBase records) ps

theorem pcFree_codeDbIs {idxBase sectionPtr : Word}
    {sectionBytes : List (BitVec 8)} {records : List WitnessIndexRecord} :
    (codeDbIs idxBase sectionPtr sectionBytes records).pcFree :=
  fun ps h =>
    pcFree_sepConj pcFree_witnessSectionIs pcFree_witnessIndexIs ps h.2.2.2

instance (idxBase sectionPtr : Word) (sectionBytes : List (BitVec 8))
    (records : List WitnessIndexRecord) :
    Assertion.PCFree (codeDbIs idxBase sectionPtr sectionBytes records) :=
  ⟨pcFree_codeDbIs⟩

/-! ## The lookup model and its guarantees -/

/-- Semantic model of `witness_codes_lookup_by_hash` /
    `witness_lookup_by_hash`: the `(offset, len)` of the first record
    whose stored hash equals the target. (The guest's binary search
    over the sorted arena and its uncapped linear fallback both return
    a record with this property.) -/
def witnessLookupSpec (records : List WitnessIndexRecord)
    (h : List (BitVec 8)) : Option (Nat × Nat) :=
  (records.find? (fun r => r.hash == h)).map (fun r => (r.offset, r.len))

/-- **Lookup-by-hash returns a slice whose keccak IS the queried
    hash** — the code-as-resource guarantee (`code_hash` keys really
    name their bytecode). -/
theorem witnessLookupSpec_correct {records : List WitnessIndexRecord}
    {section_ h : List (BitVec 8)} {off len : Nat}
    (hm : ∀ r ∈ records, r.matchesSection section_)
    (hf : witnessLookupSpec records h = some (off, len)) :
    off + len ≤ section_.length ∧
    Stateless.SpecRef.keccak256 ((section_.drop off).take len) = h := by
  unfold witnessLookupSpec at hf
  cases hfind : records.find? (fun r => r.hash == h) with
  | none => rw [hfind] at hf; simp at hf
  | some r =>
    rw [hfind] at hf
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨hoff, hlen⟩ := hf
    have hhash : r.hash = h := by
      have := List.find?_some hfind
      simpa using this
    have hmatch := hm r (List.mem_of_find?_eq_some hfind)
    obtain ⟨hbound, hkec⟩ := hmatch
    subst hoff hlen
    exact ⟨hbound, by rw [← hkec, hhash]⟩

/-- The index content the builder computes for a section: one record
    per element, hash = keccak of the element, slice = the element's
    offsets (this is the pre-sort record list;
    `witness_codes_index_build` heapsorts it in place). -/
def indexOfSection (bs : List (BitVec 8)) : List WitnessIndexRecord :=
  (List.range (sszSectionCount bs)).map (fun i =>
    { hash := Stateless.SpecRef.keccak256 (sszElement bs i)
      offset := sszSectionOffset bs i
      len := sszSectionEnd bs i - sszSectionOffset bs i })

/-- **The index carries exactly the spec-reference code DB's hashes**:
    `indexOfSection`'s keys are the keys of
    `SpecRef.build_code_db (sszSectionElements bs)` (the
    `witness_state.py` port), in element order. -/
theorem indexOfSection_hashes_eq_build_code_db (bs : List (BitVec 8)) :
    (indexOfSection bs).map (·.hash) =
      (Stateless.SpecRef.build_code_db (sszSectionElements bs)).map Prod.fst := by
  unfold indexOfSection Stateless.SpecRef.build_code_db sszSectionElements
  rw [List.map_map, List.map_map, List.map_map]
  rfl

/-- Every record the builder computes matches the section, given the
    validated offsets table. -/
theorem indexOfSection_matchesSection (bs : List (BitVec 8))
    (hwf : sszSectionWF bs) :
    ∀ r ∈ indexOfSection bs, r.matchesSection bs := by
  intro r hr
  unfold indexOfSection at hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  have hilt : i < sszSectionCount bs := List.mem_range.mp hi
  obtain ⟨-, hmono, hbound⟩ := hwf
  constructor
  · show sszSectionOffset bs i + (sszSectionEnd bs i - sszSectionOffset bs i) ≤ _
    unfold sszSectionEnd
    by_cases hnext : i + 1 < sszSectionCount bs
    · rw [if_pos hnext]
      have h1 := hmono i hilt hnext
      have h2 := hbound (i + 1) hnext
      omega
    · rw [if_neg hnext]
      have := hbound i hilt
      omega
  · show _ = Stateless.SpecRef.keccak256 ((bs.drop _).take _)
    rfl

/-! ## Concrete pipeline cross-checks

A two-code section, built by hand in the exact SSZ `List[ByteList]`
wire format and cross-checked against the spec-level SSZ serializer;
then the whole navigation → index → lookup pipeline runs on it. -/

/-- `codes = [[0x60, 0x00], [0x60, 0x01]]`; offsets table `[8, 10]`. -/
private def testSection : List (BitVec 8) :=
  [8, 0, 0, 0, 10, 0, 0, 0, 0x60, 0x00, 0x60, 0x01]

-- The hand-built section is exactly the spec-level SSZ serialization of
-- the two byte-lists.
#guard Stateless.SpecRef.SszValue.serialize
    (.list 16 none [.byteList 16 [0x60, 0x00], .byteList 16 [0x60, 0x01]]) =
  testSection

#guard sszSectionCount testSection = 2
#guard decide (sszSectionWF testSection)
#guard sszElement testSection 0 = [0x60, 0x00]
#guard sszElement testSection 1 = [0x60, 0x01]

-- Index + lookup: the code is found by its keccak, at its slice.
#guard witnessLookupSpec (indexOfSection testSection)
    (Stateless.SpecRef.keccak256 [0x60, 0x01]) = some (10, 2)
#guard decide (∀ r ∈ indexOfSection testSection, r.matchesSection testSection)

/-! ## Machine-level tie-in

The byte-read primitive over a witness section, restated against
`witnessSectionIs`: reading byte `i` of the section yields `bs[i]` —
the load the linear-scan keccak loop and the offsets-table reads are
built from. Consumes the proven `bytesRegion_lbu_within`. -/

example (rd rs1 : Reg) (ptr vOld base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hwf : sszSectionWF bs) (hrd : rd ≠ .x0)
    (halign : ptr.toNat % 8 = 0) (hi : i < bs.length)
    (hover : ptr.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (ptr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU rd rs1 0))
      ((rs1 ↦ᵣ (ptr + BitVec.ofNat 64 i)) ** (rd ↦ᵣ vOld) **
       witnessSectionIs ptr bs)
      ((rs1 ↦ᵣ (ptr + BitVec.ofNat 64 i)) **
       (rd ↦ᵣ ((bs[i]'hi).zeroExtend 64)) ** witnessSectionIs ptr bs) := by
  rw [witnessSectionIs_eq_bytesRegion hwf]
  exact bytesRegion_lbu_within rd rs1 ptr vOld base bs i hrd halign hi hover hvalid

end EvmAsm.Evm64
