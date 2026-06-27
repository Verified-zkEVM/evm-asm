/-
  EvmAsm.Rv64.RLP.SchemaFold

  EL.3 / Phase 5 — the N-field HETEROGENEOUS fold: chain an arbitrary list of field units
  (scalar | byte-array, in any order) into one decoder over a shared output `bytesRegion`.
  This is the keystone that turns the concrete legacy-tx (9-field) / block-header (~19-field)
  decoders into cheap instantiations: a schema is just a `List FieldSpec`.

  Each unit is a FULLY-canonical field unit (`UnifiedFieldUnitFullyCanonical`) — a uniform
  all-`regOwn` scratch interface — so the fold threads only `x13` (the input pointer) and the
  output region. Disjointness uses the contiguous-code-range property
  (`FieldUnitDisjoint`): each unit occupies `[base_i, base_i + fieldSize)`, so the schema's CR
  is `none` outside `[base, base + schemaSize)`.
-/

import EvmAsm.Rv64.RLP.UnifiedFieldUnitFullyCanonical
import EvmAsm.Rv64.RLP.UnifiedLongBytesFieldCanonical
import EvmAsm.Rv64.RLP.UnifiedEmptyScalarFieldCanonical
import EvmAsm.Rv64.RLP.UnifiedEmptyBytesFieldCanonical
import EvmAsm.Rv64.RLP.UnifiedHeteroFieldWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- One field of a fixed decode schema: kind, payload bytes, output byte offset, and the
    store/copy immediate (`signExtend12 imm = ofNat di`). -/
structure FieldSpec where
  isScalar : Bool
  data : List Byte
  di : Nat
  imm : BitVec 12

/-- Output bytes written by a field: 8 (scalar u64) or `|data|` (byte array). -/
def fieldWriteLen (f : FieldSpec) : Nat := if f.isScalar then 8 else f.data.length

/-- Code size of a field unit: scalar 248 (empty) | 280 (non-empty); byte array `152 + 20·|data|`. -/
def fieldSize (f : FieldSpec) : Nat :=
  if f.isScalar then (if f.data = [] then 248 else 280) else 152 + 20 * f.data.length

/-- Step bound of a field unit. -/
def fieldSteps (f : FieldSpec) : Nat :=
  if f.isScalar then (if f.data = [] then 61 + (1 + 3 * 8) else (61 + (2 + 6 * f.data.length)) + (1 + 3 * 8))
  else 61 + (1 + 5 * f.data.length)

/-- Input bytes consumed by a field (its RLP item's encoding length). -/
def fieldEnc (f : FieldSpec) : Nat := (encode (.bytes f.data)).length

/-- The field unit's CodeReq at program address `base`. -/
def fieldCR (base : Word) (rOut : Reg) (f : FieldSpec) : CodeReq :=
  if f.isScalar then (if f.data = [] then emptyScalarUnitCR base rOut f.imm else scalarRegionUnitCR base rOut f.imm)
  else bytesUnitCR base rOut f.imm f.data.length

/-- The output region after a field writes its value (LE spill | payload copy). -/
def fieldUpdate (out : List Byte) (f : FieldSpec) : List Byte :=
  if f.isScalar then spillRange out (BitVec.ofNat 64 (Nat.fromBytesBE f.data)) f.di 8
  else copyRangeGen out f.data 0 f.di f.data.length

/-- Total code size of a schema. -/
def schemaSize : List FieldSpec → Nat
  | [] => 0
  | f :: rest => fieldSize f + schemaSize rest

/-- Total step bound of a schema. -/
def schemaSteps : List FieldSpec → Nat
  | [] => 0
  | f :: rest => fieldSteps f + schemaSteps rest

/-- Total input bytes consumed by a schema. -/
def schemaEnc : List FieldSpec → Nat
  | [] => 0
  | f :: rest => fieldEnc f + schemaEnc rest

/-- The output region after the whole schema runs (each field's update, in order). -/
def schemaOut (out : List Byte) : List FieldSpec → List Byte
  | [] => out
  | f :: rest => schemaOut (fieldUpdate out f) rest

/-- The schema's CodeReq: each unit at its cumulative base address. -/
def schemaCR (base : Word) (rOut : Reg) : List FieldSpec → CodeReq
  | [] => CodeReq.empty
  | f :: rest => (fieldCR base rOut f).union (schemaCR (base + BitVec.ofNat 64 (fieldSize f)) rOut rest)

/-- The uniform fold invariant: all scratch `regOwn`, `x13` at input offset `O`, input region
    `bs`, output region `out`. Equals the fully-canonical units' shared pre/post shape. -/
def schemaINV (regionBase outBase : Word) (rOut : Reg) (bs : List Byte) (O : Nat)
    (out : List Byte) : Assertion :=
  (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
    (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (regOwn .x14) **
    (regOwn .x15) ** bytesRegion regionBase bs) **
   ((rOut ↦ᵣ outBase) ** bytesRegion outBase out))

/-- Per-field validity of a schema at input offset `O` (output length `outLen`). -/
def SchemaValid (bs : List Byte) (outLen : Nat) : Nat → List FieldSpec → Prop
  | _, [] => True
  | O, f :: rest =>
    (if f.isScalar then f.data.length ≤ 8
     else (encode (.bytes f.data)).length < 256 ^ 8) ∧
    signExtend12 f.imm = BitVec.ofNat 64 f.di ∧
    f.di + fieldWriteLen f ≤ outLen ∧
    bs.drop O = encode (.bytes f.data) ++ bs.drop (O + fieldEnc f) ∧
    SchemaValid bs outLen (O + fieldEnc f) rest

/-- The per-field pure decode coincidences of a schema. -/
def schemaDecodes (bs : List Byte) : Nat → List FieldSpec → Prop
  | _, [] => True
  | O, f :: rest =>
    (if f.isScalar then decodeScalar (bs.drop O) = some (Nat.fromBytesBE f.data, bs.drop (O + fieldEnc f))
     else decode (bs.drop O) = some (.bytes f.data, bs.drop (O + fieldEnc f))) ∧
    schemaDecodes bs (O + fieldEnc f) rest

-- ---------------------------------------------------------------------------
-- Length preservation (every field update preserves the output length).
-- ---------------------------------------------------------------------------

/-- Copying preserves the destination list's length. -/
theorem copyRangeGen_length (dst src : List Byte) (si0 di0 N : Nat) :
    (copyRangeGen dst src si0 di0 N).length = dst.length := by
  induction N generalizing dst si0 di0 with
  | zero => rfl
  | succ n ih => rw [copyRangeGen, ih, List.length_set]

/-- A single field update preserves the output length. -/
theorem fieldUpdate_length (out : List Byte) (f : FieldSpec) :
    (fieldUpdate out f).length = out.length := by
  unfold fieldUpdate
  by_cases h : f.isScalar
  · simp only [h]; exact spillRange_length _ _ _ _
  · simp only [h]; exact copyRangeGen_length _ _ _ _ _

/-- The whole schema preserves the output length. -/
theorem schemaOut_length (out : List Byte) (specs : List FieldSpec) :
    (schemaOut out specs).length = out.length := by
  induction specs generalizing out with
  | nil => rfl
  | cons f rest ih => rw [schemaOut, ih, fieldUpdate_length]

-- ---------------------------------------------------------------------------
-- Disjointness: the schema CR is `none` outside `[base, base + schemaSize)`.
-- ---------------------------------------------------------------------------

/-- A single field unit's CR is `none` at/above `base + fieldSize`. -/
theorem fieldCR_none_above (base : Word) (rOut : Reg) (f : FieldSpec) (a : Word)
    (hcode : base.toNat + fieldSize f < 2 ^ 64) (h : base.toNat + fieldSize f ≤ a.toNat) :
    fieldCR base rOut f a = none := by
  by_cases hs : f.isScalar
  · by_cases hempty : f.data = []
    · have hcode' : base.toNat + 248 < 2 ^ 64 := by simpa [fieldSize, hs, hempty] using hcode
      have h' : base.toNat + 248 ≤ a.toNat := by simpa [fieldSize, hs, hempty] using h
      simp only [fieldCR, hs, hempty, if_true]
      exact empty_scalar_unit_cr_none_above base rOut f.imm a hcode' h'
    · have hcode' : base.toNat + 280 < 2 ^ 64 := by simpa [fieldSize, hs, hempty] using hcode
      have h' : base.toNat + 280 ≤ a.toNat := by simpa [fieldSize, hs, hempty] using h
      simp only [fieldCR, hs, hempty, if_false]
      exact scalar_region_unit_cr_none_above base rOut f.imm a hcode' h'
  · have hcode' : base.toNat + (152 + 20 * f.data.length) < 2 ^ 64 := by
      simpa [fieldSize, hs] using hcode
    have h' : base.toNat + (152 + 20 * f.data.length) ≤ a.toNat := by simpa [fieldSize, hs] using h
    simp only [fieldCR, hs]
    exact bytes_unit_cr_none_above base rOut f.imm f.data.length a hcode' h'

/-- A single field unit's CR is `none` below `base`. -/
theorem fieldCR_none_below (base : Word) (rOut : Reg) (f : FieldSpec) (a : Word)
    (hcode : base.toNat + fieldSize f < 2 ^ 64) (h : a.toNat < base.toNat) :
    fieldCR base rOut f a = none := by
  by_cases hs : f.isScalar
  · by_cases hempty : f.data = []
    · have hcode' : base.toNat + 248 < 2 ^ 64 := by simpa [fieldSize, hs, hempty] using hcode
      simp only [fieldCR, hs, hempty, if_true]
      exact empty_scalar_unit_cr_none_below base rOut f.imm a hcode' h
    · have hcode' : base.toNat + 280 < 2 ^ 64 := by simpa [fieldSize, hs, hempty] using hcode
      simp only [fieldCR, hs, hempty, if_false]
      exact scalar_region_unit_cr_none_below base rOut f.imm a hcode' h
  · have hcode' : base.toNat + (152 + 20 * f.data.length) < 2 ^ 64 := by
      simpa [fieldSize, hs] using hcode
    simp only [fieldCR, hs]
    exact bytes_unit_cr_none_below base rOut f.imm f.data.length a hcode' h

/-- The schema CR is `none` below `base` (every unit is at or after `base`). -/
theorem schemaCR_none_below (rOut : Reg) :
    ∀ (specs : List FieldSpec) (base : Word) (a : Word),
      base.toNat + schemaSize specs < 2 ^ 64 → a.toNat < base.toNat →
      schemaCR base rOut specs a = none := by
  intro specs
  induction specs with
  | nil => intro base a _ _; rfl
  | cons f rest ih =>
    intro base a hcode hlt
    have hsz : (base + BitVec.ofNat 64 (fieldSize f)).toNat = base.toNat + fieldSize f := by
      have : base.toNat + fieldSize f < 2 ^ 64 := by
        have : schemaSize (f :: rest) = fieldSize f + schemaSize rest := rfl
        omega
      bv_omega
    have h1 : fieldCR base rOut f a = none :=
      fieldCR_none_below base rOut f a (by have : schemaSize (f :: rest) = fieldSize f + schemaSize rest := rfl; omega) hlt
    have h2 : schemaCR (base + BitVec.ofNat 64 (fieldSize f)) rOut rest a = none :=
      ih (base + BitVec.ofNat 64 (fieldSize f)) a
        (by rw [hsz]; have : schemaSize (f :: rest) = fieldSize f + schemaSize rest := rfl; omega)
        (by rw [hsz]; omega)
    simp only [schemaCR, CodeReq.union, h1, h2]

/-- The schema CR is `none` at/above `base + schemaSize` (every unit ends before it). -/
theorem schemaCR_none_above (rOut : Reg) :
    ∀ (specs : List FieldSpec) (base : Word) (a : Word),
      base.toNat + schemaSize specs < 2 ^ 64 → base.toNat + schemaSize specs ≤ a.toNat →
      schemaCR base rOut specs a = none := by
  intro specs
  induction specs with
  | nil => intro base a _ _; rfl
  | cons f rest ih =>
    intro base a hcode hge
    have hszrec : schemaSize (f :: rest) = fieldSize f + schemaSize rest := rfl
    have hsz : (base + BitVec.ofNat 64 (fieldSize f)).toNat = base.toNat + fieldSize f := by
      have : base.toNat + fieldSize f < 2 ^ 64 := by omega
      bv_omega
    have h1 : fieldCR base rOut f a = none :=
      fieldCR_none_above base rOut f a (by omega) (by omega)
    have h2 : schemaCR (base + BitVec.ofNat 64 (fieldSize f)) rOut rest a = none :=
      ih (base + BitVec.ofNat 64 (fieldSize f)) a (by rw [hsz]; omega) (by rw [hsz]; omega)
    simp only [schemaCR, CodeReq.union, h1, h2]

/-- **Schema-prefix ⊥ next unit.** The CR of a schema occupying `[base, base+schemaSize)` is
    disjoint from a unit's CR at `base + schemaSize` (used to extend a fold by one field). -/
theorem schemaCR_disjoint_fieldCR (rOut : Reg) (specs : List FieldSpec) (base : Word) (f : FieldSpec)
    (hcode : base.toNat + (schemaSize specs + fieldSize f) < 2 ^ 64) :
    (schemaCR base rOut specs).Disjoint (fieldCR (base + BitVec.ofNat 64 (schemaSize specs)) rOut f) := by
  have hbsz : (base + BitVec.ofNat 64 (schemaSize specs)).toNat = base.toNat + schemaSize specs := by
    bv_omega
  refine codeReq_disjoint_of_ranges _ _ (base.toNat + schemaSize specs)
    (fun a ha => schemaCR_none_above rOut specs base a (by omega) ha)
    (fun a ha => fieldCR_none_below (base + BitVec.ofNat 64 (schemaSize specs)) rOut f a
      (by rw [hbsz]; omega) (by rw [hbsz]; omega))

end EvmAsm.Rv64.RLP
