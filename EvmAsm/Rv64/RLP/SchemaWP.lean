/-
  EvmAsm.Rv64.RLP.SchemaWP

  WP-facing adapters for fixed-schema RLP field units.  The canonical field
  proofs expose the right machine behavior but their postconditions are ordered
  for local composition; this file normalizes them to `schemaINV`, so callers can
  use a field as a one-step weakest-precondition certificate.
-/

import EvmAsm.Rv64.RLP.SchemaFold
import EvmAsm.Rv64.WP.CFG

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

namespace SchemaWP


/-- Scalar fields bounded to eight payload bytes always have an RLP encoding within the
    decoder length bound used by the field endpoint. -/
theorem scalarField_encode_size_of_len_le_8 (data : List Byte) (hlen8 : data.length ≤ 8) :
    (encode (.bytes data)).length < 256 ^ 8 := by
  unfold encode encodeBytes
  cases data with
  | nil => simp
  | cons b tail =>
      cases tail with
      | nil =>
          by_cases hb : b.toNat < 0x80 <;> simp [hb]
      | cons c tail =>
          have hlen8_tail : tail.length + 2 ≤ 8 := by simpa using hlen8
          have h55 : tail.length + 1 + 1 ≤ 55 := by omega
          simp [h55]
          omega

/-- The schema invariant entails the canonical byte-field precondition. -/
theorem schemaINV_entails_byteFieldPre
    (regionBase outBase : Word) (rOut : Reg) (bs : List Byte) (O : Nat)
    (outBytes : List Byte) :
    WP.Entails (schemaINV regionBase outBase rOut bs O outBytes)
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (regOwn .x14) **
        (regOwn .x15) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)) := by
  intro h hp
  unfold schemaINV at hp
  xperm_hyp hp

/-- The canonical byte-field postcondition entails the schema invariant. -/
theorem byteFieldPost_entails_schemaINV
    (regionBase outBase : Word) (rOut : Reg) (bs : List Byte) (O : Nat)
    (data outBytes : List Byte) (di0 : Nat) :
    WP.Entails
      (((regOwn .x12) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
          (regOwn .x14) ** (regOwn .x15) **
          (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
          bytesRegion outBase (copyRangeGen outBytes data 0 di0 data.length)) **
        (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11))
      (schemaINV regionBase outBase rOut bs (O + (encode (.bytes data)).length)
        (copyRangeGen outBytes data 0 di0 data.length)) := by
  intro h hp
  unfold schemaINV
  xperm_hyp hp


/-- The canonical scalar-field postcondition entails the schema invariant. -/
theorem scalarFieldPost_entails_schemaINV
    (regionBase outBase : Word) (rOut : Reg) (bs : List Byte) (O : Nat)
    (data outBytes : List Byte) (di0 : Nat) :
    WP.Entails
      (((regOwn .x11) ** (regOwn .x14) ** (rOut ↦ᵣ outBase) **
          bytesRegion outBase
            (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE data)) di0 8)) **
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
          regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
          regOwn .x5 ** regOwn .x10 ** regOwn .x15))
      (schemaINV regionBase outBase rOut bs (O + (encode (.bytes data)).length)
        (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE data)) di0 8)) := by
  intro h hp
  unfold schemaINV
  xperm_hyp hp

/-- Normalize a canonical byte-field unit into the schema fold invariant.
    The returned certificate computes the precondition for the requested
    postcondition `schemaINV ... (O + enc(data)) (copyRangeGen ...)`. -/
def byteFieldStepCert
    (base regionBase outBase : Word) (rOut : Reg) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail outBytes : List Byte) (di0 : Nat)
    (hsize : (encode (.bytes data)).length < 256 ^ 8)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hdst : di0 + data.length ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (148 + 4 + 20 * data.length) < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    WP.CFG.Cert base (base + 148 + 4 + BitVec.ofNat 64 (20 * data.length))
      (bytesUnitCR base rOut fieldImm data.length)
      (schemaINV regionBase outBase rOut bs (O + (encode (.bytes data)).length)
        (copyRangeGen outBytes data 0 di0 data.length)) := by
  by_cases hnil : data = []
  · subst data
    exact (WP.CFG.block
      (byteFieldPost_entails_schemaINV regionBase outBase rOut bs O ([] : List Byte) outBytes di0)
      (unified_empty_bytes_field_decode_and_copy_fully_canonical base regionBase rOut outBase
        fieldImm bs O tail outBytes di0 halign hdalign hover hwin hImm hdst hdov hdval hcode
        hdrop).1).weakenPre
      (schemaINV_entails_byteFieldPre regionBase outBase rOut bs O outBytes)
  · by_cases hshort : data.length ≤ 55
    · have hlen1 : 1 ≤ data.length := by
        cases data with
        | nil => contradiction
        | cons _ _ => simp
      exact (WP.CFG.block
        (byteFieldPost_entails_schemaINV regionBase outBase rOut bs O data outBytes di0)
        (unified_bytes_field_decode_and_copy_fully_canonical base regionBase rOut outBase fieldImm
          bs O data tail outBytes di0 hlen1 hshort hsize halign hdalign hover hwin hImm hdst hdov
          hdval hcode hdrop).1).weakenPre
        (schemaINV_entails_byteFieldPre regionBase outBase rOut bs O outBytes)
    · have hlong : 55 < data.length := by omega
      exact (WP.CFG.block
        (byteFieldPost_entails_schemaINV regionBase outBase rOut bs O data outBytes di0)
        (unified_long_bytes_field_decode_and_copy_fully_canonical base regionBase rOut outBase
          fieldImm bs O data tail outBytes di0 hlong hsize halign hdalign hover hwin hImm hdst hdov
          hdval hcode hdrop).1).weakenPre
        (schemaINV_entails_byteFieldPre regionBase outBase rOut bs O outBytes)

/-- The computed WP precondition of `byteFieldStepCert` is the schema invariant before the field. -/
theorem byteFieldStepCert_pre
    (base regionBase outBase : Word) (rOut : Reg) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail outBytes : List Byte) (di0 : Nat)
    (hsize : (encode (.bytes data)).length < 256 ^ 8)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hdst : di0 + data.length ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (148 + 4 + 20 * data.length) < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    (byteFieldStepCert base regionBase outBase rOut fieldImm bs O data tail outBytes di0
      hsize halign hdalign hover hwin hImm hdst hdov hdval hcode hdrop).pre =
      schemaINV regionBase outBase rOut bs O outBytes := by
  by_cases hnil : data = []
  · subst data
    simp [byteFieldStepCert, WP.Triple.weakenPre]
  · unfold byteFieldStepCert
    simp [hnil]
    split <;> rfl

/-- Pure decode coincidence paired with `byteFieldStepCert`. -/
theorem byteFieldStep_decode
    (base regionBase outBase : Word) (rOut : Reg) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail outBytes : List Byte) (di0 : Nat)
    (hsize : (encode (.bytes data)).length < 256 ^ 8)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hdst : di0 + data.length ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (148 + 4 + 20 * data.length) < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    decode (bs.drop O) = some (.bytes data, tail) := by
  by_cases hnil : data = []
  · subst data
    exact (unified_empty_bytes_field_decode_and_copy_fully_canonical base regionBase rOut outBase
      fieldImm bs O tail outBytes di0 halign hdalign hover hwin hImm hdst hdov hdval hcode hdrop).2
  · by_cases hshort : data.length ≤ 55
    · have hlen1 : 1 ≤ data.length := by
        cases data with
        | nil => contradiction
        | cons _ _ => simp
      exact (unified_bytes_field_decode_and_copy_fully_canonical base regionBase rOut outBase
        fieldImm bs O data tail outBytes di0 hlen1 hshort hsize halign hdalign hover hwin hImm hdst
        hdov hdval hcode hdrop).2
    · have hlong : 55 < data.length := by omega
      exact (unified_long_bytes_field_decode_and_copy_fully_canonical base regionBase rOut outBase
        fieldImm bs O data tail outBytes di0 hlong hsize halign hdalign hover hwin hImm hdst hdov
        hdval hcode hdrop).2


/-- Normalize a canonical scalar field unit into the schema fold invariant.  The certificate covers
    the empty zero scalar and the non-empty canonical scalar path. -/
def scalarFieldStepCert
    (base regionBase outBase : Word) (rOut : Reg) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail outBytes : List Byte) (di0 : Nat)
    (hlen8 : data.length ≤ 8) (hcanon : data = [] ∨ data.headD 1 ≠ 0)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hdst : di0 + 8 ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (if data = [] then 248 else 280) < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    WP.CFG.Cert base (base + BitVec.ofNat 64 (if data = [] then 248 else 280))
      (if data = [] then emptyScalarUnitCR base rOut fieldImm
       else scalarRegionUnitCR base rOut fieldImm)
      (schemaINV regionBase outBase rOut bs (O + (encode (.bytes data)).length)
        (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE data)) di0 8)) := by
  by_cases hnil : data = []
  · subst data
    have hexit : base + 148 + 4 + BitVec.ofNat 64 (12 * 8) = base + BitVec.ofNat 64 248 := by
      bv_omega
    have hcode_empty : base.toNat + (148 + 4 + 12 * 8) < 2 ^ 64 := by
      simpa using hcode
    exact ((WP.CFG.block
      (scalarFieldPost_entails_schemaINV regionBase outBase rOut bs O ([] : List Byte) outBytes di0)
      (unified_empty_scalar_field_decode_and_store_region_fully_canonical base regionBase rOut
        outBase fieldImm bs O tail outBytes di0 halign hover hwin hdrop hdalign hdst hdov hdval hImm
        hcode_empty).1).changeExit hexit).weakenPre
      (schemaINV_entails_byteFieldPre regionBase outBase rOut bs O outBytes)
  · have hlen1 : 1 ≤ data.length := by
      cases data with
      | nil => contradiction
      | cons _ _ => simp
    have hhead : data.headD 1 ≠ 0 := by
      cases hcanon with
      | inl h => exact False.elim (hnil h)
      | inr h => exact h
    have hsize : (encode (.bytes data)).length < 256 ^ 8 :=
      scalarField_encode_size_of_len_le_8 data hlen8
    have hcode_data : base.toNat + 280 < 2 ^ 64 := by
      simpa [hnil] using hcode
    have hexit : base + 180 + 4 + BitVec.ofNat 64 (12 * 8) = base + BitVec.ofNat 64 280 := by
      bv_omega
    simpa [hnil] using (((WP.CFG.block
      (scalarFieldPost_entails_schemaINV regionBase outBase rOut bs O data outBytes di0)
      (unified_scalar_field_decode_and_store_region_fully_canonical base regionBase rOut outBase
        fieldImm bs O data tail outBytes di0 hlen1 hlen8 hhead hsize halign hdalign hover hwin hImm
        hdst hdov hdval hcode_data hdrop).1).changeExit hexit).weakenPre
      (schemaINV_entails_byteFieldPre regionBase outBase rOut bs O outBytes))

/-- Pure decode coincidence paired with `scalarFieldStepCert`. -/
theorem scalarFieldStep_decode
    (base regionBase outBase : Word) (rOut : Reg) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail outBytes : List Byte) (di0 : Nat)
    (hlen8 : data.length ≤ 8) (hcanon : data = [] ∨ data.headD 1 ≠ 0)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hdst : di0 + 8 ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (if data = [] then 248 else 280) < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail) := by
  by_cases hnil : data = []
  · subst data
    have hcode_empty : base.toNat + (148 + 4 + 12 * 8) < 2 ^ 64 := by
      simpa using hcode
    simpa using (unified_empty_scalar_field_decode_and_store_region_fully_canonical base
      regionBase rOut outBase fieldImm bs O tail outBytes di0 halign hover hwin hdrop hdalign hdst
      hdov hdval hImm hcode_empty).2
  · have hlen1 : 1 ≤ data.length := by
      cases data with
      | nil => contradiction
      | cons _ _ => simp
    have hhead : data.headD 1 ≠ 0 := by
      cases hcanon with
      | inl h => exact False.elim (hnil h)
      | inr h => exact h
    have hsize : (encode (.bytes data)).length < 256 ^ 8 :=
      scalarField_encode_size_of_len_le_8 data hlen8
    have hcode_data : base.toNat + 280 < 2 ^ 64 := by
      simpa [hnil] using hcode
    exact (unified_scalar_field_decode_and_store_region_fully_canonical base regionBase rOut outBase
      fieldImm bs O data tail outBytes di0 hlen1 hlen8 hhead hsize halign hdalign hover hwin hImm hdst
      hdov hdval hcode_data hdrop).2

/-- Schema-facing byte field step.  The static field record supplies the output
    offset and immediate; the postcondition is expressed with `fieldEnc` and
    `fieldUpdate`, so this is the adapter consumed by a schema fold. -/
def byteFieldSpecStepCert
    (base regionBase outBase : Word) (rOut : Reg)
    (bs : List Byte) (O : Nat) (outBytes : List Byte) (f : FieldSpec)
    (hbyte : f.isScalar = false)
    (hsize : (if f.isScalar then f.data.length ≤ 8
      else (encode (.bytes f.data)).length < 256 ^ 8))
    (hImm : signExtend12 f.imm = BitVec.ofNat 64 f.di)
    (hdst : f.di + fieldWriteLen f ≤ outBytes.length)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + fieldSize f < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes f.data) ++ bs.drop (O + fieldEnc f)) :
    WP.CFG.Cert base (base + BitVec.ofNat 64 (fieldSize f))
      (fieldCR base rOut f)
      (schemaINV regionBase outBase rOut bs (O + fieldEnc f) (fieldUpdate outBytes f)) := by
  have hsize_data : (encode (.bytes f.data)).length < 256 ^ 8 := by
    simpa [hbyte] using hsize
  have hdst_data : f.di + f.data.length ≤ outBytes.length := by
    simpa [fieldWriteLen, hbyte] using hdst
  have hcode_data : base.toNat + (148 + 4 + 20 * f.data.length) < 2 ^ 64 := by
    simpa [fieldSize, hbyte] using hcode
  have hexit : base + 148 + 4 + BitVec.ofNat 64 (20 * f.data.length)
      = base + BitVec.ofNat 64 (fieldSize f) := by
    simp [fieldSize, hbyte]
    bv_omega
  have cert := byteFieldStepCert base regionBase outBase rOut f.imm bs O f.data
    (bs.drop (O + fieldEnc f)) outBytes f.di hsize_data halign hdalign hover hwin hImm hdst_data
    hdov hdval hcode_data hdrop
  simpa [fieldCR, fieldEnc, fieldUpdate, hbyte] using cert.changeExit hexit

/-- Pure decode fact produced by `byteFieldSpecStepCert`. -/
theorem byteFieldSpecStep_decode
    (base regionBase outBase : Word) (rOut : Reg)
    (bs : List Byte) (O : Nat) (outBytes : List Byte) (f : FieldSpec)
    (hbyte : f.isScalar = false)
    (hsize : (if f.isScalar then f.data.length ≤ 8
      else (encode (.bytes f.data)).length < 256 ^ 8))
    (hImm : signExtend12 f.imm = BitVec.ofNat 64 f.di)
    (hdst : f.di + fieldWriteLen f ≤ outBytes.length)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + fieldSize f < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes f.data) ++ bs.drop (O + fieldEnc f)) :
    decode (bs.drop O) = some (.bytes f.data, bs.drop (O + fieldEnc f)) := by
  have hsize_data : (encode (.bytes f.data)).length < 256 ^ 8 := by
    simpa [hbyte] using hsize
  have hdst_data : f.di + f.data.length ≤ outBytes.length := by
    simpa [fieldWriteLen, hbyte] using hdst
  have hcode_data : base.toNat + (148 + 4 + 20 * f.data.length) < 2 ^ 64 := by
    simpa [fieldSize, hbyte] using hcode
  exact byteFieldStep_decode base regionBase outBase rOut f.imm bs O f.data
    (bs.drop (O + fieldEnc f)) outBytes f.di hsize_data halign hdalign hover hwin hImm hdst_data
    hdov hdval hcode_data hdrop

/-- Schema-facing scalar field step.  The scalar guard is only the static canonicality condition
    needed by the success path, while the produced postcondition is still `fieldUpdate`. -/
def scalarFieldSpecStepCert
    (base regionBase outBase : Word) (rOut : Reg)
    (bs : List Byte) (O : Nat) (outBytes : List Byte) (f : FieldSpec)
    (hscalar : f.isScalar = true)
    (hsize : (if f.isScalar then f.data.length ≤ 8
      else (encode (.bytes f.data)).length < 256 ^ 8))
    (hcanon : f.data = [] ∨ f.data.headD 1 ≠ 0)
    (hImm : signExtend12 f.imm = BitVec.ofNat 64 f.di)
    (hdst : f.di + fieldWriteLen f ≤ outBytes.length)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + fieldSize f < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes f.data) ++ bs.drop (O + fieldEnc f)) :
    WP.CFG.Cert base (base + BitVec.ofNat 64 (fieldSize f))
      (fieldCR base rOut f)
      (schemaINV regionBase outBase rOut bs (O + fieldEnc f) (fieldUpdate outBytes f)) := by
  have hlen8 : f.data.length ≤ 8 := by
    simpa [hscalar] using hsize
  have hdst8 : f.di + 8 ≤ outBytes.length := by
    simpa [fieldWriteLen, hscalar] using hdst
  have hcode_scalar : base.toNat + (if f.data = [] then 248 else 280) < 2 ^ 64 := by
    simpa [fieldSize, hscalar] using hcode
  have cert := scalarFieldStepCert base regionBase outBase rOut f.imm bs O f.data
    (bs.drop (O + fieldEnc f)) outBytes f.di hlen8 hcanon halign hdalign hover hwin hImm hdst8
    hdov hdval hcode_scalar hdrop
  simpa [fieldCR, fieldEnc, fieldUpdate, fieldSize, hscalar] using cert

/-- Pure scalar decode fact produced by `scalarFieldSpecStepCert`. -/
theorem scalarFieldSpecStep_decode
    (base regionBase outBase : Word) (rOut : Reg)
    (bs : List Byte) (O : Nat) (outBytes : List Byte) (f : FieldSpec)
    (hscalar : f.isScalar = true)
    (hsize : (if f.isScalar then f.data.length ≤ 8
      else (encode (.bytes f.data)).length < 256 ^ 8))
    (hcanon : f.data = [] ∨ f.data.headD 1 ≠ 0)
    (hImm : signExtend12 f.imm = BitVec.ofNat 64 f.di)
    (hdst : f.di + fieldWriteLen f ≤ outBytes.length)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + fieldSize f < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes f.data) ++ bs.drop (O + fieldEnc f)) :
    decodeScalar (bs.drop O) = some (Nat.fromBytesBE f.data, bs.drop (O + fieldEnc f)) := by
  have hlen8 : f.data.length ≤ 8 := by
    simpa [hscalar] using hsize
  have hdst8 : f.di + 8 ≤ outBytes.length := by
    simpa [fieldWriteLen, hscalar] using hdst
  have hcode_scalar : base.toNat + (if f.data = [] then 248 else 280) < 2 ^ 64 := by
    simpa [fieldSize, hscalar] using hcode
  exact scalarFieldStep_decode base regionBase outBase rOut f.imm bs O f.data
    (bs.drop (O + fieldEnc f)) outBytes f.di hlen8 hcanon halign hdalign hover hwin hImm hdst8
    hdov hdval hcode_scalar hdrop

/-- Field-step automation: choose the scalar or byte WP certificate from the field descriptor. -/
def fieldSpecStepCert
    (base regionBase outBase : Word) (rOut : Reg)
    (bs : List Byte) (O : Nat) (outBytes : List Byte) (f : FieldSpec)
    (hsize : (if f.isScalar then f.data.length ≤ 8
      else (encode (.bytes f.data)).length < 256 ^ 8))
    (hcanon : f.isScalar = true → f.data = [] ∨ f.data.headD 1 ≠ 0)
    (hImm : signExtend12 f.imm = BitVec.ofNat 64 f.di)
    (hdst : f.di + fieldWriteLen f ≤ outBytes.length)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + fieldSize f < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes f.data) ++ bs.drop (O + fieldEnc f)) :
    WP.CFG.Cert base (base + BitVec.ofNat 64 (fieldSize f))
      (fieldCR base rOut f)
      (schemaINV regionBase outBase rOut bs (O + fieldEnc f) (fieldUpdate outBytes f)) := by
  by_cases hscalar : f.isScalar = true
  · exact scalarFieldSpecStepCert base regionBase outBase rOut bs O outBytes f hscalar hsize
      (hcanon hscalar) hImm hdst halign hdalign hover hwin hdov hdval hcode hdrop
  · have hbyte : f.isScalar = false := by
      cases hs : f.isScalar with
      | false => rfl
      | true => exact False.elim (hscalar hs)
    exact byteFieldSpecStepCert base regionBase outBase rOut bs O outBytes f hbyte hsize hImm hdst
      halign hdalign hover hwin hdov hdval hcode hdrop

/-- Pure decode fact paired with `fieldSpecStepCert`. -/
theorem fieldSpecStep_decode
    (base regionBase outBase : Word) (rOut : Reg)
    (bs : List Byte) (O : Nat) (outBytes : List Byte) (f : FieldSpec)
    (hsize : (if f.isScalar then f.data.length ≤ 8
      else (encode (.bytes f.data)).length < 256 ^ 8))
    (hcanon : f.isScalar = true → f.data = [] ∨ f.data.headD 1 ≠ 0)
    (hImm : signExtend12 f.imm = BitVec.ofNat 64 f.di)
    (hdst : f.di + fieldWriteLen f ≤ outBytes.length)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + fieldSize f < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes f.data) ++ bs.drop (O + fieldEnc f)) :
    (if f.isScalar then
      decodeScalar (bs.drop O) = some (Nat.fromBytesBE f.data, bs.drop (O + fieldEnc f))
     else
      decode (bs.drop O) = some (.bytes f.data, bs.drop (O + fieldEnc f))) := by
  by_cases hscalar : f.isScalar = true
  · simpa [hscalar] using scalarFieldSpecStep_decode base regionBase outBase rOut bs O outBytes f
      hscalar hsize (hcanon hscalar) hImm hdst halign hdalign hover hwin hdov hdval hcode hdrop
  · have hbyte : f.isScalar = false := by
      cases hs : f.isScalar with
      | false => rfl
      | true => exact False.elim (hscalar hs)
    simpa [hbyte] using byteFieldSpecStep_decode base regionBase outBase rOut bs O outBytes f hbyte
      hsize hImm hdst halign hdalign hover hwin hdov hdval hcode hdrop


end SchemaWP

end EvmAsm.Rv64.RLP
