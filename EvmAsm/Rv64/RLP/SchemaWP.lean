/-
  EvmAsm.Rv64.RLP.SchemaWP

  WP-facing adapters for fixed-schema RLP field units.  The canonical field
  proofs expose the right machine behavior but their postconditions are ordered
  for local composition; this file normalizes them to `schemaINV`, so callers can
  use a field as a one-step weakest-precondition certificate.
-/

import EvmAsm.Rv64.RLP.SchemaFold
import EvmAsm.Rv64.RLP.SchemaListEncode
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

/-- Scalar canonicality side conditions for a successful schema witness.  This is deliberately
    separate from the static layout: it talks about the field bytes being proved on a success path. -/
def SchemaCanonical : List FieldSpec → Prop
  | [] => True
  | f :: rest => (f.isScalar = true → f.data = [] ∨ f.data.headD 1 ≠ 0) ∧ SchemaCanonical rest

/-- A field descriptor with its validity/drop evidence determines the pure decode fact for that
    field.  This is machine-independent: the static layout evidence is separate from the decoded
    payload witness, and scalar canonicality is used only on the scalar success path. -/
theorem fieldSpecStep_decode_of_valid
    (bs : List Byte) (O : Nat) (f : FieldSpec)
    (hsize : (if f.isScalar then f.data.length ≤ 8
      else (encode (.bytes f.data)).length < 256 ^ 8))
    (hcanon : f.isScalar = true → f.data = [] ∨ f.data.headD 1 ≠ 0)
    (hdrop : bs.drop O = encode (.bytes f.data) ++ bs.drop (O + fieldEnc f)) :
    (if f.isScalar then
      decodeScalar (bs.drop O) = some (Nat.fromBytesBE f.data, bs.drop (O + fieldEnc f))
     else
      decode (bs.drop O) = some (.bytes f.data, bs.drop (O + fieldEnc f))) := by
  by_cases hscalar : f.isScalar = true
  · have henc : (encode (.bytes f.data)).length < 256 ^ 8 :=
      scalarField_encode_size_of_len_le_8 f.data (by simpa [hscalar] using hsize)
    have hdec : decode (bs.drop O) = some (.bytes f.data, bs.drop (O + fieldEnc f)) := by
      rw [hdrop]
      exact decode_encode_append (.bytes f.data) (bs.drop (O + fieldEnc f)) henc
    have hheadD : f.data.headD (1 : Byte) ≠ (0 : Byte) := by
      cases hcanon hscalar with
      | inl hnil => simp [hnil]
      | inr h => simpa using h
    have hhead : ¬ f.data.head?.getD (BitVec.ofNat 8 1) = BitVec.ofNat 8 0 := by
      cases hd : f.data with
      | nil => simp
      | cons b _ =>
          have hb : b ≠ (0 : Byte) := by simpa [hd] using hheadD
          simpa [hd] using hb
    simp [hscalar, decodeScalar, hdec, hhead]
  · have hbyte : f.isScalar = false := by
      cases hs : f.isScalar with
      | false => rfl
      | true => exact False.elim (hscalar hs)
    have henc : (encode (.bytes f.data)).length < 256 ^ 8 := by
      simpa [hbyte] using hsize
    have hdec : decode (bs.drop O) = some (.bytes f.data, bs.drop (O + fieldEnc f)) := by
      rw [hdrop]
      exact decode_encode_append (.bytes f.data) (bs.drop (O + fieldEnc f)) henc
    simpa [hbyte] using hdec

/-- Fold the pure decode facts over a whole successful schema witness.  This mirrors
    `schemaStep_spec_within`, but it has no machine-side premises and can be used
    by semantic bridges such as withdrawal decoding. -/
theorem schemaDecodes_of_valid_canonical
    (bs : List Byte) :
    ∀ (specs : List FieldSpec) (O outLen : Nat),
      SchemaValid bs outLen O specs → SchemaCanonical specs → schemaDecodes bs O specs := by
  intro specs
  induction specs with
  | nil => intro O outLen _ _; simp [schemaDecodes]
  | cons f rest ih =>
      intro O outLen hvalid hcanon
      obtain ⟨hsize, _hImm, _hdst, hdrop, hvalid_tail⟩ := hvalid
      obtain ⟨hcanon_head, hcanon_tail⟩ := hcanon
      constructor
      · exact fieldSpecStep_decode_of_valid bs O f hsize hcanon_head hdrop
      · exact ih (O + fieldEnc f) outLen hvalid_tail hcanon_tail

/-- Soundness view of `fieldSpecStepCert` with the precondition exposed as `schemaINV`. -/
theorem fieldSpecStep_spec_within
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
    cpsTripleWithin (fieldSteps f) base (base + BitVec.ofNat 64 (fieldSize f))
      (fieldCR base rOut f)
      (schemaINV regionBase outBase rOut bs O outBytes)
      (schemaINV regionBase outBase rOut bs (O + fieldEnc f) (fieldUpdate outBytes f)) := by
  by_cases hscalar : f.isScalar = true
  · have hlen8 : f.data.length ≤ 8 := by
      simpa [hscalar] using hsize
    have hdst8 : f.di + 8 ≤ outBytes.length := by
      simpa [fieldWriteLen, hscalar] using hdst
    have hcode_scalar : base.toNat + (if f.data = [] then 248 else 280) < 2 ^ 64 := by
      simpa [fieldSize, hscalar] using hcode
    by_cases hnil : f.data = []
    · have hexit : base + 148 + 4 + BitVec.ofNat 64 (12 * 8) = base + BitVec.ofNat 64 248 := by
        bv_omega
      have hcode_empty : base.toNat + (148 + 4 + 12 * 8) < 2 ^ 64 := by
        simpa [hnil] using hcode_scalar
      have hdrop_empty : bs.drop O = encode (.bytes ([] : List Byte)) ++ bs.drop (O + fieldEnc f) := by
        simpa [hnil] using hdrop
      have hspec := (((WP.CFG.block
        (scalarFieldPost_entails_schemaINV regionBase outBase rOut bs O ([] : List Byte) outBytes f.di)
        (unified_empty_scalar_field_decode_and_store_region_fully_canonical base regionBase rOut
          outBase f.imm bs O (bs.drop (O + fieldEnc f)) outBytes f.di halign hover hwin hdrop_empty
          hdalign hdst8 hdov hdval hImm hcode_empty).1).changeExit hexit).weakenPre
        (schemaINV_entails_byteFieldPre regionBase outBase rOut bs O outBytes)).sound
      simpa [fieldSteps, fieldSize, fieldCR, fieldEnc, fieldUpdate, hscalar, hnil] using hspec
    · have hlen1 : 1 ≤ f.data.length := by
        cases hd : f.data with
        | nil => exact False.elim (hnil hd)
        | cons _ _ => simp
      have hhead : f.data.headD 1 ≠ 0 := by
        cases hcanon hscalar with
        | inl h => exact False.elim (hnil h)
        | inr h => exact h
      have henc : (encode (.bytes f.data)).length < 256 ^ 8 :=
        scalarField_encode_size_of_len_le_8 f.data hlen8
      have hcode_data : base.toNat + 280 < 2 ^ 64 := by
        simpa [hnil] using hcode_scalar
      have hexit : base + 180 + 4 + BitVec.ofNat 64 (12 * 8) = base + BitVec.ofNat 64 280 := by
        bv_omega
      have hspec := (((WP.CFG.block
        (scalarFieldPost_entails_schemaINV regionBase outBase rOut bs O f.data outBytes f.di)
        (unified_scalar_field_decode_and_store_region_fully_canonical base regionBase rOut outBase
          f.imm bs O f.data (bs.drop (O + fieldEnc f)) outBytes f.di hlen1 hlen8 hhead henc
          halign hdalign hover hwin hImm hdst8 hdov hdval hcode_data hdrop).1).changeExit hexit).weakenPre
        (schemaINV_entails_byteFieldPre regionBase outBase rOut bs O outBytes)).sound
      simpa [fieldSteps, fieldSize, fieldCR, fieldEnc, fieldUpdate, hscalar, hnil] using hspec
  · have hbyte : f.isScalar = false := by
      cases hs : f.isScalar with
      | false => rfl
      | true => exact False.elim (hscalar hs)
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
    by_cases hnil : f.data = []
    · have hdrop_empty : bs.drop O = encode (.bytes ([] : List Byte)) ++ bs.drop (O + fieldEnc f) := by
        simpa [hnil] using hdrop
      have hdst_empty : f.di + ([] : List Byte).length ≤ outBytes.length := by
        simpa [hnil] using hdst_data
      have hcode_empty : base.toNat + (148 + 4 + 20 * ([] : List Byte).length) < 2 ^ 64 := by
        simpa [hnil] using hcode_data
      have hexit_empty : base + 148 + 4 + BitVec.ofNat 64 (20 * ([] : List Byte).length)
          = base + BitVec.ofNat 64 (fieldSize f) := by
        simpa [hnil] using hexit
      have hspec := (((WP.CFG.block
        (byteFieldPost_entails_schemaINV regionBase outBase rOut bs O ([] : List Byte) outBytes f.di)
        (unified_empty_bytes_field_decode_and_copy_fully_canonical base regionBase rOut outBase
          f.imm bs O (bs.drop (O + fieldEnc f)) outBytes f.di halign hdalign hover hwin hImm hdst_empty
          hdov hdval hcode_empty hdrop_empty).1).changeExit hexit_empty).weakenPre
        (schemaINV_entails_byteFieldPre regionBase outBase rOut bs O outBytes)).sound
      simpa [fieldSteps, fieldSize, fieldCR, fieldEnc, fieldUpdate, hbyte, hnil] using hspec
    · by_cases hshort : f.data.length ≤ 55
      · have hlen1 : 1 ≤ f.data.length := by
          cases hd : f.data with
          | nil => exact False.elim (hnil hd)
          | cons _ _ => simp
        have hspec := (((WP.CFG.block
          (byteFieldPost_entails_schemaINV regionBase outBase rOut bs O f.data outBytes f.di)
          (unified_bytes_field_decode_and_copy_fully_canonical base regionBase rOut outBase f.imm
            bs O f.data (bs.drop (O + fieldEnc f)) outBytes f.di hlen1 hshort hsize_data halign
            hdalign hover hwin hImm hdst_data hdov hdval hcode_data hdrop).1).changeExit hexit).weakenPre
          (schemaINV_entails_byteFieldPre regionBase outBase rOut bs O outBytes)).sound
        simpa [fieldSteps, fieldSize, fieldCR, fieldEnc, fieldUpdate, hbyte, hnil] using hspec
      · have hlong : 55 < f.data.length := by omega
        have hspec := (((WP.CFG.block
          (byteFieldPost_entails_schemaINV regionBase outBase rOut bs O f.data outBytes f.di)
          (unified_long_bytes_field_decode_and_copy_fully_canonical base regionBase rOut outBase
            f.imm bs O f.data (bs.drop (O + fieldEnc f)) outBytes f.di hlong hsize_data halign
            hdalign hover hwin hImm hdst_data hdov hdval hcode_data hdrop).1).changeExit hexit).weakenPre
          (schemaINV_entails_byteFieldPre regionBase outBase rOut bs O outBytes)).sound
        simpa [fieldSteps, fieldSize, fieldCR, fieldEnc, fieldUpdate, hbyte, hnil] using hspec


/-- CPS theorem for a whole schema: the program/post pair reduces to the initial schema invariant. -/
theorem schemaStep_spec_within
    (base regionBase outBase : Word) (rOut : Reg)
    (bs : List Byte) (O : Nat) (outBytes : List Byte) (specs : List FieldSpec)
    (hvalid : SchemaValid bs outBytes.length O specs)
    (hcanon : SchemaCanonical specs)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize specs < 2 ^ 64) :
    cpsTripleWithin (schemaSteps specs) base (base + BitVec.ofNat 64 (schemaSize specs))
      (schemaCR base rOut specs)
      (schemaINV regionBase outBase rOut bs O outBytes)
      (schemaINV regionBase outBase rOut bs (O + schemaEnc specs) (schemaOut outBytes specs)) := by
  induction specs generalizing base O outBytes with
  | nil =>
      simpa [schemaSteps, schemaSize, schemaCR, schemaEnc, schemaOut] using
        (cpsTripleWithin_refl (addr := base)
          (P := schemaINV regionBase outBase rOut bs O outBytes)
          (Q := schemaINV regionBase outBase rOut bs O outBytes)
          (fun h hp => hp))
  | cons f rest ih =>
      obtain ⟨hsize, hImm, hdst, hdrop, hvalid_tail⟩ := hvalid
      obtain ⟨hcanon_head, hcanon_tail⟩ := hcanon
      have hfield_code : base.toNat + fieldSize f < 2 ^ 64 := by
        have hsz : schemaSize (f :: rest) = fieldSize f + schemaSize rest := rfl
        omega
      have hfield := fieldSpecStep_spec_within base regionBase outBase rOut bs O outBytes f hsize
        hcanon_head hImm hdst halign hdalign hover hwin hdov hdval hfield_code hdrop
      have hbase_tail : (base + BitVec.ofNat 64 (fieldSize f)).toNat = base.toNat + fieldSize f := by
        bv_omega
      have hcode_tail : (base + BitVec.ofNat 64 (fieldSize f)).toNat + schemaSize rest < 2 ^ 64 := by
        rw [hbase_tail]
        have hsz : schemaSize (f :: rest) = fieldSize f + schemaSize rest := rfl
        omega
      have hvalid_tail_step : SchemaValid bs (fieldUpdate outBytes f).length (O + fieldEnc f) rest := by
        simpa [fieldUpdate_length] using hvalid_tail
      have hdov_tail : outBase.toNat + (fieldUpdate outBytes f).length < 2 ^ 64 := by
        simpa [fieldUpdate_length] using hdov
      have hdval_tail : ∀ i, i < (fieldUpdate outBytes f).length →
          isValidByteAccess (outBase + BitVec.ofNat 64 i) = true := by
        intro i hi
        exact hdval i (by simpa [fieldUpdate_length] using hi)
      have htail := ih (base := base + BitVec.ofNat 64 (fieldSize f))
        (O := O + fieldEnc f) (outBytes := fieldUpdate outBytes f)
        hvalid_tail_step hcanon_tail hdov_tail hdval_tail hcode_tail
      have hd : (fieldCR base rOut f).Disjoint
          (schemaCR (base + BitVec.ofNat 64 (fieldSize f)) rOut rest) := by
        refine codeReq_disjoint_of_ranges _ _ (base.toNat + fieldSize f) ?_ ?_
        · intro a ha
          exact fieldCR_none_above base rOut f a hfield_code ha
        · intro a ha
          exact schemaCR_none_below rOut rest (base + BitVec.ofNat 64 (fieldSize f)) a
            hcode_tail (by rw [hbase_tail]; exact ha)
      have hseq := cpsTripleWithin_seq hd hfield htail
      have hexit : base + BitVec.ofNat 64 (fieldSize f) + BitVec.ofNat 64 (schemaSize rest) =
          base + BitVec.ofNat 64 (fieldSize f + schemaSize rest) := by
        bv_omega
      rw [hexit] at hseq
      simpa [schemaSteps, schemaSize, schemaCR, schemaEnc, schemaOut, Nat.add_assoc] using hseq

/-- WP certificate for a whole schema, exposing the reduced precondition as the certificate pre. -/
def schemaStepCert
    (base regionBase outBase : Word) (rOut : Reg)
    (bs : List Byte) (O : Nat) (outBytes : List Byte) (specs : List FieldSpec)
    (hvalid : SchemaValid bs outBytes.length O specs)
    (hcanon : SchemaCanonical specs)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize specs < 2 ^ 64) :
    WP.CFG.Cert base (base + BitVec.ofNat 64 (schemaSize specs))
      (schemaCR base rOut specs)
      (schemaINV regionBase outBase rOut bs (O + schemaEnc specs) (schemaOut outBytes specs)) :=
  WP.CFG.block (WP.Entails.refl _)
    (schemaStep_spec_within base regionBase outBase rOut bs O outBytes specs hvalid hcanon
      halign hdalign hover hwin hdov hdval hcode)

/-- The computed WP precondition of schemaStepCert is the schema invariant before the schema. -/
theorem schemaStepCert_pre
    (base regionBase outBase : Word) (rOut : Reg)
    (bs : List Byte) (O : Nat) (outBytes : List Byte) (specs : List FieldSpec)
    (hvalid : SchemaValid bs outBytes.length O specs)
    (hcanon : SchemaCanonical specs)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize specs < 2 ^ 64) :
    (schemaStepCert base regionBase outBase rOut bs O outBytes specs hvalid hcanon halign hdalign
      hover hwin hdov hdval hcode).pre = schemaINV regionBase outBase rOut bs O outBytes :=
  rfl

/-- Build `SchemaValid` for a complete short-list-encoded schema input.
    The schema payload starts after the one-byte list header, so the WP offset is `1`. -/
theorem schemaValid_of_encoded_list_short
    (bs : List Byte) (outLen : Nat) (specs : List FieldSpec)
    (hcore : ∀ f, f ∈ specs → fieldCoreValid outLen f)
    (hlen : (schemaEncBytes specs).length ≤ 55)
    (hinput : bs = encode (.list (schemaItems specs))) :
    SchemaValid bs outLen 1 specs :=
  schemaValid_of_concat bs outLen ([] : List Byte) specs 1 hcore
    (schemaConcat_of_encoded_list_short bs specs hlen hinput)

/-- WP certificate for a whole schema whose input is the complete short-list
    encoding of the field items.  This removes the caller-side payload concat
    proof and exposes the reduced precondition at offset `1`. -/
def schemaStepCertOfEncodedListShort
    (base regionBase outBase : Word) (rOut : Reg)
    (bs outBytes : List Byte) (specs : List FieldSpec)
    (hcore : ∀ f, f ∈ specs → fieldCoreValid outBytes.length f)
    (hcanon : SchemaCanonical specs)
    (hlen : (schemaEncBytes specs).length ≤ 55)
    (hinput : bs = encode (.list (schemaItems specs)))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize specs < 2 ^ 64) :
    WP.CFG.Cert base (base + BitVec.ofNat 64 (schemaSize specs))
      (schemaCR base rOut specs)
      (schemaINV regionBase outBase rOut bs (1 + schemaEnc specs) (schemaOut outBytes specs)) :=
  schemaStepCert base regionBase outBase rOut bs 1 outBytes specs
    (schemaValid_of_encoded_list_short bs outBytes.length specs hcore hlen hinput)
    hcanon halign hdalign hover hwin hdov hdval hcode

/-- The encoded-list schema certificate computes the schema invariant at payload offset `1`. -/
theorem schemaStepCertOfEncodedListShort_pre
    (base regionBase outBase : Word) (rOut : Reg)
    (bs outBytes : List Byte) (specs : List FieldSpec)
    (hcore : ∀ f, f ∈ specs → fieldCoreValid outBytes.length f)
    (hcanon : SchemaCanonical specs)
    (hlen : (schemaEncBytes specs).length ≤ 55)
    (hinput : bs = encode (.list (schemaItems specs)))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize specs < 2 ^ 64) :
    (schemaStepCertOfEncodedListShort base regionBase outBase rOut bs outBytes specs hcore hcanon
      hlen hinput halign hdalign hover hwin hdov hdval hcode).pre =
      schemaINV regionBase outBase rOut bs 1 outBytes :=
  rfl


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
