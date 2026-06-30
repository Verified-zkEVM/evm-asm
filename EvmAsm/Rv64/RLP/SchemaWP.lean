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

end SchemaWP

end EvmAsm.Rv64.RLP
