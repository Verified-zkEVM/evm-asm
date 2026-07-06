/-
  EvmAsm.Rv64.RLP.UnifiedScalarFieldRegionCanonical

  EL.3 / Phase 5 — the CANONICAL re-entry form of the scalar-into-region field unit, with a
  uniform all-`regOwn` scratch interface for `x5, x10, x11, x12, x15`. The byte-array unit
  releases `x15` as `regOwn` (it uses it as the copy counter), whereas the scalar unit framed
  `x15` through concretely; that mismatch blocked a byte-array → scalar field boundary in a
  mixed schema. This variant takes AND releases `x15` as `regOwn` (the scalar decode never
  reads it — it is framed through untouched — so weakening it to `regOwn` in the post and then
  peeling it in the pre is sound), giving the uniform interface the N-field heterogeneous fold
  needs to chain fields in any order. `x14` stays a concrete `∀`-parameter (each unit overwrites
  it via `ADDI x14, rOut, fieldImm`, so the prior field's concrete `x14` feeds in directly).

  Built from `unified_scalar_field_decode_and_store_region_at_regOwn` (#9147) by weakening its
  post `x15 ↦ v15` to `regOwn x15` (value-independent) and then peeling `x15` in the pre.
-/

import EvmAsm.Rv64.RLP.UnifiedBytesFieldRegOwn
import EvmAsm.Rv64.RLP.FieldUnitDisjoint

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics


/-- **`regOwn`-re-entry non-empty scalar field.** As
    `unified_scalar_field_decode_and_store_region` but `x5, x10, x11, x12` are `regOwn` in the
    precondition, so it can be called after a previous field unit. -/
theorem unified_scalar_field_decode_and_store_region_at_regOwn
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v14Old v15Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen8 : data.length ≤ 8) (hhead : data.headD 1 ≠ 0)
    (hsize : (encode (.bytes data)).length < 256 ^ 8)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hdst : di0 + 8 ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + 280 < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    cpsTripleWithin ((61 + (2 + 6 * data.length)) + (1 + 3 * 8)) base
      (base + 180 + 4 + BitVec.ofNat 64 (12 * 8))
      (scalarRegionUnitCR base rOut fieldImm)
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x11) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + 8))) ** (rOut ↦ᵣ outBase) **
        bytesRegion outBase
          (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE data)) di0 8)) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old)))
    ∧ decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail) := by
  refine ⟨?_, ?_⟩
  · refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes) **
          regOwn .x10 ** regOwn .x11 ** regOwn .x12)
        (fun v5 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes) **
          (.x5 ↦ᵣ v5) ** regOwn .x11 ** regOwn .x12)
        (fun v10 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes) **
          (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** regOwn .x12)
        (fun v11 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes) **
          (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11))
        (fun v12 => ?_))
    unfold scalarRegionUnitCR
    rw [CodeReq.union_assoc]
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (unified_scalar_field_decode_and_store_region base regionBase rOut outBase fieldImm bs O
        data tail outBytes di0 v5 v10 v11 v12 v14Old v15Old hlen1 hlen8 hhead hsize
        halign hdalign hover hwin hImm hdst hdov hdval hcode hdrop).1
  · exact (unified_scalar_field_decode_and_store_region base regionBase rOut outBase fieldImm bs O
      data tail outBytes di0 0 0 0 0 v14Old v15Old hlen1 hlen8 hhead hsize halign hdalign hover
      hwin hImm hdst hdov hdval hcode hdrop).2

/-- **Canonical non-empty scalar field.** As `…_at_regOwn` but `x15` is also `regOwn` in the
    precondition and postcondition. -/
theorem unified_scalar_field_decode_and_store_region_canonical
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v14Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen8 : data.length ≤ 8) (hhead : data.headD 1 ≠ 0)
    (hsize : (encode (.bytes data)).length < 256 ^ 8)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hdst : di0 + 8 ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + 280 < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    cpsTripleWithin ((61 + (2 + 6 * data.length)) + (1 + 3 * 8)) base
      (base + 180 + 4 + BitVec.ofNat 64 (12 * 8))
      (scalarRegionUnitCR base rOut fieldImm)
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (regOwn .x15) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x11) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + 8))) ** (rOut ↦ᵣ outBase) **
        bytesRegion outBase
          (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE data)) di0 8)) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (regOwn .x15)))
    ∧ decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail) := by
  refine ⟨?_, ?_⟩
  · refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x15)
        (P := (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
          (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
          bytesRegion regionBase bs ** ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
        (fun v15 => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (regIs_implies_regOwn .x15))))))))
      (unified_scalar_field_decode_and_store_region_at_regOwn base regionBase rOut outBase
        fieldImm bs O data tail outBytes di0 v14Old v15 hlen1 hlen8 hhead hsize halign hdalign
        hover hwin hImm hdst hdov hdval hcode hdrop).1
  · exact (unified_scalar_field_decode_and_store_region_at_regOwn base regionBase rOut outBase
      fieldImm bs O data tail outBytes di0 v14Old 0 hlen1 hlen8 hhead hsize halign hdalign hover
      hwin hImm hdst hdov hdval hcode hdrop).2

set_option maxRecDepth 8000 in
/-- **Canonical byte-array field decode-and-copy into region.** As
    `unified_bytes_field_decode_and_copy_at_regOwn` but `x15` is also owned abstractly (`regOwn`)
    in the precondition — the same uniform all-`regOwn` scratch interface (`x5, x10, x11, x12,
    x15`) as the canonical scalar unit. The byte-array unit already overwrites `x15` (the copy
    counter) and releases it as `regOwn`, so accepting it `regOwn` in the pre just peels it. -/
theorem unified_bytes_field_decode_and_copy_canonical
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v14Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen55 : data.length ≤ 55)
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
    cpsTripleWithin (61 + (1 + 5 * data.length)) base
        (base + 148 + 4 + BitVec.ofNat 64 (20 * data.length))
      (bytesUnitCR base rOut fieldImm data.length)
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (regOwn .x15) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + data.length))) ** (regOwn .x15) **
        (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
        bytesRegion outBase (copyRangeGen outBytes data 0 di0 data.length)) **
       (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11))
    ∧ decode (bs.drop O) = some (.bytes data, tail) := by
  refine ⟨?_, ?_⟩
  · refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x15)
        (P := (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
          (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
          bytesRegion regionBase bs ** ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
        (fun v15 => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (unified_bytes_field_decode_and_copy_at_regOwn base regionBase rOut outBase fieldImm bs O data
        tail outBytes di0 v14Old v15 hlen1 hlen55 hsize halign hdalign hover hwin hImm hdst hdov
        hdval hcode hdrop).1
  · exact (unified_bytes_field_decode_and_copy_at_regOwn base regionBase rOut outBase fieldImm bs O
      data tail outBytes di0 v14Old 0 hlen1 hlen55 hsize halign hdalign hover hwin hImm hdst hdov
      hdval hcode hdrop).2

end EvmAsm.Rv64.RLP
