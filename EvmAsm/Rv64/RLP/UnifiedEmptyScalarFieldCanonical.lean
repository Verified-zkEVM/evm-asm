/-
  EvmAsm.Rv64.RLP.UnifiedEmptyScalarFieldCanonical

  EL.3 / Phase 5 — the canonical re-entry chain for the EMPTY (`n=0`) scalar field unit
  (`UnifiedEmptyScalarField`), paralleling the non-empty scalar region chain
  (`_at_regOwn` → `_canonical` → `_fully_canonical`). The empty unit has the identical scratch
  pre/post shape as the non-empty scalar region unit (only the spill value `0`, the `x13` stride,
  the step count and code range differ), so each peeling layer mirrors its scalar counterpart with
  the underlying unit swapped. The endpoint
  `unified_empty_scalar_field_decode_and_store_region_fully_canonical` has the uniform all-`regOwn`
  scratch interface the N-field fold (`schema_walk`) consumes, with CR `emptyScalarUnitCR` — the
  prerequisite for integrating zero-valued scalar fields into the schema engine.
-/

import EvmAsm.Rv64.RLP.UnifiedEmptyScalarField
import EvmAsm.Rv64.RLP.FieldUnitDisjoint

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **`regOwn`-re-entry empty-scalar field.** As `unified_empty_scalar_field_decode_and_store_region`
    but `x5, x10, x11, x12` are `regOwn` in the precondition — callable after a prior field. -/
theorem unified_empty_scalar_field_decode_and_store_region_at_regOwn
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v14Old v15Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop O = encode (.bytes ([] : List Byte)) ++ tail)
    (hdalign : outBase.toNat % 8 = 0) (hdst : di0 + 8 ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hcode : base.toNat + (148 + 4 + 12 * 8) < 2 ^ 64) :
    cpsTripleWithin (61 + (1 + 3 * 8)) base (base + 148 + 4 + BitVec.ofNat 64 (12 * 8))
      (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        ((CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm)).union
          (spillChainCR (base + 148 + 4) 8)))
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x11) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + 8))) ** (rOut ↦ᵣ outBase) **
        bytesRegion outBase
          (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE ([] : List Byte))) di0 8)) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes ([] : List Byte))).length))) **
        regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old)))
    ∧ decodeScalar (bs.drop O) = some (0, tail) := by
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
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (unified_empty_scalar_field_decode_and_store_region base regionBase rOut outBase fieldImm bs O
        tail outBytes di0 v5 v10 v11 v12 v14Old v15Old halign hover hwin hdrop hdalign hdst hdov
        hdval hImm hcode).1
  · exact (unified_empty_scalar_field_decode_and_store_region base regionBase rOut outBase fieldImm
      bs O tail outBytes di0 0 0 0 0 v14Old v15Old halign hover hwin hdrop hdalign hdst hdov hdval
      hImm hcode).2

set_option maxRecDepth 8000 in
/-- **Canonical empty-scalar field.** As `…_at_regOwn` but `x15` is also `regOwn` in the
    precondition (CR named `emptyScalarUnitCR`). -/
theorem unified_empty_scalar_field_decode_and_store_region_canonical
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v14Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop O = encode (.bytes ([] : List Byte)) ++ tail)
    (hdalign : outBase.toNat % 8 = 0) (hdst : di0 + 8 ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hcode : base.toNat + (148 + 4 + 12 * 8) < 2 ^ 64) :
    cpsTripleWithin (61 + (1 + 3 * 8)) base (base + 148 + 4 + BitVec.ofNat 64 (12 * 8))
      (emptyScalarUnitCR base rOut fieldImm)
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (regOwn .x15) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x11) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + 8))) ** (rOut ↦ᵣ outBase) **
        bytesRegion outBase
          (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE ([] : List Byte))) di0 8)) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes ([] : List Byte))).length))) **
        regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (regOwn .x15)))
    ∧ decodeScalar (bs.drop O) = some (0, tail) := by
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
      (unified_empty_scalar_field_decode_and_store_region_at_regOwn base regionBase rOut outBase
        fieldImm bs O tail outBytes di0 v14Old v15 halign hover hwin hdrop hdalign hdst hdov hdval
        hImm hcode).1
  · exact (unified_empty_scalar_field_decode_and_store_region_at_regOwn base regionBase rOut outBase
      fieldImm bs O tail outBytes di0 v14Old 0 halign hover hwin hdrop hdalign hdst hdov hdval hImm
      hcode).2

set_option maxRecDepth 8000 in
/-- **Fully-canonical empty-scalar field.** As `…_canonical` but `x14` is also `regOwn` in both
    pre and post — the uniform scratch interface the N-field fold consumes. -/
theorem unified_empty_scalar_field_decode_and_store_region_fully_canonical
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop O = encode (.bytes ([] : List Byte)) ++ tail)
    (hdalign : outBase.toNat % 8 = 0) (hdst : di0 + 8 ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hcode : base.toNat + (148 + 4 + 12 * 8) < 2 ^ 64) :
    cpsTripleWithin (61 + (1 + 3 * 8)) base (base + 148 + 4 + BitVec.ofNat 64 (12 * 8))
      (emptyScalarUnitCR base rOut fieldImm)
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (regOwn .x14) **
        (regOwn .x15) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x11) ** (regOwn .x14) ** (rOut ↦ᵣ outBase) **
        bytesRegion outBase
          (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE ([] : List Byte))) di0 8)) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes ([] : List Byte))).length))) **
        regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (regOwn .x15)))
    ∧ decodeScalar (bs.drop O) = some (0, tail) := by
  refine ⟨?_, ?_⟩
  · refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x14)
        (P := (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
          (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (regOwn .x15) ** bytesRegion regionBase bs ** ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
        (fun v14 => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x14))))
      (unified_empty_scalar_field_decode_and_store_region_canonical base regionBase rOut outBase
        fieldImm bs O tail outBytes di0 v14 halign hover hwin hdrop hdalign hdst hdov hdval hImm
        hcode).1
  · exact (unified_empty_scalar_field_decode_and_store_region_canonical base regionBase rOut outBase
      fieldImm bs O tail outBytes di0 0 halign hover hwin hdrop hdalign hdst hdov hdval hImm hcode).2

end EvmAsm.Rv64.RLP
