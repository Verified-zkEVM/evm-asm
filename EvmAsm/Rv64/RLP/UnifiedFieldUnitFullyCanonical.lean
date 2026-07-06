/-
  EvmAsm.Rv64.RLP.UnifiedFieldUnitFullyCanonical

  EL.3 / Phase 5 — the FULLY-canonical re-entry field units: ALL scratch registers
  (`x5, x10, x11, x12, x14, x15`) owned abstractly (`regOwn`) in both the pre and post. The
  `…_canonical` units (#9160) already unified `x5, x10, x11, x12, x15`; this peels `x14` as
  well (each unit overwrites `x14` via `ADDI x14, rOut, fieldImm`, so it never reads the
  incoming value — peeling it in the pre, and weakening the advanced value to `regOwn` in the
  post, is sound). The result is a unit whose pre and post differ ONLY in `x13` (the input
  pointer, advanced by the field's encoding length) and the output `bytesRegion` (updated with
  the decoded field) — everything else is a uniform `regOwn`/`x0`/`rOut` frame.

  This uniformity is what lets the N-field heterogeneous fold chain an arbitrary list of fields
  with NO per-field value bookkeeping: every unit has the identical scratch interface.
-/

import EvmAsm.Rv64.RLP.UnifiedScalarFieldRegionCanonical

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **Fully-canonical byte-array field unit.** As `…_canonical` but `x14` is also `regOwn` in
    both pre and post — the same fully uniform scratch interface as the scalar unit. -/
theorem unified_bytes_field_decode_and_copy_fully_canonical
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
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
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (regOwn .x14) **
        (regOwn .x15) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        (regOwn .x14) ** (regOwn .x15) **
        (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
        bytesRegion outBase (copyRangeGen outBytes data 0 di0 data.length)) **
       (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11))
    ∧ decode (bs.drop O) = some (.bytes data, tail) := by
  refine ⟨?_, ?_⟩
  · refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x14)
        (P := (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
          (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (regOwn .x15) ** bytesRegion regionBase bs ** ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
        (fun v14 => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (regIs_implies_regOwn .x14)))))
      (unified_bytes_field_decode_and_copy_canonical base regionBase rOut outBase fieldImm bs O data
        tail outBytes di0 v14 hlen1 hlen55 hsize halign hdalign hover hwin hImm hdst hdov hdval
        hcode hdrop).1
  · exact (unified_bytes_field_decode_and_copy_canonical base regionBase rOut outBase fieldImm bs O
      data tail outBytes di0 0 hlen1 hlen55 hsize halign hdalign hover hwin hImm hdst hdov hdval
      hcode hdrop).2

/-- **Fully-canonical non-empty scalar field unit.** As `…_canonical` but `x14` is also
    `regOwn` in both precondition and postcondition, matching `schemaINV`. -/
theorem unified_scalar_field_decode_and_store_region_fully_canonical
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
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
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (regOwn .x14) **
        (regOwn .x15) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x11) ** (regOwn .x14) ** (rOut ↦ᵣ outBase) **
        bytesRegion outBase
          (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE data)) di0 8)) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (regOwn .x15)))
    ∧ decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail) := by
  refine ⟨?_, ?_⟩
  · refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x14)
        (P := (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
          (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (regOwn .x15) ** bytesRegion regionBase bs ** ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
        (fun v14 => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x14))))
      (unified_scalar_field_decode_and_store_region_canonical base regionBase rOut outBase
        fieldImm bs O data tail outBytes di0 v14 hlen1 hlen8 hhead hsize halign hdalign hover hwin
        hImm hdst hdov hdval hcode hdrop).1
  · exact (unified_scalar_field_decode_and_store_region_canonical base regionBase rOut outBase
      fieldImm bs O data tail outBytes di0 0 hlen1 hlen8 hhead hsize halign hdalign hover hwin hImm
      hdst hdov hdval hcode hdrop).2

end EvmAsm.Rv64.RLP
