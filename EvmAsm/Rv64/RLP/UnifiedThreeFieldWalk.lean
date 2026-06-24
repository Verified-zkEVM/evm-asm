/-
  EvmAsm.Rv64.RLP.UnifiedThreeFieldWalk

  EL.3 / Phase 5 — a THREE-field heterogeneous walk: scalar ⨾ scalar ⨾ byte-array, all
  decoded into one shared output `bytesRegion`. The integration test that exercises BOTH new
  composition pieces together: the scalar-into-region `regOwn` re-entry variant
  (`unified_scalar_field_decode_and_store_region_at_regOwn`, the middle field, callable after a
  prior field clobbered the scratch) and the reusable code-range disjointness
  (`codeReq_disjoint_of_ranges` + the per-unit `…_none_above/_below` lemmas). It demonstrates the
  path scales — disjointness is two `codeReq_disjoint_of_ranges` calls, no per-leaf product — and
  is the direct precursor to the concrete legacy-tx / block-header decoders (fixed unit sequences).

  Layout (program base `base`; field-A offset `OA`):
      base       < scalar A : decode + spill into region >   (base     .. base+280)
      base+280   < scalar B : decode + spill into region >   (base+280 .. base+560)
      base+560   < byte   C : decode + copy  into region >   (base+560 .. base+712+20·|dataC|)
-/

import EvmAsm.Rv64.RLP.FieldUnitDisjoint
import EvmAsm.Rv64.RLP.UnifiedScalarFieldRegionRegOwn
import EvmAsm.Rv64.RLP.UnifiedHeteroFieldWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **Three-field heterogeneous walk (scalar ⨾ scalar ⨾ byte-array, shared output region).**
    Decode scalar A at buffer offset `OA` (spill its u64 LE value into the output region at byte
    offset `diA`), then scalar B (at `OA+len(A)`, spill at `diB`), then byte-array C (at
    `OA+len(A)+len(B)`, copy its payload at `diC`). The output region is threaded directly through
    all three; it ends holding all three fields. Coincides with the scalar decodes of A and B and
    the item decode of C. -/
theorem unified_three_field_walk
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (offA offB offC : BitVec 12)
    (bs : List Byte) (OA : Nat) (dataA dataB dataC tail : List Byte) (outBytes : List Byte)
    (diA diB diC : Nat) (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hlenA1 : 1 ≤ dataA.length) (hlenA8 : dataA.length ≤ 8)
    (hlenB1 : 1 ≤ dataB.length) (hlenB8 : dataB.length ≤ 8)
    (hlenC1 : 1 ≤ dataC.length) (hlenC55 : dataC.length ≤ 55)
    (hsizeC : (encode (.bytes dataC)).length < 256 ^ 8)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hImmA : signExtend12 offA = BitVec.ofNat 64 diA)
    (hImmB : signExtend12 offB = BitVec.ofNat 64 diB)
    (hImmC : signExtend12 offC = BitVec.ofNat 64 diC)
    (hdstA : diA + 8 ≤ outBytes.length) (hdstB : diB + 8 ≤ outBytes.length)
    (hdstC : diC + dataC.length ≤ outBytes.length)
    (hcode : base.toNat + (560 + (152 + 20 * dataC.length)) < 2 ^ 64)
    (hdrop : bs.drop OA =
      encode (.bytes dataA) ++ encode (.bytes dataB) ++ encode (.bytes dataC) ++ tail) :
    cpsTripleWithin
        ((((61 + (2 + 6 * dataA.length)) + (1 + 3 * 8)) +
          ((61 + (2 + 6 * dataB.length)) + (1 + 3 * 8))) + (61 + (1 + 5 * dataC.length))) base
        (base + 712 + BitVec.ofNat 64 (20 * dataC.length))
      (((scalarRegionUnitCR base rOut offA).union (scalarRegionUnitCR (base + 280) rOut offB)).union
        (bytesUnitCR (base + 560) rOut offC dataC.length))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 OA)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64
            (((OA + (encode (.bytes dataA)).length) + (encode (.bytes dataB)).length)
              + (encode (.bytes dataC)).length))) **
        (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (diC + dataC.length))) ** (regOwn .x15) **
        (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
        bytesRegion outBase (copyRangeGen
          (spillRange (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE dataA)) diA 8)
            (BitVec.ofNat 64 (Nat.fromBytesBE dataB)) diB 8)
          dataC 0 diC dataC.length)) **
       (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11))
    ∧ decodeScalar (bs.drop OA)
        = some (Nat.fromBytesBE dataA, encode (.bytes dataB) ++ (encode (.bytes dataC) ++ tail))
    ∧ decodeScalar (bs.drop (OA + (encode (.bytes dataA)).length))
        = some (Nat.fromBytesBE dataB, encode (.bytes dataC) ++ tail)
    ∧ decode (bs.drop ((OA + (encode (.bytes dataA)).length) + (encode (.bytes dataB)).length))
        = some (.bytes dataC, tail) := by
  -- Right-associate the buffer split, one drop boundary per field.
  have hdropA : bs.drop OA =
      encode (.bytes dataA) ++ (encode (.bytes dataB) ++ (encode (.bytes dataC) ++ tail)) := by
    rw [hdrop]; simp only [List.append_assoc]
  have hdropB : bs.drop (OA + (encode (.bytes dataA)).length) =
      encode (.bytes dataB) ++ (encode (.bytes dataC) ++ tail) := by
    rw [← List.drop_drop, hdropA, List.drop_append_length]
  have hdropC : bs.drop ((OA + (encode (.bytes dataA)).length) + (encode (.bytes dataB)).length) =
      encode (.bytes dataC) ++ tail := by
    rw [← List.drop_drop, hdropB, List.drop_append_length]
  -- Field A: scalar into region (concrete scratch pre).
  obtain ⟨tA, hpureA⟩ := unified_scalar_field_decode_and_store_region base regionBase rOut outBase
    offA bs OA dataA (encode (.bytes dataB) ++ (encode (.bytes dataC) ++ tail)) outBytes diA
    v5Old v10 v11Old v12Old v14Old v15Old hlenA1 hlenA8 halign hover hwin hdropA hdalign hdstA
    hdov hdval hImmA (by omega)
  rw [show base + 180 + 4 + BitVec.ofNat 64 (12 * 8) = base + 280 from by bv_omega] at tA
  -- Field B: scalar into region (regOwn scratch pre).
  obtain ⟨tB, hpureB⟩ := unified_scalar_field_decode_and_store_region_at_regOwn (base + 280)
    regionBase rOut outBase offB bs (OA + (encode (.bytes dataA)).length) dataB
    (encode (.bytes dataC) ++ tail)
    (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE dataA)) diA 8) diB
    (outBase + BitVec.ofNat 64 (diA + 8)) v15Old hlenB1 hlenB8 halign hover hwin hdropB hdalign
    (by rw [spillRange_length]; exact hdstB) (by rw [spillRange_length]; exact hdov)
    (by intro i hi; rw [spillRange_length] at hi; exact hdval i hi) hImmB
    (by have h280 : (base + 280).toNat = base.toNat + 280 := by bv_omega
        omega)
  rw [show base + 280 + 180 + 4 + BitVec.ofNat 64 (12 * 8) = base + 560 from by bv_omega] at tB
  -- Field C: byte-array copy into region (regOwn scratch pre).
  obtain ⟨tC, hpureC⟩ := unified_bytes_field_decode_and_copy_at_regOwn (base + 560) regionBase rOut
    outBase offC bs ((OA + (encode (.bytes dataA)).length) + (encode (.bytes dataB)).length) dataC
    tail
    (spillRange (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE dataA)) diA 8)
      (BitVec.ofNat 64 (Nat.fromBytesBE dataB)) diB 8) diC
    (outBase + BitVec.ofNat 64 (diB + 8)) v15Old hlenC1 hlenC55 hsizeC halign hdalign hover hwin
    hImmC (by rw [spillRange_length, spillRange_length]; exact hdstC)
    (by rw [spillRange_length, spillRange_length]; exact hdov)
    (by intro i hi; rw [spillRange_length, spillRange_length] at hi; exact hdval i hi)
    (by have h560 : (base + 560).toNat = base.toNat + 560 := by bv_omega
        omega) hdropC
  rw [show base + 560 + 148 + 4 + BitVec.ofNat 64 (20 * dataC.length)
      = base + 712 + BitVec.ofNat 64 (20 * dataC.length) from by bv_omega] at tC
  -- Disjointness, by code range (each unit occupies a contiguous interval).
  have hd_AB : (scalarRegionUnitCR base rOut offA).Disjoint
      (scalarRegionUnitCR (base + 280) rOut offB) :=
    codeReq_disjoint_of_ranges _ _ (base.toNat + 280)
      (fun a ha => scalar_region_unit_cr_none_above base rOut offA a (by bv_omega) (by bv_omega))
      (fun a ha => scalar_region_unit_cr_none_below (base + 280) rOut offB a (by bv_omega)
        (by bv_omega))
  have hd_ABC : ((scalarRegionUnitCR base rOut offA).union
      (scalarRegionUnitCR (base + 280) rOut offB)).Disjoint
      (bytesUnitCR (base + 560) rOut offC dataC.length) :=
    codeReq_disjoint_of_ranges _ _ (base.toNat + 560)
      (fun a ha => by
        have hA := scalar_region_unit_cr_none_above base rOut offA a (by bv_omega) (by bv_omega)
        have hB := scalar_region_unit_cr_none_above (base + 280) rOut offB a (by bv_omega)
          (by bv_omega)
        simp only [CodeReq.union, hA, hB])
      (fun a ha => bytes_unit_cr_none_below (base + 560) rOut offC dataC.length a (by bv_omega)
        (by bv_omega))
  -- Compose (A ⨾ B) ⨾ C, reconciling each framed intermediate state by permutation.
  have AB := cpsTripleWithin_seq hd_AB
    (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) tA) tB
  refine ⟨?_, hpureA, hpureB, hpureC⟩
  exact cpsTripleWithin_seq hd_ABC
    (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) AB) tC

end EvmAsm.Rv64.RLP
