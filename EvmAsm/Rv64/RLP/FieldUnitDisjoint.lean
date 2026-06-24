/-
  EvmAsm.Rv64.RLP.FieldUnitDisjoint

  EL.3 / Phase 5 — reusable code-range disjointness for field-decode units. Every
  multi-field walk must prove unit-A's code ⊥ unit-B's code. Each field unit occupies a
  CONTIGUOUS code range `[base, base + size)` (scalar-into-region = 280 bytes; byte-array =
  `152 + 20·|data|` bytes), so two units at non-overlapping ranges have disjoint CodeReqs.

  This file packages that once:
    * `codeReq_disjoint_of_ranges` — generic: `cr1` is `none` at/above a boundary `M` and
      `cr2` is `none` below `M` ⇒ `cr1 ⊥ cr2`;
    * `scalar_region_unit_cr_none_above` / `_below` — the scalar-into-region unit's CR is
      `none` outside `[base, base+280)`;
    * `bytes_unit_cr_none_above` / `_below` — the byte-array unit's CR is `none` outside
      `[base, base + (152 + 20·|data|))`.

  With these, any walk's disjointness collapses to one `codeReq_disjoint_of_ranges` call with
  the two units' range-`none` facts — no per-leaf product, scaling to the 9-field tx / ~19-field
  header decoders.
-/

import EvmAsm.Rv64.RLP.UnifiedScalarFieldRegion
import EvmAsm.Rv64.RLP.UnifiedBytesFieldDecode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- **Generic range-split disjointness.** If `cr1` misses every address at or above a
    boundary `M` and `cr2` misses every address below `M`, the two CodeReqs are disjoint. -/
theorem codeReq_disjoint_of_ranges (cr1 cr2 : CodeReq) (M : Nat)
    (h1 : ∀ a : Word, M ≤ a.toNat → cr1 a = none)
    (h2 : ∀ a : Word, a.toNat < M → cr2 a = none) :
    cr1.Disjoint cr2 := by
  intro a
  by_cases h : a.toNat < M
  · exact Or.inr (h2 a h)
  · exact Or.inl (h1 a (by omega))

-- ---------------------------------------------------------------------------
-- Scalar-into-region unit: CR is `none` outside `[base, base+280)`.
-- ---------------------------------------------------------------------------

/-- The scalar-into-region unit's CodeReq, named for the range-`none` lemmas below. -/
def scalarRegionUnitCR (base : Word) (rOut : Reg) (fieldImm : BitVec 12) : CodeReq :=
  ((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
      (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
      (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
          (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
          (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
    ((CodeReq.singleton (base + 180) (.ADDI .x14 rOut fieldImm)).union
      (spillChainCR (base + 180 + 4) 8)))

/-- The scalar-into-region unit misses every address at or above `base + 280`. -/
theorem scalar_region_unit_cr_none_above (base : Word) (rOut : Reg) (fieldImm : BitVec 12)
    (a : Word) (hcode : base.toNat + 280 < 2 ^ 64) (h : base.toNat + 280 ≤ a.toNat) :
    scalarRegionUnitCR base rOut fieldImm a = none := by
  have hl1 : CodeReq.singleton base (.LBU .x5 .x13 0) a = none := CodeReq.singleton_miss (by bv_omega)
  have hl2 : CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
    CodeReq.ofProg_none_range_len _ _ 36 a unified_decoder_prog_length (fun k hk => by bv_omega)
  have hl3 : CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have hl4 : CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have hl5 : CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)) a = none :=
    CodeReq.ofProg_none_range_len _ _ 6 a (by rfl) (fun k hk => by bv_omega)
  have hl6 : CodeReq.singleton (base + 180) (.ADDI .x14 rOut fieldImm) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have hl7 : spillChainCR (base + 180 + 4) 8 a = none :=
    spillChainCR_none _ a 8 (fun j hj => by bv_omega)
  simp only [scalarRegionUnitCR, CodeReq.union, hl1, hl2, hl3, hl4, hl5, hl6, hl7]

/-- The scalar-into-region unit misses every address below `base`. -/
theorem scalar_region_unit_cr_none_below (base : Word) (rOut : Reg) (fieldImm : BitVec 12)
    (a : Word) (hcode : base.toNat + 280 < 2 ^ 64) (h : a.toNat < base.toNat) :
    scalarRegionUnitCR base rOut fieldImm a = none := by
  have hl1 : CodeReq.singleton base (.LBU .x5 .x13 0) a = none := CodeReq.singleton_miss (by bv_omega)
  have hl2 : CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
    CodeReq.ofProg_none_range_len _ _ 36 a unified_decoder_prog_length (fun k hk => by bv_omega)
  have hl3 : CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have hl4 : CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have hl5 : CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)) a = none :=
    CodeReq.ofProg_none_range_len _ _ 6 a (by rfl) (fun k hk => by bv_omega)
  have hl6 : CodeReq.singleton (base + 180) (.ADDI .x14 rOut fieldImm) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have hl7 : spillChainCR (base + 180 + 4) 8 a = none :=
    spillChainCR_none _ a 8 (fun j hj => by bv_omega)
  simp only [scalarRegionUnitCR, CodeReq.union, hl1, hl2, hl3, hl4, hl5, hl6, hl7]

-- ---------------------------------------------------------------------------
-- Empty (n=0) scalar unit: CR is `none` outside `[base, base+248)`.
-- ---------------------------------------------------------------------------

/-- The empty (`n=0`) scalar-into-region unit's CodeReq: descend (`base .. base+148`) ⨾
    `ADDI x14, rOut, fieldImm` + 8-iteration spill chain (no read loop). -/
def emptyScalarUnitCR (base : Word) (rOut : Reg) (fieldImm : BitVec 12) : CodeReq :=
  ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
      (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
    ((CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm)).union
      (spillChainCR (base + 148 + 4) 8))

/-- The empty-scalar unit misses every address at or above `base + 248`. -/
theorem empty_scalar_unit_cr_none_above (base : Word) (rOut : Reg) (fieldImm : BitVec 12)
    (a : Word) (hcode : base.toNat + 248 < 2 ^ 64) (h : base.toNat + 248 ≤ a.toNat) :
    emptyScalarUnitCR base rOut fieldImm a = none := by
  have hl1 : CodeReq.singleton base (.LBU .x5 .x13 0) a = none := CodeReq.singleton_miss (by bv_omega)
  have hl2 : CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
    CodeReq.ofProg_none_range_len _ _ 36 a unified_decoder_prog_length (fun k hk => by bv_omega)
  have hl3 : CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have hl4 : spillChainCR (base + 148 + 4) 8 a = none :=
    spillChainCR_none _ a 8 (fun j hj => by bv_omega)
  simp only [emptyScalarUnitCR, CodeReq.union, hl1, hl2, hl3, hl4]

/-- The empty-scalar unit misses every address below `base`. -/
theorem empty_scalar_unit_cr_none_below (base : Word) (rOut : Reg) (fieldImm : BitVec 12)
    (a : Word) (hcode : base.toNat + 248 < 2 ^ 64) (h : a.toNat < base.toNat) :
    emptyScalarUnitCR base rOut fieldImm a = none := by
  have hl1 : CodeReq.singleton base (.LBU .x5 .x13 0) a = none := CodeReq.singleton_miss (by bv_omega)
  have hl2 : CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
    CodeReq.ofProg_none_range_len _ _ 36 a unified_decoder_prog_length (fun k hk => by bv_omega)
  have hl3 : CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have hl4 : spillChainCR (base + 148 + 4) 8 a = none :=
    spillChainCR_none _ a 8 (fun j hj => by bv_omega)
  simp only [emptyScalarUnitCR, CodeReq.union, hl1, hl2, hl3, hl4]

-- ---------------------------------------------------------------------------
-- Byte-array unit: CR is `none` outside `[base, base + (152 + 20·len))`.
-- ---------------------------------------------------------------------------

/-- The byte-array unit's CodeReq (parameterized by the payload length `len`). -/
def bytesUnitCR (base : Word) (rOut : Reg) (fieldImm : BitVec 12) (len : Nat) : CodeReq :=
  ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
      (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
    ((CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm)).union
      (byteCopyChainCR (base + 148 + 4) len))

/-- The byte-array unit misses every address at or above `base + (152 + 20·len)`. -/
theorem bytes_unit_cr_none_above (base : Word) (rOut : Reg) (fieldImm : BitVec 12) (len : Nat)
    (a : Word) (hcode : base.toNat + (152 + 20 * len) < 2 ^ 64)
    (h : base.toNat + (152 + 20 * len) ≤ a.toNat) :
    bytesUnitCR base rOut fieldImm len a = none := by
  have hm1 : CodeReq.singleton base (.LBU .x5 .x13 0) a = none := CodeReq.singleton_miss (by bv_omega)
  have hm2 : CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
    CodeReq.ofProg_none_range_len _ _ 36 a unified_decoder_prog_length (fun k hk => by bv_omega)
  have hm3 : CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have hm4 : byteCopyChainCR (base + 148 + 4) len a = none :=
    byteCopyChainCR_none _ a len (fun j hj => by bv_omega)
  simp only [bytesUnitCR, CodeReq.union, hm1, hm2, hm3, hm4]

/-- The byte-array unit misses every address below `base`. -/
theorem bytes_unit_cr_none_below (base : Word) (rOut : Reg) (fieldImm : BitVec 12) (len : Nat)
    (a : Word) (hcode : base.toNat + (152 + 20 * len) < 2 ^ 64) (h : a.toNat < base.toNat) :
    bytesUnitCR base rOut fieldImm len a = none := by
  have hm1 : CodeReq.singleton base (.LBU .x5 .x13 0) a = none := CodeReq.singleton_miss (by bv_omega)
  have hm2 : CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
    CodeReq.ofProg_none_range_len _ _ 36 a unified_decoder_prog_length (fun k hk => by bv_omega)
  have hm3 : CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have hm4 : byteCopyChainCR (base + 148 + 4) len a = none :=
    byteCopyChainCR_none _ a len (fun j hj => by bv_omega)
  simp only [bytesUnitCR, CodeReq.union, hm1, hm2, hm3, hm4]

end EvmAsm.Rv64.RLP
