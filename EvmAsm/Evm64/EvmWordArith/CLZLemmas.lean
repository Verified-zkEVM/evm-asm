/-
  EvmAsm.Evm64.EvmWordArith.CLZLemmas

  Correctness lemmas for the CLZ (Count Leading Zeros) binary search.
  Connects the clzResult function to mathematical properties needed
  for the division algorithm:
  - shift=0 implies MSB is set (val ≥ 2^63)

  Proof strategy: algebraic, using a generic "clzStep" abstraction.
  Each CLZ stage is an instance of clzStep. We prove:
  1. clzStep_fst_bound: stage count grows by at most m (no overflow)
  2. clzStep_fst_zero: if output count = 0, input count = 0 and stage passed
  3. clzStep_snd_of_pass: when stage passes, value is preserved
  Then chain these through the 6 stages.
-/

import EvmAsm.Evm64.DivMod.Compose.CLZ
import EvmAsm.Evm64.EvmWordArith.DivN4Lemmas

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Generic CLZ stage abstraction
-- ============================================================================

/-- A single CLZ binary-search stage. Checks if val>>>K ≠ 0:
    if so, keeps (count, val); otherwise, adds m to count and shifts val left. -/
def clzStep (K M_s : Nat) (m : Word) (p : Word × Word) : Word × Word :=
  (if p.2 >>> K ≠ 0 then p.1 else p.1 + m,
   if p.2 >>> K ≠ 0 then p.2 else p.2 <<< M_s)

/-- Stage count bound: if input count ≤ B and B + m < 2^64,
    then output count ≤ B + m. -/
theorem clzStep_fst_bound {K M_s : Nat} {m : Word} {p : Word × Word} {B : Nat}
    (hc : p.1.toNat ≤ B) (hno : B + m.toNat < 2^64) :
    (clzStep K M_s m p).1.toNat ≤ B + m.toNat := by
  unfold clzStep; dsimp only []
  split
  · omega
  · rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : p.1.toNat + m.toNat < 2^64)]
    omega

/-- Stage pass detection: if output count = 0, then input count = 0
    and the shift condition held (stage "passed"). -/
theorem clzStep_fst_zero {K M_s : Nat} {m : Word} {p : Word × Word}
    (hm : m.toNat ≥ 1) (hno : p.1.toNat + m.toNat < 2^64)
    (h : (clzStep K M_s m p).1 = 0) :
    p.1 = 0 ∧ p.2 >>> K ≠ 0 := by
  unfold clzStep at h; dsimp only [] at h
  split at h
  · exact ⟨h, by assumption⟩
  · exfalso
    have h0 : (p.1 + m).toNat = 0 := by rw [h]; rfl
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hno] at h0; omega

/-- Value preservation: when a stage passes, the output value equals the input. -/
theorem clzStep_snd_of_pass {K M_s : Nat} {m : Word} {p : Word × Word}
    (hpass : p.2 >>> K ≠ 0) :
    (clzStep K M_s m p).2 = p.2 := by
  unfold clzStep; dsimp only []; exact if_pos hpass

-- ============================================================================
-- signExtend12 concrete toNat values
-- ============================================================================

private theorem se_1  : (signExtend12 (1  : BitVec 12)).toNat = 1  := by decide
private theorem se_2  : (signExtend12 (2  : BitVec 12)).toNat = 2  := by decide
private theorem se_4  : (signExtend12 (4  : BitVec 12)).toNat = 4  := by decide
private theorem se_8  : (signExtend12 (8  : BitVec 12)).toNat = 8  := by decide
private theorem se_16 : (signExtend12 (16 : BitVec 12)).toNat = 16 := by decide
private theorem se_32 : (signExtend12 (32 : BitVec 12)).toNat = 32 := by decide

-- ============================================================================
-- CLZ pipeline: stages 0–4 (before the final stage 5)
-- ============================================================================

/-- The first 5 CLZ stages (0 through 4), producing an intermediate (count, value) pair.
    Stage 5 is handled separately since it only updates the count. -/
def clzPipeline (val : Word) : Word × Word :=
  let s0 := clzStep 32 32 (signExtend12 32) ((0 : Word), val)
  let s1 := clzStep 48 16 (signExtend12 16) s0
  let s2 := clzStep 56 8  (signExtend12  8) s1
  let s3 := clzStep 60 4  (signExtend12  4) s2
  clzStep 62 2 (signExtend12 2) s3

-- Intermediate stage references for bounds chain
private def clzS0 (val : Word) :=
  clzStep 32 32 (signExtend12 32) ((0 : Word), val)
private def clzS1 (val : Word) :=
  clzStep 48 16 (signExtend12 16) (clzS0 val)
private def clzS2 (val : Word) :=
  clzStep 56 8  (signExtend12  8) (clzS1 val)
private def clzS3 (val : Word) :=
  clzStep 60 4  (signExtend12  4) (clzS2 val)

private theorem clzPipeline_unfold (val : Word) :
    clzPipeline val = clzStep 62 2 (signExtend12 2) (clzS3 val) := by
  unfold clzPipeline clzS3 clzS2 clzS1 clzS0; rfl

-- ============================================================================
-- Bound chain: each intermediate count is bounded (algebraic, no case splits)
-- ============================================================================

private theorem clzS0_bound (val : Word) : (clzS0 val).1.toNat ≤ 32 := by
  have h0 : ((0 : Word), val).1.toNat ≤ 0 := by simp
  exact clzStep_fst_bound h0 (by have := se_32; omega)

private theorem clzS1_bound (val : Word) : (clzS1 val).1.toNat ≤ 48 := by
  exact clzStep_fst_bound (clzS0_bound val) (by have := se_16; omega)

private theorem clzS2_bound (val : Word) : (clzS2 val).1.toNat ≤ 56 := by
  exact clzStep_fst_bound (clzS1_bound val) (by have := se_8; omega)

private theorem clzS3_bound (val : Word) : (clzS3 val).1.toNat ≤ 60 := by
  exact clzStep_fst_bound (clzS2_bound val) (by have := se_4; omega)

/-- The pipeline count (stages 0–4) is at most 62. -/
theorem clzPipeline_fst_le (val : Word) : (clzPipeline val).1.toNat ≤ 62 := by
  rw [clzPipeline_unfold]
  exact clzStep_fst_bound (clzS3_bound val) (by have := se_2; omega)

-- ============================================================================
-- Overflow lemmas for backward pass (derived from bounds)
-- ============================================================================

private theorem clzS3_no_overflow (val : Word) :
    (clzS3 val).1.toNat + (signExtend12 (2 : BitVec 12)).toNat < 2^64 := by
  have := clzS3_bound val; have := se_2; omega

private theorem clzS2_no_overflow (val : Word) :
    (clzS2 val).1.toNat + (signExtend12 (4 : BitVec 12)).toNat < 2^64 := by
  have := clzS2_bound val; have := se_4; omega

private theorem clzS1_no_overflow (val : Word) :
    (clzS1 val).1.toNat + (signExtend12 (8 : BitVec 12)).toNat < 2^64 := by
  have := clzS1_bound val; have := se_8; omega

private theorem clzS0_no_overflow (val : Word) :
    (clzS0 val).1.toNat + (signExtend12 (16 : BitVec 12)).toNat < 2^64 := by
  have := clzS0_bound val; have := se_16; omega

private theorem clzInit_no_overflow (val : Word) :
    ((0 : Word), val).1.toNat + (signExtend12 (32 : BitVec 12)).toNat < 2^64 := by
  have h1 : ((0 : Word), val).1.toNat = 0 := by simp
  have := se_32; omega

-- ============================================================================
-- Connection: clzResult = pipeline + stage 5
-- ============================================================================

theorem clzResult_fst_eq (val : Word) :
    (clzResult val).1 =
      if (clzPipeline val).2 >>> 63 ≠ 0
      then (clzPipeline val).1
      else (clzPipeline val).1 + signExtend12 1 := by
  unfold clzResult clzPipeline clzStep; rfl

theorem clzResult_snd_eq (val : Word) :
    (clzResult val).2 = (clzPipeline val).2 := by
  unfold clzResult clzPipeline clzStep; rfl

-- ============================================================================
-- Helper: ushiftRight 63 nonzero implies ≥ 2^63
-- ============================================================================

theorem toNat_ge_of_ushiftRight_63 {val : Word}
    (h : val >>> (63 : Nat) ≠ 0) : val.toNat ≥ 2^63 := by
  have hne : (val >>> (63 : Nat)).toNat ≠ 0 := by
    intro heq; exact h (BitVec.eq_of_toNat_eq (by simp [heq]))
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hne
  have := val.isLt; omega

-- ============================================================================
-- Backward pass: if pipeline count = 0, all stages passed and value = val
-- ============================================================================

/-- Helper: rewrite pipeline.2 = val when all stages passed. -/
private theorem pipeline_snd_chain {val : Word}
    (hval : ((0 : Word), val).2 >>> 32 ≠ 0)
    (hv0 : (clzS0 val).2 >>> 48 ≠ 0)
    (hv1 : (clzS1 val).2 >>> 56 ≠ 0)
    (hv2 : (clzS2 val).2 >>> 60 ≠ 0)
    (hv3 : (clzS3 val).2 >>> 62 ≠ 0) :
    (clzPipeline val).2 = val := by
  rw [clzPipeline_unfold, clzStep_snd_of_pass hv3]
  unfold clzS3; rw [clzStep_snd_of_pass hv2]
  unfold clzS2; rw [clzStep_snd_of_pass hv1]
  unfold clzS1; rw [clzStep_snd_of_pass hv0]
  unfold clzS0; rw [clzStep_snd_of_pass hval]

/-- If the pipeline count is 0, all 5 stages passed and the pipeline value = val. -/
private theorem clzPipeline_zero (val : Word) (h : (clzPipeline val).1 = 0) :
    (clzPipeline val).2 = val := by
  rw [clzPipeline_unfold] at h
  have ⟨hc3, hv3⟩ := clzStep_fst_zero (by have := se_2; omega) (clzS3_no_overflow val) h
  have ⟨hc2, hv2⟩ := clzStep_fst_zero (by have := se_4; omega) (clzS2_no_overflow val) hc3
  have ⟨hc1, hv1⟩ := clzStep_fst_zero (by have := se_8; omega) (clzS1_no_overflow val) hc2
  have ⟨hc0, hv0⟩ := clzStep_fst_zero (by have := se_16; omega) (clzS0_no_overflow val) hc1
  have ⟨_, hval⟩ := clzStep_fst_zero (by have := se_32; omega) (clzInit_no_overflow val) hc0
  exact pipeline_snd_chain hval hv0 hv1 hv2 hv3

-- ============================================================================
-- Main theorem: CLZ shift=0 implies MSB is set
-- ============================================================================

/-- When CLZ reports shift=0, the input value has its MSB set (val ≥ 2^63).
    This connects the shift=0 path condition in the division algorithm
    to the mathematical normalization condition needed for quotient bounds. -/
theorem clz_zero_imp_msb (val : Word) (h : (clzResult val).1 = 0) :
    val.toNat ≥ 2^63 := by
  rw [clzResult_fst_eq] at h
  have hbnd := clzPipeline_fst_le val
  split at h
  · -- Stage 5 passed: pipeline count = 0
    rename_i h5_pass
    have hsnd := clzPipeline_zero val h
    rw [hsnd] at h5_pass
    exact toNat_ge_of_ushiftRight_63 h5_pass
  · -- Stage 5 failed: pipeline.1 + 1 = 0, contradicts bound ≤ 62
    exfalso
    have h0 : ((clzPipeline val).1 + signExtend12 1).toNat = 0 := by rw [h]; rfl
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := se_1; omega)] at h0
    have := se_1; omega

-- ============================================================================
-- CLZ shift=0 implies value unchanged
-- ============================================================================

/-- When CLZ reports shift=0, the shifted value equals the original. -/
theorem clz_zero_imp_snd (val : Word) (h : (clzResult val).1 = 0) :
    (clzResult val).2 = val := by
  rw [clzResult_fst_eq] at h
  have hbnd := clzPipeline_fst_le val
  split at h
  · rw [clzResult_snd_eq]; exact clzPipeline_zero val h
  · exfalso
    have h0 : ((clzPipeline val).1 + signExtend12 1).toNat = 0 := by rw [h]; rfl
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := se_1; omega)] at h0
    have := se_1; omega

-- ============================================================================
-- CLZ count bound
-- ============================================================================

/-- The CLZ count is always at most 63. -/
theorem clzResult_fst_toNat_le (val : Word) :
    (clzResult val).1.toNat ≤ 63 := by
  rw [clzResult_fst_eq]
  have hbnd := clzPipeline_fst_le val
  split
  · omega
  · rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := se_1; omega)]
    have := se_1; omega

end EvmAsm.Evm64
