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

/-- General form: `val >>> K = 0` iff `val.toNat < 2^K`. -/
theorem ushiftRight_eq_zero_iff {val : Word} (K : Nat) :
    val >>> K = 0 ↔ val.toNat < 2 ^ K := by
  constructor
  · intro hz
    have h0 : (val >>> K).toNat = 0 := by rw [hz]; rfl
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h0
    rcases (Nat.div_eq_zero_iff).mp h0 with hc | hc
    · exact absurd hc (by positivity)
    · exact hc
  · intro hlt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp [Nat.div_eq_zero_iff, hlt]

/-- Contrapositive form: `val >>> K ≠ 0` iff `val.toNat ≥ 2^K`. -/
theorem ushiftRight_ne_zero_iff {val : Word} (K : Nat) :
    val >>> K ≠ 0 ↔ val.toNat ≥ 2 ^ K := by
  rw [ne_eq, ushiftRight_eq_zero_iff K]; omega

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

-- ============================================================================
-- Converse: MSB set implies CLZ shift=0
-- ============================================================================

/-- If val >>> K ≠ 0 for a larger K, then val >>> K' ≠ 0 for K' ≤ K.
    (Higher-order bits set implies lower-order bits nonzero.) -/
theorem ushiftRight_ne_zero_of_msb {val : Word} {K : Nat} (hK : K ≤ 63)
    (hmsb : val >>> (63 : Nat) ≠ 0) : val >>> K ≠ 0 := by
  intro h; apply hmsb; apply BitVec.eq_of_toNat_eq
  show (val >>> (63 : Nat)).toNat = (0 : Word).toNat
  have h0 : (val >>> K).toNat = 0 := by rw [h]; rfl
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h0 ⊢; simp
  have hlt : val.toNat < 2^K := by
    rcases (Nat.div_eq_zero_iff).mp h0 with h | h
    · exact absurd h (by positivity)
    · exact h
  have : 2^K ≤ (2 : Nat)^63 := Nat.pow_le_pow_right (by omega) hK; omega

/-- When a clzStep's shift condition holds, the step is the identity. -/
private theorem clzStep_of_pass {K M_s : Nat} {m : Word} {p : Word × Word}
    (hpass : p.2 >>> K ≠ 0) :
    clzStep K M_s m p = p := by
  unfold clzStep; exact Prod.ext (if_pos hpass) (if_pos hpass)

/-- When MSB is set, the entire pipeline is the identity (all stages pass). -/
private theorem clzPipeline_of_msb (val : Word) (hmsb : val >>> (63 : Nat) ≠ 0) :
    clzPipeline val = ((0 : Word), val) := by
  have h32 := ushiftRight_ne_zero_of_msb (K := 32) (by omega) hmsb
  have h48 := ushiftRight_ne_zero_of_msb (K := 48) (by omega) hmsb
  have h56 := ushiftRight_ne_zero_of_msb (K := 56) (by omega) hmsb
  have h60 := ushiftRight_ne_zero_of_msb (K := 60) (by omega) hmsb
  have h62 := ushiftRight_ne_zero_of_msb (K := 62) (by omega) hmsb
  -- Each stage is identity: unfold and rewrite step by step
  unfold clzPipeline; dsimp only []
  rw [show clzStep 32 32 (signExtend12 32) ((0 : Word), val) = ((0 : Word), val)
    from clzStep_of_pass h32]
  rw [show clzStep 48 16 (signExtend12 16) ((0 : Word), val) = ((0 : Word), val)
    from clzStep_of_pass h48]
  rw [show clzStep 56 8 (signExtend12 8) ((0 : Word), val) = ((0 : Word), val)
    from clzStep_of_pass h56]
  rw [show clzStep 60 4 (signExtend12 4) ((0 : Word), val) = ((0 : Word), val)
    from clzStep_of_pass h60]
  exact clzStep_of_pass h62

/-- When the MSB is set (val ≥ 2^63), CLZ reports shift=0. -/
theorem msb_imp_clz_zero (val : Word) (hmsb : val >>> (63 : Nat) ≠ 0) :
    (clzResult val).1 = 0 := by
  rw [clzResult_fst_eq, clzPipeline_of_msb val hmsb]; exact if_pos hmsb

-- ============================================================================
-- Biconditional characterization
-- ============================================================================

/-- CLZ shift=0 iff the MSB is set: `(clzResult val).1 = 0 ↔ val >>> 63 ≠ 0`. -/
theorem clzResult_fst_eq_zero_iff (val : Word) :
    (clzResult val).1 = 0 ↔ val >>> (63 : Nat) ≠ 0 := by
  constructor
  · intro h
    have hge := clz_zero_imp_msb val h
    intro heq
    have : (val >>> (63 : Nat)).toNat = 0 := by rw [heq]; rfl
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
    have := val.isLt; omega
  · exact msb_imp_clz_zero val

-- ============================================================================
-- Pipeline invariant: val * 2^count = value.toNat (no overflow at each stage)
-- ============================================================================

/-- Generic clzStep invariant: if `K + M_s = 64`, `m.toNat = M_s`, and the
    input count's Nat is small enough to avoid wraparound, then the shift
    relation `val * 2^count = value.toNat` is preserved. -/
theorem clzStep_invariant_pres (K M_s : Nat) (m : Word) (val : Word) (p : Word × Word)
    (hinv : val.toNat * 2^p.1.toNat = p.2.toNat)
    (hKMs : K + M_s = 64)
    (hm_toNat : m.toNat = M_s)
    (hp_count_bound : p.1.toNat + M_s < 2^64) :
    val.toNat * 2^(clzStep K M_s m p).1.toNat = (clzStep K M_s m p).2.toNat := by
  unfold clzStep
  split
  · -- pass case: count and value unchanged
    exact hinv
  · rename_i hfail
    push Not at hfail
    -- fail case: p.2 >>> K = 0, i.e., p.2.toNat < 2^K
    have hp2_lt : p.2.toNat < 2^K := (ushiftRight_eq_zero_iff K).mp hfail
    -- (p.2 <<< M_s).toNat = p.2.toNat * 2^M_s (no wrap since K + M_s = 64)
    have hp2_shifted : (p.2 <<< M_s).toNat = p.2.toNat * 2^M_s := by
      rw [BitVec.toNat_shiftLeft]
      simp only [Nat.shiftLeft_eq]
      have : p.2.toNat * 2^M_s < 2^64 := by
        have hpos : 0 < (2 : Nat) ^ M_s := by positivity
        have : p.2.toNat * 2^M_s < 2^K * 2^M_s :=
          Nat.mul_lt_mul_right hpos |>.mpr hp2_lt
        rw [← pow_add, hKMs] at this; exact this
      exact Nat.mod_eq_of_lt this
    -- (p.1 + m).toNat = p.1.toNat + M_s (no wrap by hp_count_bound + hm_toNat)
    have hp1_sum : (p.1 + m).toNat = p.1.toNat + M_s := by
      rw [BitVec.toNat_add, hm_toNat]
      exact Nat.mod_eq_of_lt hp_count_bound
    -- Now prove: val * 2^(p.1 + m).toNat = (p.2 <<< M_s).toNat
    show val.toNat * 2^(p.1 + m).toNat = (p.2 <<< M_s).toNat
    rw [hp2_shifted, hp1_sum, pow_add, ← Nat.mul_assoc, hinv]

/-- Specialized: clzStep preserves the invariant AND the count is bounded
    (for M_s ≤ 32, ensuring no overflow in any CLZ stage). -/
theorem clzStep_invariant_and_bound (K M_s : Nat) (m : Word) (val : Word)
    (p : Word × Word) (B_in B_out : Nat)
    (hinv : val.toNat * 2^p.1.toNat = p.2.toNat)
    (hcount : p.1.toNat ≤ B_in)
    (hKMs : K + M_s = 64)
    (hm_toNat : m.toNat = M_s)
    (hBout : B_in + M_s = B_out)
    (hB_lt : B_out < 2^64) :
    val.toNat * 2^(clzStep K M_s m p).1.toNat = (clzStep K M_s m p).2.toNat ∧
    (clzStep K M_s m p).1.toNat ≤ B_out := by
  refine ⟨?_, ?_⟩
  · apply clzStep_invariant_pres K M_s m val p hinv hKMs hm_toNat
    omega
  · -- Count bound
    unfold clzStep
    split
    · show p.1.toNat ≤ B_out; omega
    · show (p.1 + m).toNat ≤ B_out
      rw [BitVec.toNat_add, hm_toNat, Nat.mod_eq_of_lt (by omega : p.1.toNat + M_s < 2^64)]
      omega

/-- Full pipeline invariant: after all 5 pipeline stages, the invariant
    `val * 2^count = value` holds, and count is bounded by 62. -/
theorem clzPipeline_invariant (val : Word) :
    val.toNat * 2^(clzPipeline val).1.toNat = (clzPipeline val).2.toNat ∧
    (clzPipeline val).1.toNat ≤ 62 := by
  rw [clzPipeline_unfold]
  -- Initial invariant: val * 2^0 = val
  have h0 : val.toNat * 2^((0 : Word), val).1.toNat = ((0 : Word), val).2.toNat := by
    simp
  have hb0 : ((0 : Word), val).1.toNat ≤ 0 := by simp
  -- Stage 0: K=32, M_s=32, m=signExtend12 32. Invariant + bound ≤ 32.
  have h1 := clzStep_invariant_and_bound 32 32 (signExtend12 32) val _ 0 32
    h0 hb0 (by norm_num) se_32 (by norm_num) (by norm_num)
  -- Stage 1: K=48, M_s=16, m=signExtend12 16. Invariant + bound ≤ 48.
  have h2 := clzStep_invariant_and_bound 48 16 (signExtend12 16) val _ 32 48
    h1.1 h1.2 (by norm_num) se_16 (by norm_num) (by norm_num)
  -- Stage 2: K=56, M_s=8.
  have h3 := clzStep_invariant_and_bound 56 8 (signExtend12 8) val _ 48 56
    h2.1 h2.2 (by norm_num) se_8 (by norm_num) (by norm_num)
  -- Stage 3: K=60, M_s=4.
  have h4 := clzStep_invariant_and_bound 60 4 (signExtend12 4) val _ 56 60
    h3.1 h3.2 (by norm_num) se_4 (by norm_num) (by norm_num)
  -- Stage 4 (final pipeline stage): K=62, M_s=2.
  have h5 := clzStep_invariant_and_bound 62 2 (signExtend12 2) val _ 60 62
    h4.1 h4.2 (by norm_num) se_2 (by norm_num) (by norm_num)
  exact h5

/-- CLZ top-limb bound: when `val ≠ 0`, `val.toNat < 2^(64 - clz)`. This is
    the main consumer-facing bound that the MOD stack spec's `hb3_bound`
    hypothesis needs. -/
theorem clzResult_fst_top_bound (val : Word) :
    val.toNat < 2 ^ (64 - (clzResult val).1.toNat) := by
  obtain ⟨hinv, hcount⟩ := clzPipeline_invariant val
  -- Value is a Word, so bounded by 2^64.
  have hval_lt : (clzPipeline val).2.toNat < 2^64 := (clzPipeline val).2.isLt
  rw [clzResult_fst_eq]
  by_cases h5 : (clzPipeline val).2 >>> 63 ≠ 0
  · -- Stage 5 passed: clzResult.1 = pipeline.1.
    rw [if_pos h5]
    -- From invariant: val * 2^count = value < 2^64, so val < 2^(64-count).
    have : val.toNat * 2^(clzPipeline val).1.toNat < 2^64 := by
      rw [hinv]; exact hval_lt
    have hpos : 0 < 2^(clzPipeline val).1.toNat := Nat.pos_of_ne_zero (by positivity)
    have hpow_eq : (2 : Nat)^64 = 2^(64 - (clzPipeline val).1.toNat) *
        2^(clzPipeline val).1.toNat := by
      rw [← pow_add, show 64 - (clzPipeline val).1.toNat + (clzPipeline val).1.toNat =
          64 from by omega]
    rw [hpow_eq] at this
    exact Nat.lt_of_mul_lt_mul_right this
  · -- Stage 5 failed: clzResult.1 = pipeline.1 + 1.
    simp only [h5, if_false]
    push Not at h5
    -- value < 2^63 (from h5: value >>> 63 = 0, applying ushiftRight_eq_zero_iff).
    have hval_lt_63 : (clzPipeline val).2.toNat < 2^63 :=
      (ushiftRight_eq_zero_iff 63).mp h5
    -- From invariant: val * 2^count = value < 2^63, so val < 2^(63-count).
    have : val.toNat * 2^(clzPipeline val).1.toNat < 2^63 := by
      rw [hinv]; exact hval_lt_63
    have hpos : 0 < 2^(clzPipeline val).1.toNat := Nat.pos_of_ne_zero (by positivity)
    -- Show clzPipeline.1.toNat + signExtend12 1 = pipeline.1.toNat + 1, toNat-wise.
    have hsum_toNat :
        ((clzPipeline val).1 + signExtend12 (1 : BitVec 12)).toNat =
        (clzPipeline val).1.toNat + 1 := by
      rw [BitVec.toNat_add, se_1]
      exact Nat.mod_eq_of_lt (by omega : (clzPipeline val).1.toNat + 1 < 2^64)
    rw [hsum_toNat]
    -- Target: val < 2^(64 - (count + 1)) = 2^(63 - count).
    -- We have: val * 2^count < 2^63 = 2^(63-count) * 2^count.
    have hpow_eq : (2 : Nat)^63 = 2^(63 - (clzPipeline val).1.toNat) *
        2^(clzPipeline val).1.toNat := by
      rw [← pow_add, show 63 - (clzPipeline val).1.toNat + (clzPipeline val).1.toNat =
          63 from by omega]
    rw [hpow_eq] at this
    have hlt : val.toNat < 2^(63 - (clzPipeline val).1.toNat) :=
      Nat.lt_of_mul_lt_mul_right this
    have hsub : 64 - ((clzPipeline val).1.toNat + 1) = 63 - (clzPipeline val).1.toNat := by
      omega
    rw [hsub]; exact hlt

end EvmAsm.Evm64
