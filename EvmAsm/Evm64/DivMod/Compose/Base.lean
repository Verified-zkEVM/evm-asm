/-
  EvmAsm.Evm64.DivMod.Compose.Base

  Shared infrastructure for DivMod composition: divCode/modCode definitions,
  program length lemmas, and the skipBlock tactic macro.
-/

import EvmAsm.Evm64.DivMod.LimbSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Program length lemmas (via native_decide)
-- Non-private so they are accessible from sub-files via skipBlock macro.
-- ============================================================================

theorem divK_phaseA_len : (divK_phaseA 1016).length = 8 := by native_decide
theorem divK_phaseB_len : divK_phaseB.length = 21 := by native_decide
theorem divK_clz_len : divK_clz.length = 24 := by native_decide
theorem divK_phaseC2_len : (divK_phaseC2 172).length = 4 := by native_decide
theorem divK_normB_len : divK_normB.length = 21 := by native_decide
theorem divK_normA_len : (divK_normA 40).length = 21 := by native_decide
theorem divK_copyAU_len : divK_copyAU.length = 9 := by native_decide
theorem divK_loopSetup_len : (divK_loopSetup 460).length = 4 := by native_decide
theorem divK_loopBody_len : (divK_loopBody 556 7740).length = 114 := by native_decide
theorem divK_denorm_len : divK_denorm.length = 25 := by native_decide
theorem divK_divEpilogue_len : (divK_div_epilogue 24).length = 10 := by native_decide
theorem divK_zeroPath_len : divK_zeroPath.length = 5 := by native_decide
theorem divK_nop_len : (ADDI .x0 .x0 0 : Program).length = 1 := by native_decide
theorem divK_div128_len : divK_div128.length = 49 := by native_decide
theorem divK_modEpilogue_len : (divK_mod_epilogue 24).length = 10 := by native_decide

/-- Skip one ofProg block in a right-nested union via range disjointness.
    Closes the disjointness goal using block length lemmas + bv_omega. -/
macro "skipBlock" : tactic =>
  `(tactic| apply CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range _ _ _ _ (fun k1 k2 hk1 hk2 => by
        simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
          divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
          divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len,
          divK_zeroPath_len, divK_nop_len, divK_div128_len,
          divK_modEpilogue_len] at hk1 hk2
        bv_omega)))

-- ============================================================================
-- Full program CodeReq definitions
-- ============================================================================

/-- The full evm_div code split into 14 per-phase CodeReq.ofProg blocks.
    This is the canonical CodeReq for all composed specs. -/
abbrev divCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base (divK_phaseA 1016),             -- block 0
    CodeReq.ofProg (base + 32) divK_phaseB,              -- block 1
    CodeReq.ofProg (base + 116) divK_clz,                -- block 2
    CodeReq.ofProg (base + 212) (divK_phaseC2 172),      -- block 3
    CodeReq.ofProg (base + 228) divK_normB,              -- block 4
    CodeReq.ofProg (base + 312) (divK_normA 40),         -- block 5
    CodeReq.ofProg (base + 396) divK_copyAU,             -- block 6
    CodeReq.ofProg (base + 432) (divK_loopSetup 460),    -- block 7
    CodeReq.ofProg (base + 448) (divK_loopBody 556 7740),-- block 8
    CodeReq.ofProg (base + 904) divK_denorm,             -- block 9
    CodeReq.ofProg (base + 1004) (divK_div_epilogue 24), -- block 10
    CodeReq.ofProg (base + 1044) divK_zeroPath,          -- block 11
    CodeReq.ofProg (base + 1064) (ADDI .x0 .x0 0),      -- block 12
    CodeReq.ofProg (base + 1068) divK_div128             -- block 13
  ]

/-- The full evm_mod code split into 14 per-phase CodeReq.ofProg blocks.
    Identical to divCode except block 10 uses divK_mod_epilogue. -/
abbrev modCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base (divK_phaseA 1016),
    CodeReq.ofProg (base + 32) divK_phaseB,
    CodeReq.ofProg (base + 116) divK_clz,
    CodeReq.ofProg (base + 212) (divK_phaseC2 172),
    CodeReq.ofProg (base + 228) divK_normB,
    CodeReq.ofProg (base + 312) (divK_normA 40),
    CodeReq.ofProg (base + 396) divK_copyAU,
    CodeReq.ofProg (base + 432) (divK_loopSetup 460),
    CodeReq.ofProg (base + 448) (divK_loopBody 556 7740),
    CodeReq.ofProg (base + 904) divK_denorm,
    CodeReq.ofProg (base + 1004) (divK_mod_epilogue 24),  -- block 10 differs from divCode
    CodeReq.ofProg (base + 1044) divK_zeroPath,
    CodeReq.ofProg (base + 1064) (ADDI .x0 .x0 0),
    CodeReq.ofProg (base + 1068) divK_div128
  ]

-- ============================================================================
-- Shared code: blocks common to divCode and modCode (all except epilogue)
-- ============================================================================

/-- Shared code blocks between divCode and modCode (everything except block 10, the epilogue).
    Used as the code requirement for loop body and div128 specs, which are identical
    for DIV and MOD. -/
abbrev sharedDivModCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base (divK_phaseA 1016),             -- block 0
    CodeReq.ofProg (base + 32) divK_phaseB,              -- block 1
    CodeReq.ofProg (base + 116) divK_clz,                -- block 2
    CodeReq.ofProg (base + 212) (divK_phaseC2 172),      -- block 3
    CodeReq.ofProg (base + 228) divK_normB,              -- block 4
    CodeReq.ofProg (base + 312) (divK_normA 40),         -- block 5
    CodeReq.ofProg (base + 396) divK_copyAU,             -- block 6
    CodeReq.ofProg (base + 432) (divK_loopSetup 460),    -- block 7
    CodeReq.ofProg (base + 448) (divK_loopBody 556 7740),-- block 8
    CodeReq.ofProg (base + 904) divK_denorm,             -- block 9
    -- NO epilogue block (this is where divCode and modCode differ)
    CodeReq.ofProg (base + 1044) divK_zeroPath,          -- block 10 (was 11)
    CodeReq.ofProg (base + 1064) (ADDI .x0 .x0 0),      -- block 11 (was 12)
    CodeReq.ofProg (base + 1068) divK_div128             -- block 12 (was 13)
  ]

-- Per-block subsumption: each shared block ⊆ divCode.
-- Blocks 0-9 are at the same union positions; blocks 10-12 (shared) = blocks 11-13 (divCode).
private theorem shared_b0_div (b : Word) : ∀ a i, (CodeReq.ofProg b (divK_phaseA 1016)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left _ _
private theorem shared_b1_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 32) divK_phaseB) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b2_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 116) divK_clz) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b3_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 212) (divK_phaseC2 172)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b4_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 228) divK_normB) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b5_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 312) (divK_normA 40)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b6_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 396) divK_copyAU) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b7_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 432) (divK_loopSetup 460)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b8_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 448) (divK_loopBody 556 7740)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b9_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 904) divK_denorm) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b10_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 1044) divK_zeroPath) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b11_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 1064) (ADDI .x0 .x0 0 : Program)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b12_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + 1068) divK_div128) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _

/-- sharedDivModCode ⊆ divCode: every shared block is also in divCode. -/
theorem sharedDivModCode_sub_divCode (base : Word) :
    ∀ a i, (sharedDivModCode base) a = some i → (divCode base) a = some i := by
  unfold sharedDivModCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono (shared_b0_div base)
    (CodeReq.union_split_mono (shared_b1_div base)
    (CodeReq.union_split_mono (shared_b2_div base)
    (CodeReq.union_split_mono (shared_b3_div base)
    (CodeReq.union_split_mono (shared_b4_div base)
    (CodeReq.union_split_mono (shared_b5_div base)
    (CodeReq.union_split_mono (shared_b6_div base)
    (CodeReq.union_split_mono (shared_b7_div base)
    (CodeReq.union_split_mono (shared_b8_div base)
    (CodeReq.union_split_mono (shared_b9_div base)
    (CodeReq.union_split_mono (shared_b10_div base)
    (CodeReq.union_split_mono (shared_b11_div base)
    (CodeReq.union_split_mono (shared_b12_div base)
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

-- Per-block subsumption: each shared block ⊆ modCode.
private theorem shared_b0_mod (b : Word) : ∀ a i, (CodeReq.ofProg b (divK_phaseA 1016)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left _ _
private theorem shared_b1_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 32) divK_phaseB) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b2_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 116) divK_clz) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b3_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 212) (divK_phaseC2 172)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b4_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 228) divK_normB) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b5_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 312) (divK_normA 40)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b6_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 396) divK_copyAU) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b7_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 432) (divK_loopSetup 460)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b8_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 448) (divK_loopBody 556 7740)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b9_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 904) divK_denorm) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b10_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 1044) divK_zeroPath) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b11_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 1064) (ADDI .x0 .x0 0 : Program)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b12_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + 1068) divK_div128) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
/-- sharedDivModCode ⊆ modCode: every shared block is also in modCode. -/
theorem sharedDivModCode_sub_modCode (base : Word) :
    ∀ a i, (sharedDivModCode base) a = some i → (modCode base) a = some i := by
  unfold sharedDivModCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono (shared_b0_mod base)
    (CodeReq.union_split_mono (shared_b1_mod base)
    (CodeReq.union_split_mono (shared_b2_mod base)
    (CodeReq.union_split_mono (shared_b3_mod base)
    (CodeReq.union_split_mono (shared_b4_mod base)
    (CodeReq.union_split_mono (shared_b5_mod base)
    (CodeReq.union_split_mono (shared_b6_mod base)
    (CodeReq.union_split_mono (shared_b7_mod base)
    (CodeReq.union_split_mono (shared_b8_mod base)
    (CodeReq.union_split_mono (shared_b9_mod base)
    (CodeReq.union_split_mono (shared_b10_mod base)
    (CodeReq.union_split_mono (shared_b11_mod base)
    (CodeReq.union_split_mono (shared_b12_mod base)
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

end EvmAsm.Rv64
