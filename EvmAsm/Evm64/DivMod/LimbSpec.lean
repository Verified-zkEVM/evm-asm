-- file-size-exception: tracked by issue #312 (split per-limb / mulsub / addback / phase / branch / div128 into a LimbSpec/ subdirectory). Grandfathered pending split.
/-
  EvmAsm.Evm64.DivModSpec

  CPS specifications for the 256-bit EVM DIV and MOD programs (Knuth Algorithm D).
  Bottom-up decomposition starting from the simplest phases.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.LimbSpec.AddBack
import EvmAsm.Evm64.DivMod.LimbSpec.AddBackFinalLoopControl
import EvmAsm.Evm64.DivMod.LimbSpec.CLZ
import EvmAsm.Evm64.DivMod.LimbSpec.CopyAU
import EvmAsm.Evm64.DivMod.LimbSpec.Denorm
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Clamp
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Phase1
import EvmAsm.Evm64.DivMod.LimbSpec.Div128PhaseEnd
import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1
import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Tail
import EvmAsm.Evm64.DivMod.LimbSpec.Div128UnProdCheck
import EvmAsm.Evm64.DivMod.LimbSpec.Epilogue
import EvmAsm.Evm64.DivMod.LimbSpec.LoopSetup
import EvmAsm.Evm64.DivMod.LimbSpec.MulSub
import EvmAsm.Evm64.DivMod.LimbSpec.MulSubLimb
import EvmAsm.Evm64.DivMod.LimbSpec.MulSubSetup
import EvmAsm.Evm64.DivMod.LimbSpec.NormA
import EvmAsm.Evm64.DivMod.LimbSpec.NormB
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseA
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseBCascade
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseBInit
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseBTail
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseC2
import EvmAsm.Evm64.DivMod.LimbSpec.SubCarryStoreQj
import EvmAsm.Evm64.DivMod.LimbSpec.TrialStoreComposed
import EvmAsm.Evm64.DivMod.LimbSpec.TrialQuotient
import EvmAsm.Evm64.DivMod.LimbSpec.ZeroPath
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- Zero path spec (divK_zeroPath_{code,spec}) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.ZeroPath (sixth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Phase A specs (divK_phaseA_{code,body_spec,spec}) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.PhaseA (seventh chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Phase A specs (divK_phaseA_{code,body_spec,spec}) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.PhaseA (seventh chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Phase B init specs (divK_phaseB_init{1,2}_{code,spec}) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.PhaseBInit (eighth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Phase C4 / CopyAU spec (divK_copyAU_{code,spec}) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.CopyAU (fifth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- NormB per-limb specs (divK_normB_merge_*, divK_normB_last_*) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.NormB (second chunk of #312 split). Re-exported
-- via the import at the top of this file, so downstream surface is unchanged.

-- NormA per-limb specs (divK_normA_{top,mergeA,mergeB,last}_*) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.NormA (third chunk of #312 split). Re-exported
-- via the import at the top of this file, so downstream surface is unchanged.

-- Denorm per-limb specs (divK_denorm_merge_*, divK_denorm_last_*) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.Denorm (first chunk of #312 split). Re-exported
-- via the import at the top of this file, so downstream surface is unchanged.

-- Epilogue per-limb specs (divK_epilogue_{load,store}_*) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.Epilogue (fourth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Phase B tail spec (divK_phaseB_tail_{code,spec}) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.PhaseBTail (tenth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Phase C2 specs (divK_phaseC2_{code,body_spec,spec}) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.PhaseC2 (ninth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Phase B cascade step spec (divK_phaseB_cascade_step_{code,spec}) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.PhaseBCascade (eleventh chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Loop setup specs (divK_loopSetup_{code,body_spec,spec}) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.LoopSetup (twelfth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- CLZ specs (divK_clz_{init,stage_prog,stage_code,stage_taken_spec,stage_ntaken_spec},
-- divK_clz_last_{prog,code,taken_spec,ntaken_spec}) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.CLZ (thirteenth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Mul-sub partA/partB specs (divK_mulsub_{partA,partB}_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.MulSub (fourteenth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Add-back partA/partB specs (divK_addback_{partA,partB}_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.AddBack (fifteenth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Sub-carry + Store-qj specs (divK_sub_carry_spec, divK_store_qj_{addr,write}_spec)
-- moved to EvmAsm.Evm64.DivMod.LimbSpec.SubCarryStoreQj (sixteenth chunk of #312
-- split). Re-exported via the import at the top of this file, so downstream
-- surface is unchanged.

-- AddBack finalization + Loop control specs (divK_addback_final_spec,
-- divK_loop_control_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.AddBackFinalLoopControl (seventeenth chunk
-- of #312 split). Re-exported via the import at the top of this file, so
-- downstream surface is unchanged.

-- Mul-sub setup + save_j + addback init specs
-- (divK_mulsub_setup_spec, divK_save_j_spec, divK_addback_init_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.MulSubSetup (eighteenth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- Trial quotient specs (divK_correction_branch_spec, divK_trial_load_u_spec,
-- divK_trial_load_vtop_spec, divK_trial_max_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.TrialQuotient (nineteenth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- div128 Phase 1 + Step 1 init specs (divK_div128_{save_split_d,split_ulo,step1_init}_spec)
-- moved to EvmAsm.Evm64.DivMod.LimbSpec.Div128Phase1 (twentieth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- div128 un21 + prodcheck body + q1/q0 corrections specs
-- (divK_div128_{compute_un21,prodcheck_body,correct_q1,correct_q0}_spec)
-- moved to EvmAsm.Evm64.DivMod.LimbSpec.Div128UnProdCheck (twenty-first
-- chunk of #312 split). Re-exported via the import at the top of this file,
-- so downstream surface is unchanged.

-- div128 tail specs (divK_div128_{clamp_test_q1,clamp_test_q0,step2_init,
-- prodcheck2_body,correct_q0_single,combine_q,restore_return}_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.Div128Tail (twenty-second chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- div128 clamp q1 merged spec (divK_div128_clamp_q1_merged_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.Div128Clamp (twenty-third chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.
-- div128 prodcheck1 merged spec (divK_div128_prodcheck1_merged_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1 (twenty-fourth chunk of #312
-- split). Re-exported via the import at the top of this file, so downstream
-- surface is unchanged.

-- div128 clamp q0 merged spec (divK_div128_clamp_q0_merged_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.Div128Clamp (twenty-third chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.
-- div128 prodcheck2 merged spec (divK_div128_prodcheck2_merged_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2 (twenty-fifth chunk of #312
-- split). Re-exported via the import at the top of this file, so downstream
-- surface is unchanged.

-- ============================================================================
-- div128 subroutine: Step 1 full [10]-[24].
-- 15 instructions: DIVU+MUL+SUB (init) + SRLI+BEQ+ADDI+ADD (clamp q1)
--   + LD+MUL+SLLI+OR+BLTU+JAL+ADDI+ADD (product check 1).
-- ============================================================================

/-- div128 step 1: trial division q1, clamp, product check. Instrs [10]-[24].
    Input: u_hi in x7, d_hi in x6, un1 in x11, dlo in memory.
    Output: refined q1 in x10, refined rhat in x7. -/
theorem divK_div128_step1_spec
    (sp u_hi d_hi un1 v1_old v5_old v10_old dlo : Word) (base : Word) :
    let q1 := rv64_divu u_hi d_hi
    let rhat := u_hi - q1 * d_hi
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * dlo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x10 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x5 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x5 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x10 .x10 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 44) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 48) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 52) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 56) (.ADD .x7 .x7 .x6)))))))))))))))
    cpsTriple base (base + 60) cr
      ((.x7 ↦ᵣ u_hi) ** (.x6 ↦ᵣ d_hi) ** (.x10 ↦ᵣ v10_old) **
       (.x5 ↦ᵣ v5_old) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ v1_old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ d_hi) ** (.x10 ↦ᵣ q1') **
       (.x5 ↦ᵣ q_dlo) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ rhat_un1) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** (sp + signExtend12 3952 ↦ₘ dlo)) := by
  intro q1 rhat hi q1c rhatc q_dlo rhat_un1 q1' rhat' cr
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.DIVU .x10 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x5 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x5 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x10 .x10 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 44) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 48) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 52) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 56) (.ADD .x7 .x7 .x6))))))))))))))) := rfl
  -- Sub-spec 1: init [10]-[12]
  have h1_raw := divK_div128_step1_init_spec u_hi d_hi v5_old v10_old base
  have h1 : cpsTriple base (base + 12) cr _ _ :=
    cpsTriple_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]; exact CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_left _ _)))
  have h1f := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ v1_old) ** (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
     (sp + signExtend12 3952 ↦ₘ dlo))
    (by pcFree) h1
  -- Sub-spec 2: clamp q1 [13]-[16]
  have h2_raw := divK_div128_clamp_q1_merged_spec q1 rhat d_hi (q1 * d_hi) (base + 12)
  have : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  have : (base + 12 : Word) + 8 = base + 20 := by bv_addr
  have : (base + 12 : Word) + 12 = base + 24 := by bv_addr
  have : (base + 12 : Word) + 16 = base + 28 := by bv_addr
  simp only [*] at h2_raw
  have h2 : cpsTriple (base + 12) (base + 28) cr _ _ :=
    cpsTriple_extend_code (h := h2_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · simp at h)
  have h2f := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ v1_old) ** (.x12 ↦ᵣ sp) **
     (sp + signExtend12 3952 ↦ₘ dlo))
    (by pcFree) h2
  -- Compose blocks 1 → 2
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1f h2f
  -- Sub-spec 3: prodcheck1 [17]-[24]
  have h3_raw := divK_div128_prodcheck1_merged_spec sp q1c rhatc d_hi un1
    v1_old hi dlo (base + 28)
  have : (base + 28 : Word) + 4 = base + 32 := by bv_addr
  have : (base + 28 : Word) + 8 = base + 36 := by bv_addr
  have : (base + 28 : Word) + 12 = base + 40 := by bv_addr
  have : (base + 28 : Word) + 16 = base + 44 := by bv_addr
  have : (base + 28 : Word) + 20 = base + 48 := by bv_addr
  have : (base + 28 : Word) + 24 = base + 52 := by bv_addr
  have : (base + 28 : Word) + 28 = base + 56 := by bv_addr
  have : (base + 28 : Word) + 32 = base + 60 := by bv_addr
  simp only [*] at h3_raw
  have h3 : cpsTriple (base + 28) (base + 60) cr _ _ :=
    cpsTriple_extend_code (h := h3_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · split at h
              · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
              · split at h
                · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                · split at h
                  · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                  · split at h
                    · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                    · simp at h)
  have h3f := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ 0))
    (by pcFree) h3
  -- Compose blocks 1→2 → 3
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 h3f
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    h123
-- ============================================================================
-- div128 subroutine: Step 2 full [30]-[44].
-- 15 instructions: DIVU+MUL+SUB (init) + SRLI+BEQ+ADDI+ADD (clamp q0)
--   + LD+MUL+SLLI+LD+OR+BLTU+JAL+ADDI (product check 2).
-- ============================================================================

/-- div128 step 2: trial division q0, clamp, product check. Instrs [30]-[44].
    Input: un21 in x7, d_hi in x6, dlo/un0 in memory.
    Output: refined q0 in x5. -/
theorem divK_div128_step2_spec
    (sp un21 d_hi v1_old v5_old v11_old dlo un0 : Word) (base : Word) :
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * dlo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 44) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 48) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 52) (.JAL .x0 8))
       (CodeReq.singleton (base + 56) (.ADDI .x5 .x5 4095)))))))))))))))
    cpsTriple base (base + 60) cr
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ d_hi) ** (.x5 ↦ᵣ v5_old) **
       (.x1 ↦ᵣ v1_old) ** (.x11 ↦ᵣ v11_old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x7 ↦ᵣ q0_dlo) ** (.x6 ↦ᵣ d_hi) ** (.x5 ↦ᵣ q0') **
       (.x1 ↦ᵣ rhat2_un0) ** (.x11 ↦ᵣ un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0 rhat2 hi q0c rhat2c q0_dlo rhat2_un0 q0' cr
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 44) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 48) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 52) (.JAL .x0 8))
       (CodeReq.singleton (base + 56) (.ADDI .x5 .x5 4095))))))))))))))) := rfl
  -- Sub-spec 1: init [30]-[32]
  have h1_raw := divK_div128_step2_init_spec un21 d_hi v1_old v5_old v11_old base
  have h1 : cpsTriple base (base + 12) cr _ _ :=
    cpsTriple_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]; exact CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_left _ _)))
  have h1f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h1
  -- Sub-spec 2: clamp q0 [33]-[36]
  have h2_raw := divK_div128_clamp_q0_merged_spec q0 rhat2 d_hi (q0 * d_hi) (base + 12)
  have : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  have : (base + 12 : Word) + 8 = base + 20 := by bv_addr
  have : (base + 12 : Word) + 12 = base + 24 := by bv_addr
  have : (base + 12 : Word) + 16 = base + 28 := by bv_addr
  simp only [*] at h2_raw
  have h2 : cpsTriple (base + 12) (base + 28) cr _ _ :=
    cpsTriple_extend_code (h := h2_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · simp at h)
  have h2f := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ un21) ** (.x12 ↦ᵣ sp) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h2
  -- Compose blocks 1 → 2
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1f h2f
  -- Sub-spec 3: prodcheck2 [37]-[44]
  have h3_raw := divK_div128_prodcheck2_merged_spec sp q0c rhat2c hi
    un21 dlo un0 (base + 28)
  have : (base + 28 : Word) + 4 = base + 32 := by bv_addr
  have : (base + 28 : Word) + 8 = base + 36 := by bv_addr
  have : (base + 28 : Word) + 12 = base + 40 := by bv_addr
  have : (base + 28 : Word) + 16 = base + 44 := by bv_addr
  have : (base + 28 : Word) + 20 = base + 48 := by bv_addr
  have : (base + 28 : Word) + 24 = base + 52 := by bv_addr
  have : (base + 28 : Word) + 28 = base + 56 := by bv_addr
  have : (base + 28 : Word) + 32 = base + 60 := by bv_addr
  simp only [*] at h3_raw
  have h3 : cpsTriple (base + 28) (base + 60) cr _ _ :=
    cpsTriple_extend_code (h := h3_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · split at h
              · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
              · split at h
                · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                · split at h
                  · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                  · split at h
                    · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                    · simp at h)
  have h3f := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ d_hi) ** (.x0 ↦ᵣ 0))
    (by pcFree) h3
  -- Compose blocks 1→2 → 3
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 h3f
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    h123
-- Composed per-limb specs (divK_mulsub_limb_spec, divK_addback_limb_spec)
-- moved to EvmAsm.Evm64.DivMod.LimbSpec.MulSubLimb (twenty-sixth chunk of
-- #312 split). Re-exported via the import at the top of this file, so
-- downstream surface is unchanged.
-- ============================================================================
-- Trial load + Store qj composed specs (divK_trial_load_spec, divK_store_qj_spec)
-- moved to EvmAsm.Evm64.DivMod.LimbSpec.TrialStoreComposed (twenty-eighth chunk
-- of #312 split). Re-exported via the import at the top of this file, so
-- downstream surface is unchanged.
end EvmAsm.Evm64
