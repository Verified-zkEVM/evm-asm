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
-- ============================================================================
-- div128 subroutine: Product check 2 section [37]-[44].
-- 8 instructions: LD+MUL+SLLI+LD+OR (body) + BLTU+JAL (branch) + ADDI (correction).
-- BLTU taken → ADDI correction, BLTU ntaken → JAL skip. Both merge at base+32.
-- ============================================================================

/-- div128 product check 2: compute q0*d_lo vs rhat2*2^32+un0, conditionally correct q0.
    Instrs [37]-[44]. Both BLTU paths merge at base+32. -/
theorem divK_div128_prodcheck2_merged_spec
    (sp q0 rhat2 v1_old v7_old dlo un0 : Word) (base : Word) :
    let q0_dlo := q0 * dlo
    let rhat2_un0 := (rhat2 <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0 + signExtend12 4095 else q0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 16) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 20) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 24) (.JAL .x0 8))
       (CodeReq.singleton (base + 28) (.ADDI .x5 .x5 4095))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
       (.x7 ↦ᵣ v7_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ un0) **
       (.x7 ↦ᵣ q0_dlo) ** (.x1 ↦ᵣ rhat2_un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0_dlo rhat2_un0 q0' cr
  -- 1. Body: 5 instructions (LD+MUL+SLLI+LD+OR)
  have hbody : cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
       (.x7 ↦ᵣ v7_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
       (.x7 ↦ᵣ q0_dlo) ** (.x1 ↦ᵣ rhat2_un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
    have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo 3952 base (by nofun)
    have I1 := mul_spec_gen .x7 .x5 .x1 v7_old q0 dlo (base + 4) (by nofun)
    have I2 := slli_spec_gen .x1 .x11 dlo rhat2 32 (base + 8) (by nofun)
    have I3 := ld_spec_gen .x11 .x12 sp rhat2 un0 3944 (base + 12) (by nofun)
    have I4 := or_spec_gen_rd_eq_rs1 .x1 .x11 (rhat2 <<< (32 : BitVec 6).toNat) un0 (base + 16) (by nofun)
    runBlock I0 I1 I2 I3 I4
  -- 2. BLTU at base+20
  have hbltu_raw := bltu_spec_gen .x1 .x7 (8 : BitVec 13) rhat2_un0 q0_dlo (base + 20)
  have hsig : signExtend13 (8 : BitVec 13) = (8 : Word) := by decide
  have ha_t : (base + 20) + signExtend13 (8 : BitVec 13) = base + 28 := by rw [hsig]; bv_addr
  have ha_f : (base + 20 : Word) + 4 = base + 24 := by bv_addr
  rw [ha_t, ha_f] at hbltu_raw
  -- 3. Frame BLTU
  have hbltu_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hbltu_raw
  -- 4. Extend to full cr
  have hbltu_ext : cpsBranch (base + 20) cr
      (((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo)) **
       ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
        (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)))
      (base + 28)
        (((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo) ** ⌜BitVec.ult rhat2_un0 q0_dlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
          (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)))
      (base + 24)
        (((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo) ** ⌜¬BitVec.ult rhat2_un0 q0_dlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
          (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))) :=
    fun R hR s hcr hPR hpc =>
      hbltu_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show cr (base + 20) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 20 = base) := by bv_omega
        have h1 : ¬(base + 20 = base + 4) := by bv_omega
        have h2 : ¬(base + 20 = base + 8) := by bv_omega
        have h3 : ¬(base + 20 = base + 12) := by bv_omega
        have h4 : ¬(base + 20 = base + 16) := by bv_omega
        simp only [beq_iff_eq, h0, h1, h2, h3, h4, ↓reduceIte]))) hPR hpc
  -- 5. Compose body → BLTU
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbltu_ext
  -- 6. by_cases on BLTU condition
  by_cases hcond : BitVec.ult rhat2_un0 q0_dlo
  · -- BLTU taken: correction (ADDI q0--)
    have hq : q0' = q0 + signExtend12 4095 := if_pos hcond
    rw [hq]
    have taken_br := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    -- Correction: ADDI q0-- from base+28 to base+32
    have I5 := addi_spec_gen_same .x5 q0 4095 (base + 28) (by nofun)
    have hcorr : cpsTriple (base + 28) (base + 32) cr
        (.x5 ↦ᵣ q0)
        (.x5 ↦ᵣ (q0 + signExtend12 4095)) := by
      runBlock I5
    have hcorr_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (by pcFree) hcorr
    have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp')
      taken_br hcorr_framed
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full
  · -- BLTU not-taken: JAL skip
    have hq : q0' = q0 := if_neg hcond
    rw [hq]
    have ntaken_br := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact absurd ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    -- JAL skip: base+24 → base+32
    have hj : signExtend21 (8 : BitVec 21) = (8 : Word) := by decide
    have I_jal := jal_x0_spec_gen 8 (base + 24)
    rw [hj] at I_jal
    have ha_jal : (base + 24 : Word) + 8 = base + 32 := by bv_addr
    rw [ha_jal] at I_jal
    have hcr_jal : ∀ a i, CodeReq.singleton (base + 24) (.JAL .x0 8) a = some i →
        cr a = some i := by
      intro a i h
      simp only [CodeReq.singleton] at h
      split at h
      · next heq => rw [beq_iff_eq] at heq; subst heq; simp_all [cr, CodeReq.union, CodeReq.singleton]
      · simp at h
    have I_jal_cr := cpsTriple_extend_code hcr_jal I_jal
    have hjal_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo) ** (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) **
       (.x11 ↦ᵣ un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (by pcFree) I_jal_cr
    simp only [sepConj_emp_left'] at hjal_framed
    have ntaken_clean : cpsTriple base (base + 24) cr
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
         (.x7 ↦ᵣ v7_old) ** (.x1 ↦ᵣ v1_old) **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
        ((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo) **
         (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) :=
      cpsTriple_consequence _ _ _ _ _ _ _
        (fun h hp => hp)
        (fun h hp => by
          have hp' : (((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo)) **
            ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
             (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))) h :=
            sepConj_mono_left (sepConj_mono_right
              (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
          xperm_hyp hp')
        ntaken_br
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
        (fun _ hp => hp)
        ntaken_clean hjal_framed)
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
