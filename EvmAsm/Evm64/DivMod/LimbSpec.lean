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
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Phase1
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Tail
import EvmAsm.Evm64.DivMod.LimbSpec.Div128UnProdCheck
import EvmAsm.Evm64.DivMod.LimbSpec.Epilogue
import EvmAsm.Evm64.DivMod.LimbSpec.LoopSetup
import EvmAsm.Evm64.DivMod.LimbSpec.MulSub
import EvmAsm.Evm64.DivMod.LimbSpec.MulSubSetup
import EvmAsm.Evm64.DivMod.LimbSpec.NormA
import EvmAsm.Evm64.DivMod.LimbSpec.NormB
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseA
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseBCascade
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseBInit
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseBTail
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseC2
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

-- ============================================================================
-- Subtract carry from u[j+4]: 4 instructions after mul-sub limbs.
-- ============================================================================

/-- Subtract carry from u[j+4].
    4 instructions: LD, SLTU, SUB, SD. Produces borrow (x7). -/
theorem divK_sub_carry_spec (u_base carry_in v5_old v7_old u_top : Word)
    (u_off : BitVec 12) (base : Word) :
    let borrow := if BitVec.ult u_top carry_in then (1 : Word) else 0
    let u_new := u_top - carry_in
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x7 .x5 .x10))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x5 .x5 .x10))
       (CodeReq.singleton (base + 12) (.SD .x6 .x5 u_off))))
    cpsTriple base (base + 16) cr
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       ((u_base + signExtend12 u_off) ↦ₘ u_top))
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ u_new) ** (.x7 ↦ᵣ borrow) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro borrow u_new cr
  have I0 := ld_spec_gen .x5 .x6 u_base v5_old u_top u_off base (by nofun)
  have I1 := sltu_spec_gen .x7 .x5 .x10 v7_old u_top carry_in (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x5 .x10 u_top carry_in (base + 8) (by nofun)
  have I3 := sd_spec_gen .x6 .x5 u_base u_new u_top u_off (base + 12)
  runBlock I0 I1 I2 I3

-- ============================================================================
-- Store q[j]: 4 instructions.
-- ============================================================================

/-- Store q[j]: compute &q[j] = sp+4088 - j*8, store q_hat.
    First 3 instructions compute q_addr. Then SD stores. Split into 3+1. -/
theorem divK_store_qj_addr_spec (sp j v5_old v7_old : Word)
    (base : Word) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let sp_m8 := sp + signExtend12 4088
    let q_addr := sp_m8 - j_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x7 .x12 4088))
       (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5)))
    cpsTriple base (base + 12) cr
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr)) := by
  intro j_x8 sp_m8 q_addr cr
  have I0 := slli_spec_gen .x5 .x1 v5_old j 3 base (by nofun)
  have I1 := addi_spec_gen .x7 .x12 v7_old sp 4088 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 sp_m8 j_x8 (base + 8) (by nofun)
  runBlock I0 I1 I2

/-- Store q[j]: SD q_hat at q_addr. 1 instruction. -/
theorem divK_store_qj_write_spec (q_addr q_hat q_old : Word) (base : Word) :
    let cr := CodeReq.singleton base (.SD .x7 .x11 0)
    cpsTriple base (base + 4) cr
      ((.x7 ↦ᵣ q_addr) ** (.x11 ↦ᵣ q_hat) ** (q_addr ↦ₘ q_old))
      ((.x7 ↦ᵣ q_addr) ** (.x11 ↦ᵣ q_hat) ** (q_addr ↦ₘ q_hat)) := by
  intro cr
  have hse : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr : q_addr + signExtend12 (0 : BitVec 12) = q_addr := by rw [hse]; bv_omega
  have I0 := sd_spec_gen .x7 .x11 q_addr q_hat q_old 0 base
  rw [haddr] at I0
  runBlock I0

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

-- ============================================================================
-- div128 subroutine: Clamp q1 section [13]-[16].
-- 4 instructions: SRLI + BEQ + ADDI + ADD.
-- BEQ skips correction if q1 < 2^32, else q1-- and rhat+=d_hi.
-- ============================================================================

/-- div128 clamp q1: test q1 >= 2^32, conditionally decrement and adjust rhat.
    Instrs [13]-[16]. Both BEQ paths merge at base+16. -/
theorem divK_div128_clamp_q1_merged_spec (q1 rhat d_hi v5_old : Word) (base : Word) :
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1' := if hi = 0 then q1 else q1 + signExtend12 4095
    let rhat' := if hi = 0 then rhat else rhat + d_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x5 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.BEQ .x5 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 12) (.ADD .x7 .x7 .x6))))
    cpsTriple base (base + 16) cr
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ v5_old) ** (.x0 ↦ᵣ 0))
      ((.x10 ↦ᵣ q1') ** (.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
  intro hi q1' rhat' cr
  -- 1. SRLI body
  have I0 := srli_spec_gen .x5 .x10 v5_old q1 32 base (by nofun)
  have hbody : cpsTriple base (base + 4) cr
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ v5_old) ** (.x0 ↦ᵣ 0))
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
    runBlock I0
  -- 2. BEQ at base+4 (keep pure facts)
  have hbeq_raw := beq_spec_gen .x5 .x0 (12 : BitVec 13) hi (0 : Word) (base + 4)
  have hsig : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbeq_raw
  -- 3. Frame BEQ with x10, x7, x6
  have hbeq_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))
    (by pcFree) hbeq_raw
  -- 4. Extend to full cr
  have hbeq_ext : cpsBranch (base + 4) cr
      (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi)))
      (base + 16)
        (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi = 0⌝) **
         ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi)))
      (base + 8)
        (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi ≠ 0⌝) **
         ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))) :=
    fun R hR s hcr hPR hpc =>
      hbeq_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show cr (base + 4) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  -- 5. Compose body → BEQ
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_ext
  -- 6. by_cases on hi = 0
  by_cases hcond : hi = 0
  · -- hi = 0 → BEQ taken (skip correction)
    have hq : q1' = q1 := if_pos hcond
    have hr : rhat' = rhat := if_pos hcond
    rw [hq, hr]
    -- Eliminate ntaken path (hi ≠ 0 contradicts hcond)
    have taken := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    -- Strip pure fact from taken postcondition and permute
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') taken
  · -- hi ≠ 0 → BEQ not-taken (execute correction)
    have hq : q1' = q1 + signExtend12 4095 := if_neg hcond
    have hr : rhat' = rhat + d_hi := if_neg hcond
    rw [hq, hr]
    -- Eliminate taken path (hi = 0 contradicts hcond)
    have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact hcond ((sepConj_pure_right _ _ _).1 h_x0p).2)
    -- Correction: ADDI + ADD from base+8 to base+16
    have I1 := addi_spec_gen_same .x10 q1 4095 (base + 8) (by nofun)
    have I2 := add_spec_gen_rd_eq_rs1 .x7 .x6 rhat d_hi (base + 12) (by nofun)
    have hcorr : cpsTriple (base + 8) (base + 16) cr
        ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))
        ((.x10 ↦ᵣ (q1 + signExtend12 4095)) ** (.x7 ↦ᵣ (rhat + d_hi)) ** (.x6 ↦ᵣ d_hi)) := by
      runBlock I1 I2
    have hcorr_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcFree) hcorr
    have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') ntaken hcorr_framed
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full
-- ============================================================================
-- div128 subroutine: Product check 1 section [17]-[24].
-- 8 instructions: LD+MUL+SLLI+OR (body) + BLTU+JAL (branch) + ADDI+ADD (correction).
-- BLTU taken → correction, BLTU ntaken → JAL skip. Both merge at base+32.
-- ============================================================================

/-- div128 product check 1: compute q1*d_lo vs rhat*2^32+un1, conditionally correct.
    Instrs [17]-[24]. Both BLTU paths merge at base+32. -/
theorem divK_div128_prodcheck1_merged_spec
    (sp q1 rhat d_hi un1 v1_old v5_old dlo : Word) (base : Word) :
    let q_dlo := q1 * dlo
    let rhat_un1 := (rhat <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1 + signExtend12 4095 else q1
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhat + d_hi else rhat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 20) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 28) (.ADD .x7 .x7 .x6))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1') ** (.x7 ↦ᵣ rhat') ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ q_dlo) ** (.x1 ↦ᵣ rhat_un1) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo)) := by
  intro q_dlo rhat_un1 q1' rhat' cr
  -- 1. Body: 4 instructions (LD+MUL+SLLI+OR)
  have hbody : cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ q_dlo) ** (.x1 ↦ᵣ rhat_un1) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo)) := by
    have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo 3952 base (by nofun)
    have I1 := mul_spec_gen .x5 .x10 .x1 v5_old q1 dlo (base + 4) (by nofun)
    have I2 := slli_spec_gen .x1 .x7 dlo rhat 32 (base + 8) (by nofun)
    have I3 := or_spec_gen_rd_eq_rs1 .x1 .x11 (rhat <<< (32 : BitVec 6).toNat) un1 (base + 12) (by nofun)
    runBlock I0 I1 I2 I3
  -- 2. BLTU at base+16, strip pure
  have hbltu_raw := bltu_spec_gen .x1 .x5 (8 : BitVec 13) rhat_un1 q_dlo (base + 16)
  have hsig : signExtend13 (8 : BitVec 13) = (8 : Word) := by decide
  have ha_t : (base + 16) + signExtend13 (8 : BitVec 13) = base + 24 := by rw [hsig]; bv_addr
  have ha_f : (base + 16 : Word) + 4 = base + 20 := by bv_addr
  rw [ha_t, ha_f] at hbltu_raw
  -- 3. Frame BLTU with remaining atoms
  have hbltu_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
     (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo))
    (by pcFree) hbltu_raw
  -- 4. Extend to full cr
  have hbltu_ext : cpsBranch (base + 16) cr
      (((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo)) **
       ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
        (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo)))
      (base + 24)
        (((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) ** ⌜BitVec.ult rhat_un1 q_dlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
          (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo)))
      (base + 20)
        (((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) ** ⌜¬BitVec.ult rhat_un1 q_dlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
          (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo))) :=
    fun R hR s hcr hPR hpc =>
      hbltu_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show cr (base + 16) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 16 = base) := by bv_omega
        have h1 : ¬(base + 16 = base + 4) := by bv_omega
        have h2 : ¬(base + 16 = base + 8) := by bv_omega
        have h3 : ¬(base + 16 = base + 12) := by bv_omega
        simp only [beq_iff_eq, h0, h1, h2, h3, ↓reduceIte]))) hPR hpc
  -- 5. Compose body → BLTU
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbltu_ext
  -- 6. by_cases on BLTU condition
  by_cases hcond : BitVec.ult rhat_un1 q_dlo
  · -- BLTU taken: rhat_un1 < q_dlo → correction
    have hq : q1' = q1 + signExtend12 4095 := if_pos hcond
    have hr : rhat' = rhat + d_hi := if_pos hcond
    rw [hq, hr]
    -- Eliminate ntaken path
    have taken_br := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    -- Correction: ADDI q1-- + ADD rhat+=d_hi
    have I4 := addi_spec_gen_same .x10 q1 4095 (base + 24) (by nofun)
    have I5 := add_spec_gen_rd_eq_rs1 .x7 .x6 rhat d_hi (base + 28) (by nofun)
    have hcorr : cpsTriple (base + 24) (base + 32) cr
        ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))
        ((.x10 ↦ᵣ (q1 + signExtend12 4095)) ** (.x7 ↦ᵣ (rhat + d_hi)) ** (.x6 ↦ᵣ d_hi)) := by
      runBlock I4 I5
    have hcorr_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ un1) **
       (sp + signExtend12 3952 ↦ₘ dlo))
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
  · -- BLTU not-taken: rhat_un1 >= q_dlo → JAL skip
    have hq : q1' = q1 := if_neg hcond
    have hr : rhat' = rhat := if_neg hcond
    rw [hq, hr]
    -- Eliminate taken path
    have ntaken_br := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact absurd ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    -- JAL skip: base+20 → base+32
    have hj : signExtend21 (12 : BitVec 21) = (12 : Word) := by decide
    have I_jal := jal_x0_spec_gen 12 (base + 20)
    rw [hj] at I_jal
    have ha_jal : (base + 20 : Word) + 12 = base + 32 := by bv_addr
    rw [ha_jal] at I_jal
    -- Extend JAL CR from singleton to cr
    have hcr_jal : ∀ a i, CodeReq.singleton (base + 20) (.JAL .x0 12) a = some i →
        cr a = some i := by
      intro a i h
      simp only [CodeReq.singleton] at h
      split at h
      · next heq => rw [beq_iff_eq] at heq; subst heq; simp_all [cr, CodeReq.union, CodeReq.singleton]
      · simp at h
    have I_jal_cr := cpsTriple_extend_code hcr_jal I_jal
    have hjal_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) ** (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) **
       (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      (by pcFree) I_jal_cr
    simp only [sepConj_emp_left'] at hjal_framed
    -- Strip pure and compose with JAL
    have ntaken_clean : cpsTriple base (base + 20) cr
        ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
         (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (.x6 ↦ᵣ d_hi) **
         (sp + signExtend12 3952 ↦ₘ dlo))
        ((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) **
         (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
         (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo)) :=
      cpsTriple_consequence _ _ _ _ _ _ _
        (fun h hp => hp)
        (fun h hp => by
          have hp' : (((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo)) **
            ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
             (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo))) h :=
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
-- div128 subroutine: Clamp q0 section [33]-[36].
-- 4 instructions: SRLI + BEQ + ADDI + ADD.
-- BEQ skips correction if q0 < 2^32, else q0-- and rhat2+=d_hi.
-- ============================================================================

/-- div128 clamp q0: test q0 >= 2^32, conditionally decrement and adjust rhat2.
    Instrs [33]-[36]. Both BEQ paths merge at base+16. -/
theorem divK_div128_clamp_q0_merged_spec (q0 rhat2 d_hi v1_old : Word) (base : Word) :
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0' := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2' := if hi = 0 then rhat2 else rhat2 + d_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x5 .x5 4095))
       (CodeReq.singleton (base + 12) (.ADD .x11 .x11 .x6))))
    cpsTriple base (base + 16) cr
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi) **
       (.x1 ↦ᵣ v1_old) ** (.x0 ↦ᵣ 0))
      ((.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2') ** (.x6 ↦ᵣ d_hi) **
       (.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
  intro hi q0' rhat2' cr
  -- 1. SRLI body
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi) **
       (.x1 ↦ᵣ v1_old) ** (.x0 ↦ᵣ 0))
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi) **
       (.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
    have I0 := srli_spec_gen .x1 .x5 v1_old q0 32 base (by nofun)
    runBlock I0
  -- 2. BEQ at base+4 (keep pure facts)
  have hbeq_raw := beq_spec_gen .x1 .x0 (12 : BitVec 13) hi (0 : Word) (base + 4)
  have hsig : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbeq_raw
  -- 3. Frame BEQ with x5, x11, x6
  have hbeq_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi))
    (by pcFree) hbeq_raw
  -- 4. Extend to full cr
  have hbeq_ext : cpsBranch (base + 4) cr
      (((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi)))
      (base + 16)
        (((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi = 0⌝) **
         ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi)))
      (base + 8)
        (((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi ≠ 0⌝) **
         ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi))) :=
    fun R hR s hcr hPR hpc =>
      hbeq_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show cr (base + 4) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  -- 5. Compose body → BEQ
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_ext
  -- 6. by_cases on hi = 0
  by_cases hcond : hi = 0
  · -- hi = 0 → BEQ taken (skip correction)
    have hq : q0' = q0 := if_pos hcond
    have hr : rhat2' = rhat2 := if_pos hcond
    rw [hq, hr]
    have taken := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') taken
  · -- hi ≠ 0 → BEQ not-taken (execute correction)
    have hq : q0' = q0 + signExtend12 4095 := if_neg hcond
    have hr : rhat2' = rhat2 + d_hi := if_neg hcond
    rw [hq, hr]
    have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact hcond ((sepConj_pure_right _ _ _).1 h_x0p).2)
    -- Correction: ADDI + ADD from base+8 to base+16
    have I1 := addi_spec_gen_same .x5 q0 4095 (base + 8) (by nofun)
    have I2 := add_spec_gen_rd_eq_rs1 .x11 .x6 rhat2 d_hi (base + 12) (by nofun)
    have hcorr : cpsTriple (base + 8) (base + 16) cr
        ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi))
        ((.x5 ↦ᵣ (q0 + signExtend12 4095)) ** (.x11 ↦ᵣ (rhat2 + d_hi)) ** (.x6 ↦ᵣ d_hi)) := by
      runBlock I1 I2
    have hcorr_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcFree) hcorr
    have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') ntaken hcorr_framed
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full
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
-- ============================================================================
-- div128 subroutine: Phase 1 [0]-[9] — save ret/d, split d and u_lo.
-- 10 instructions: SD+SD+SRLI+SLLI+SRLI+SD + SRLI+SLLI+SRLI+SD.
-- ============================================================================

/-- div128 Phase 1: save return addr/d, split d and u_lo. Instrs [0]-[9].
    Input: x12=sp, x2=ret_addr, x10=d, x5=u_lo, x7=u_hi.
    Output: x6=d_hi, x11=un1, x5=un0 (saved), x7=u_hi (unchanged). -/
theorem divK_div128_phase1_spec
    (sp ret_addr d u_lo u_hi v1_old v6_old v11_old
     ret_mem d_mem dlo_mem un0_mem : Word) (base : Word) :
    let d_hi := d >>> (32 : BitVec 6).toNat
    let d_lo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let un1 := u_lo >>> (32 : BitVec 6).toNat
    let un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SD .x12 .x2 3968))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x10 3960))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SRLI .x6 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLLI .x1 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SRLI .x1 .x1 32))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x1 3952))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SRLI .x11 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SLLI .x5 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SRLI .x5 .x5 32))
       (CodeReq.singleton (base + 36) (.SD .x12 .x5 3944))))))))))
    cpsTriple base (base + 40) cr
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ v6_old) ** (.x1 ↦ᵣ v1_old) ** (.x5 ↦ᵣ u_lo) **
       (.x11 ↦ᵣ v11_old) ** (.x7 ↦ᵣ u_hi) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ d_hi) ** (.x1 ↦ᵣ d_lo) ** (.x5 ↦ᵣ un0) **
       (.x11 ↦ᵣ un1) ** (.x7 ↦ᵣ u_hi) **
       (sp + signExtend12 3968 ↦ₘ ret_addr) **
       (sp + signExtend12 3960 ↦ₘ d) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro d_hi d_lo un1 un0 cr
  -- Instructions from save_split_d (6 instrs at base)
  have I0 := sd_spec_gen .x12 .x2 sp ret_addr ret_mem 3968 base
  have I1 := sd_spec_gen .x12 .x10 sp d d_mem 3960 (base + 4)
  have I2 := srli_spec_gen .x6 .x10 v6_old d 32 (base + 8) (by nofun)
  have I3 := slli_spec_gen .x1 .x10 v1_old d 32 (base + 12) (by nofun)
  have I4 := srli_spec_gen_same .x1 (d <<< (32 : BitVec 6).toNat) 32 (base + 16) (by nofun)
  have I5 := sd_spec_gen .x12 .x1 sp d_lo dlo_mem 3952 (base + 20)
  -- Instructions from split_ulo (4 instrs at base+24)
  have I6 := srli_spec_gen .x11 .x5 v11_old u_lo 32 (base + 24) (by nofun)
  have I7 := slli_spec_gen_same .x5 u_lo 32 (base + 28) (by nofun)
  have I8 := srli_spec_gen_same .x5 (u_lo <<< (32 : BitVec 6).toNat) 32 (base + 32) (by nofun)
  have I9 := sd_spec_gen .x12 .x5 sp un0 un0_mem 3944 (base + 36)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9
-- ============================================================================
-- div128 subroutine: End phase [45]-[48] — combine q + restore/return.
-- 4 instructions: SLLI + OR + LD + JALR.
-- ============================================================================

/-- div128 end phase: combine q1,q0 into q, restore return addr, return.
    Instrs [45]-[48]. Exit to ret_addr. -/
theorem divK_div128_end_spec
    (sp q1 q0 v2_old v11_old ret_addr : Word) (base : Word)
    (halign : (ret_addr + signExtend12 0) &&& ~~~1 = ret_addr) :
    let q1_hi := q1 <<< (32 : BitVec 6).toNat
    let q := q1_hi ||| q0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x11 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.OR .x11 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x2 .x12 3968))
       (CodeReq.singleton (base + 12) (.JALR .x0 .x2 0))))
    cpsTriple base ret_addr cr
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ v11_old) **
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2_old) ** (sp + signExtend12 3968 ↦ₘ ret_addr))
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ q) **
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr)) := by
  intro q1_hi q cr
  -- Instructions from combine_q (2 instrs at base)
  have I0 := slli_spec_gen .x11 .x10 v11_old q1 32 base (by nofun)
  have I1 := or_spec_gen_rd_eq_rs1 .x11 .x5 q1_hi q0 (base + 4) (by nofun)
  -- Instructions from restore_return (2 instrs at base+8)
  have I2 := ld_spec_gen .x2 .x12 sp v2_old ret_addr 3968 (base + 8) (by nofun)
  have I3 := jalr_x0_spec_gen .x2 ret_addr 0 (base + 12)
  rw [halign] at I3
  runBlock I0 I1 I2 I3
-- ============================================================================
-- Composed per-limb specs: mulsub_limb, addback_limb.
-- These compose partA+partB into single per-limb operations.
-- ============================================================================

/-- Mul-sub full limb: partA (6 instrs) + partB (5 instrs) = 11 instructions.
    Input: q_hat (x11), carry_in (x10), v[i] and u[j+i] in memory.
    Output: carry_out (x10), u_new stored. -/
theorem divK_mulsub_limb_spec
    (sp u_base q_hat carry_in v5_old v7_old v2_old v_i u_i : Word)
    (v_off u_off : BitVec 12) (base : Word) :
    let prod_lo := q_hat * v_i
    let prod_hi := rv64_mulhu q_hat v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let partial_carry := borrow_add + prod_hi
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    let u_new := u_i - full_sub
    let carry_out := partial_carry + borrow_sub
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.MULHU .x5 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x7 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x10 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADD .x10 .x10 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SLTU .x5 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SUB .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 36) (.ADD .x10 .x10 .x5))
       (CodeReq.singleton (base + 40) (.SD .x6 .x2 u_off)))))))))))
    cpsTriple base (base + 44) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_in) **
       (.x6 ↦ᵣ u_base) ** (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_out) **
       (.x6 ↦ᵣ u_base) ** (.x5 ↦ᵣ borrow_sub) ** (.x7 ↦ᵣ full_sub) **
       (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro prod_lo prod_hi full_sub borrow_add partial_carry borrow_sub u_new carry_out cr
  -- Instructions from partA (6 instrs at base)
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun)
  have I1 := mul_spec_gen .x7 .x11 .x5 v7_old q_hat v_i (base + 4) (by nofun)
  have I2 := mulhu_spec_gen_rd_eq_rs2 .x5 .x11 q_hat v_i (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x7 .x10 prod_lo carry_in (base + 12) (by nofun)
  have I4 := sltu_spec_gen_rd_eq_rs2 .x10 .x7 full_sub carry_in (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1 .x10 .x5 borrow_add prod_hi (base + 20) (by nofun)
  -- Instructions from partB (5 instrs at base+24)
  have I6 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 24) (by nofun)
  have I7 := sltu_spec_gen .x5 .x2 .x7 prod_hi u_i full_sub (base + 28) (by nofun)
  have I8 := sub_spec_gen_rd_eq_rs1 .x2 .x7 u_i full_sub (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1 .x10 .x5 partial_carry borrow_sub (base + 36) (by nofun)
  have I10 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 40)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10
/-- Add-back full limb: partA (5 instrs) + partB (3 instrs) = 8 instructions.
    Input: carry_in (x7), v[i] and u[j+i] in memory.
    Output: carry_out (x7), u_new stored. -/
theorem divK_addback_limb_spec
    (sp u_base carry_in v5_old v2_old v_i u_i : Word)
    (v_off u_off : BitVec 12) (base : Word) :
    let u_plus_carry := u_i + carry_in
    let carry1 := if BitVec.ult u_plus_carry carry_in then (1 : Word) else 0
    let u_new := u_plus_carry + v_i
    let carry2 := if BitVec.ult u_new v_i then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x7 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.ADD .x2 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SLTU .x5 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x7 .x7 .x5))
       (CodeReq.singleton (base + 28) (.SD .x6 .x2 u_off))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ carry2) ** (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro u_plus_carry carry1 u_new carry2 carry_out cr
  -- Instructions from partA (5 instrs at base)
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun)
  have I1 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 4) (by nofun)
  have I2 := add_spec_gen_rd_eq_rs1 .x2 .x7 u_i carry_in (base + 8) (by nofun)
  have I3 := sltu_spec_gen_rd_eq_rs2 .x7 .x2 u_plus_carry carry_in (base + 12) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x2 .x5 u_plus_carry v_i (base + 16) (by nofun)
  -- Instructions from partB (3 instrs at base+20)
  have I5 := sltu_spec_gen_rd_eq_rs2 .x5 .x2 u_new v_i (base + 20) (by nofun)
  have I6 := or_spec_gen_rd_eq_rs1 .x7 .x5 carry1 carry2 (base + 24) (by nofun)
  have I7 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 28)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7
-- ============================================================================
-- Trial quotient load phase: load u[j+n], u[j+n-1], v_top = b[n-1].
-- trial_load_u [1]-[7] + trial_load_vtop [8]-[12] = 12 instructions.
-- ============================================================================

/-- Trial quotient load: fetch u_hi, u_lo, v_top from memory.
    Instrs [1]-[12] of loop body.
    Output: x7 = u_hi, x5 = u_lo, x10 = v_top, x6 = vtop_base. -/
theorem divK_trial_load_spec
    (sp j n v5_old v6_old v7_old v10_old u_hi u_lo v_top : Word)
    (base : Word) :
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x7 .x1 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x7 .x7 3))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADDI .x5 .x12 4056))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x5 0))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x6 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 32) (.ADDI .x6 .x6 4095))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x6 .x6 3))
      (CodeReq.union (CodeReq.singleton (base + 40) (.ADD .x6 .x12 .x6))
       (CodeReq.singleton (base + 44) (.LD .x10 .x6 32))))))))))))
    cpsTriple base (base + 48) cr
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtop_base) **
       (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top)) := by
  intro u_addr vtop_base cr
  -- Instructions from trial_load_u (7 instrs at base)
  let jpn := j + n
  let jpn_x8 := jpn <<< (3 : BitVec 6).toNat
  let u0_base := sp + signExtend12 4056
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr0 : u_addr + signExtend12 (0 : BitVec 12) = u_addr := by rw [hse0]; bv_omega
  have I0 := ld_spec_gen .x5 .x12 sp v5_old n 3984 base (by nofun)
  have I1 := add_spec_gen .x7 .x1 .x5 j n v7_old (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x7 jpn 3 (base + 8) (by nofun)
  have I3 := addi_spec_gen .x5 .x12 n sp 4056 (base + 12) (by nofun)
  have I4 := sub_spec_gen_rd_eq_rs1 .x5 .x7 u0_base jpn_x8 (base + 16) (by nofun)
  have I5 := ld_spec_gen .x7 .x5 u_addr jpn_x8 u_hi 0 (base + 20) (by nofun)
  rw [haddr0] at I5
  have I6 := ld_spec_gen_same .x5 u_addr u_lo 8 (base + 24) (by nofun)
  -- Instructions from trial_load_vtop (5 instrs at base+28)
  let nm1 := n + signExtend12 4095
  let nm1_x8 := nm1 <<< (3 : BitVec 6).toNat
  have I7 := ld_spec_gen .x6 .x12 sp v6_old n 3984 (base + 28) (by nofun)
  have I8 := addi_spec_gen_same .x6 n 4095 (base + 32) (by nofun)
  have I9 := slli_spec_gen_same .x6 nm1 3 (base + 36) (by nofun)
  have I10 := add_spec_gen_rd_eq_rs2 .x6 .x12 sp nm1_x8 (base + 40) (by nofun)
  have I11 := ld_spec_gen .x10 .x6 vtop_base v10_old v_top 32 (base + 44) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11
-- ============================================================================
-- Composed store q[j]: addr computation + SD = 4 instructions.
-- ============================================================================

/-- Store q[j]: compute address and store q_hat. 4 instructions.
    q_addr = sp + 4088 - j*8. -/
theorem divK_store_qj_spec (sp j q_hat v5_old v7_old q_old : Word)
    (base : Word) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - j_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x7 .x12 4088))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
       (CodeReq.singleton (base + 12) (.SD .x7 .x11 0))))
    cpsTriple base (base + 16) cr
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (q_addr ↦ₘ q_old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr) **
       (q_addr ↦ₘ q_hat)) := by
  intro j_x8 q_addr cr
  -- Instructions from store_qj_addr (3 instrs at base)
  have I0 := slli_spec_gen .x5 .x1 v5_old j 3 base (by nofun)
  have I1 := addi_spec_gen .x7 .x12 v7_old sp 4088 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 (sp + signExtend12 4088) j_x8 (base + 8) (by nofun)
  -- SD instruction with signExtend12 normalization
  have hse : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr : q_addr + signExtend12 (0 : BitVec 12) = q_addr := by rw [hse]; bv_omega
  have I3 := sd_spec_gen .x7 .x11 q_addr q_hat q_old 0 (base + 12)
  rw [haddr] at I3
  runBlock I0 I1 I2 I3
end EvmAsm.Evm64
