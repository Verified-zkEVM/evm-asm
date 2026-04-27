/-
  EvmAsm.Evm64.DivModSpec

  CPS specifications for the 256-bit EVM DIV and MOD programs (Knuth Algorithm D).
  Bottom-up decomposition starting from the simplest phases.
-/

-- Every `LimbSpec.*` sub-file already imports `DivMod.Program`,
-- `Rv64.SyscallSpecs`, `Rv64.ControlFlow`, `Rv64.Tactics.XSimp`, and
-- `Rv64.Tactics.RunBlock`, so those direct imports would be redundant.
import EvmAsm.Evm64.DivMod.LimbSpec.AddBack
import EvmAsm.Evm64.DivMod.LimbSpec.AddBackFinalLoopControl
import EvmAsm.Evm64.DivMod.LimbSpec.CLZ
import EvmAsm.Evm64.DivMod.LimbSpec.CopyAU
import EvmAsm.Evm64.DivMod.LimbSpec.Denorm
-- `Div128Step1` covers `Div128Clamp`, `Div128Phase1`, `Div128ProdCheck1`.
-- `Div128Step2` covers `Div128Clamp`, `Div128ProdCheck2`, `Div128Tail`.
import EvmAsm.Evm64.DivMod.LimbSpec.Div128PhaseEnd
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1v2
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2
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

-- div128 step 1 full composition spec (divK_div128_step1_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1 (twenty-ninth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

-- div128 step 2 full composition spec (divK_div128_step2_spec) moved to
-- EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2 (thirtieth chunk of #312 split).
-- Re-exported via the import at the top of this file, so downstream surface
-- is unchanged.

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
