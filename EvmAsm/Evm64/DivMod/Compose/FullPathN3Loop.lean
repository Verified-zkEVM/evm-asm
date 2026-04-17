-- file-size-exception: tracked by issue #312 (Compose subtree split). Each loop-iteration lift composes with the pre-loop in one place; grandfathered pending split into per-iteration files.
/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop

  Lifts n=3 two-iteration loop compositions from sharedDivModCode to divCode,
  and composes with the pre-loop (base → base+448) to produce
  preloop+loop specs (base → base+904).
-/

import EvmAsm.Evm64.DivMod.LoopComposeN3
import EvmAsm.Evm64.DivMod.LoopUnifiedN3
import EvmAsm.Evm64.DivMod.Compose.FullPathN3
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address normalization lemmas for n=3 preloop+loop composition
-- ============================================================================

/-- signExtend12(4) - 3 = 1, for x1 register in loopSetupPost at n=3. -/
theorem x1_val_n3 : signExtend12 (4 : BitVec 12) - (3 : Word) = (1 : Word) := by decide

-- se12_32, se12_40, se12_48, se12_56 are in Base.lean

-- Address normalization: signExtend12/<<</>> → concrete values via simp, then bv_omega.
-- bv_addr only handles (a+k1)+k2=a+k3; these involve subtraction and shifts.
-- Pattern matches LoopComposeN3.lean.
theorem n3_ub1_off0 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) =
    sp + signExtend12 4048 := by
  divmod_addr
theorem n3_ub1_off4088 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    sp + signExtend12 4040 := by
  divmod_addr
theorem n3_ub1_off4080 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    sp + signExtend12 4032 := by
  divmod_addr
theorem n3_ub1_off4072 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    sp + signExtend12 4024 := by
  divmod_addr
theorem n3_ub1_off4064 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 =
    sp + signExtend12 4016 := by
  divmod_addr
theorem n3_ub0_off0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) =
    sp + signExtend12 4056 := by
  divmod_addr
theorem n3_qa1 (sp : Word) :
    sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4080 := by
  divmod_addr
theorem n3_qa0 (sp : Word) :
    sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4088 := by
  divmod_addr
theorem n3_uhi_1_addr (sp : Word) :
    sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4024 := by
  divmod_addr
theorem n3_ulo_1_addr (sp : Word) :
    (sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4032 := by
  divmod_addr
theorem n3_vtop_addr (sp : Word) :
    sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32 = sp + 48 := by
  divmod_addr
theorem n3_uhi_0_addr (sp : Word) :
    sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4032 := by
  divmod_addr
theorem n3_ulo_0_addr (sp : Word) :
    (sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4040 := by
  divmod_addr

-- ============================================================================
-- Lift unified n=3 _da loop from sharedDivModCode to divCode
-- ============================================================================

/-- Lift the unified n=3 2-iteration _da loop spec from sharedDivModCode to divCode. -/
theorem divK_loop_n3_unified_da_divCode (bltu_1 bltu_0 : Bool)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu_1 : bltu_1 = BitVec.ult u3 v2)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN3_da bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2) :
    cpsTriple (base + 448) (base + 908) (divCode base)
      (loopN3PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN3UnifiedPost_da bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig
        ret_mem d_mem dlo_mem scratch_un0) :=
  cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_n3_unified_da_spec bltu_1 bltu_0
      sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
      hbltu_1 hbltu_0)
