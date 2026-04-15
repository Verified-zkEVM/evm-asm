/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Loop

  Preloop+loop composition for n=2 (shift≠0 path).
  Composes:
  - Preloop: evm_div_n2_to_loopSetup_spec (base → base+448)
  - Loop: divK_loop_n2_unified_spec (base+448 → base+904)

  Follows the pattern of FullPathN3Loop.lean but for n=2.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop
import EvmAsm.Evm64.DivMod.LoopUnifiedN2

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address normalization lemmas for n=2 preloop+loop composition
-- Maps u_base(j)/q_addr(j) relative offsets to flat sp+signExtend12 offsets.
-- signExtend12/<<</>> → concrete values via simp, then bv_omega.
-- bv_addr only handles (a+k1)+k2=a+k3; these involve subtraction and shifts,
-- so bv_omega is required. Pattern matches FullPathN3Loop.lean:69.
-- ============================================================================

/-- signExtend12(4) - 2 = 2, for x1 register in loopSetupPost at n=2. -/
theorem x1_val_n2 : signExtend12 (4 : BitVec 12) - (2 : Word) = (2 : Word) := by decide

-- u_base(2) = sp + se(4056) - 16.  Offsets map to flat addresses:
-- u_base(2)+0     = sp+se(4040)  [u0 at iteration j=2]
-- u_base(2)-8     = sp+se(4032)  [u1]
-- u_base(2)-16    = sp+se(4024)  [u2]
-- u_base(2)-24    = sp+se(4016)  [u3]
-- u_base(2)-32    = sp+se(4008)  [u_top]

theorem n2_ub2_off0 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) =
    sp + signExtend12 4040 := by
  simp only [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (2 : Word) <<< 3 = (16 : Word) from by decide]; bv_omega
theorem n2_ub2_off4088 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    sp + signExtend12 4032 := by
  simp only [show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (2 : Word) <<< 3 = (16 : Word) from by decide]; bv_omega
theorem n2_ub2_off4080 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    sp + signExtend12 4024 := by
  simp only [show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (2 : Word) <<< 3 = (16 : Word) from by decide]; bv_omega
theorem n2_ub2_off4072 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    sp + signExtend12 4016 := by
  simp only [show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by decide,
    show signExtend12 (4016 : BitVec 12) = (18446744073709551536 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (2 : Word) <<< 3 = (16 : Word) from by decide]; bv_omega
theorem n2_ub2_off4064 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 =
    sp + signExtend12 4008 := by
  simp only [show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by decide,
    show signExtend12 (4008 : BitVec 12) = (18446744073709551528 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (2 : Word) <<< 3 = (16 : Word) from by decide]; bv_omega

-- u_base(1)+0 = sp+se(4048), already covered by n3_ub1_off0 (same addresses)
-- u_base(0)+0 = sp+se(4056), already covered by n3_ub0_off0

-- q_addr(j) = sp + se(4088) - j<<<3
theorem n2_qa2 (sp : Word) :
    sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4072 := by
  simp only [show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (2 : Word) <<< 3 = (16 : Word) from by decide]; bv_omega
-- n2_qa1 = n3_qa1 (same: sp + se(4088) - 8 = sp + se(4080))
-- n2_qa0 = n3_qa0 (same: sp + se(4088) - 0 = sp + se(4088))

-- div128 hi/lo addresses for j=2
theorem n2_uhi_2_addr (sp : Word) :
    sp + signExtend12 4056 - (2 + (2 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4024 := by
  simp only [show (2 + (2 : Word)) = (4 : Word) from by decide,
    show (4 : Word) <<< (3 : BitVec 6).toNat = (32 : Word) from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by decide]; bv_omega
theorem n2_ulo_2_addr (sp : Word) :
    (sp + signExtend12 4056 - (2 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4032 := by
  simp only [show (2 + (2 : Word)) = (4 : Word) from by decide,
    show (4 : Word) <<< (3 : BitVec 6).toNat = (32 : Word) from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by decide]; bv_omega

-- v[n-1] address for n=2: v[1] at sp + ((2:Word) + se(4095))<<<3 + se(32)
theorem n2_vtop_addr (sp : Word) :
    sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32 =
    sp + signExtend12 40 := by
  simp only [show (2 : Word) + signExtend12 (4095 : BitVec 12) = (1 : Word) from by decide,
    show (1 : Word) <<< (3 : BitVec 6).toNat = (8 : Word) from by decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega

-- div128 hi/lo addresses for j=1
theorem n2_uhi_1_addr (sp : Word) :
    sp + signExtend12 4056 - (1 + (2 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4032 := by
  simp only [show (1 + (2 : Word)) = (3 : Word) from by decide,
    show (3 : Word) <<< (3 : BitVec 6).toNat = (24 : Word) from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by decide]; bv_omega
theorem n2_ulo_1_addr (sp : Word) :
    (sp + signExtend12 4056 - (1 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4040 := by
  simp only [show (1 + (2 : Word)) = (3 : Word) from by decide,
    show (3 : Word) <<< (3 : BitVec 6).toNat = (24 : Word) from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by decide]; bv_omega

-- div128 hi/lo addresses for j=0
theorem n2_uhi_0_addr (sp : Word) :
    sp + signExtend12 4056 - (0 + (2 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4040 := by
  simp only [show (0 + (2 : Word)) = (2 : Word) from by decide,
    show (2 : Word) <<< (3 : BitVec 6).toNat = (16 : Word) from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by decide]; bv_omega
theorem n2_ulo_0_addr (sp : Word) :
    (sp + signExtend12 4056 - (0 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4048 := by
  simp only [show (0 + (2 : Word)) = (2 : Word) from by decide,
    show (2 : Word) <<< (3 : BitVec 6).toNat = (16 : Word) from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by decide]; bv_omega

-- ============================================================================
-- Lift unified n=2 loop from sharedDivModCode to divCode
-- ============================================================================

/-- Lift the unified n=2 3-iteration loop spec from sharedDivModCode to divCode. -/
theorem divK_loop_n2_unified_divCode (bltu_2 bltu_1 bltu_0 : Bool)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_1 u0_orig_0
     q2_old q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_2 : isValidDwordAccess (sp + signExtend12 4056 - (2 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu_2 : bltu_2 = BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1 v1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.2.1 v1) :
    cpsTriple (base + 448) (base + 904) (divCode base)
      (loopN2PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_1 u0_orig_0 q2_old q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN2UnifiedPost bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_1 u0_orig_0 ret_mem d_mem dlo_mem scratch_un0) :=
  cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_n2_unified_spec bltu_2 bltu_1 bltu_0
      sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig_1 u0_orig_0 q2_old q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_2 hv_ulo_2 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_2 hv_u1_2 hv_u2_2 hv_u3_2 hv_u4_2 hv_q2
      hv_uhi_1 hv_ulo_1 hv_u0_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
      hbltu_2 hbltu_1 hbltu_0)

-- ============================================================================
-- loopExitPostN2 at j=0: concrete address specialization
-- ============================================================================

/-- Specialize `loopExitPostN2` at `j=0`: all u_base/q_addr offsets become
    flat `sp + signExtend12 K` addresses. Uses the shared u_base_off*_j0 lemmas. -/
theorem loopExitPostN2_j0_eq (sp q_f c3 un0_f un1_f un2_f un3_f u4_f
    v0 v1 v2 v3 : Word) :
    loopExitPostN2 sp (0 : Word) q_f c3 un0_f un1_f un2_f un3_f u4_f v0 v1 v2 v3 =
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ signExtend12 4095) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ sp + signExtend12 4056) **
     (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
     (.x2 ↦ᵣ un3_f) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ un0_f) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ un1_f) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ un2_f) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ un3_f) **
     ((sp + signExtend12 4024) ↦ₘ u4_f) **
     ((sp + signExtend12 4088) ↦ₘ q_f)) := by
  simp only [loopExitPost_unfold]
  rw [u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
      u_base_off4072_j0, u_base_off4064_j0, u_base_j0, q_addr_j0]
  simp only [show (0 : Word) <<< (3 : BitVec 6).toNat = (0 : Word) from by decide]
  rw [show (0 : Word) + signExtend12 4095 = signExtend12 4095 from BitVec.zero_add _]

end EvmAsm.Evm64
