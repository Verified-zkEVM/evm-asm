/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1Loop

  Preloop+loop composition for n=1 (shift≠0 path).
  Composes:
  - Preloop: evm_div_n1_to_loopSetup_spec (base → base+448)
  - Loop: divK_loop_n1_unified_spec (base+448 → base+904)

  Follows the pattern of FullPathN2Loop.lean but for n=1.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Loop
import EvmAsm.Evm64.DivMod.LoopUnifiedN1

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (bv6_toNat_3 word_shl3_0)

-- ============================================================================
-- Address normalization lemmas for n=1 preloop+loop composition
-- Maps uBase(j)/qAddr(j) relative offsets to flat sp+signExtend12 offsets.
-- signExtend12/<<</>> → concrete values via simp, then bv_omega.
-- bv_addr only handles (a+k1)+k2=a+k3; these involve subtraction and shifts,
-- so bv_omega is required. Pattern matches FullPathN2Loop.lean.
-- ============================================================================

/-- signExtend12(4) - 1 = 3, for x1 register in loopSetupPost at n=1. -/
theorem x1_val_n1 : signExtend12 (4 : BitVec 12) - (1 : Word) = (3 : Word) := by decide

-- uBase(3) = sp + se(4056) - 24.  Offsets map to flat addresses:
-- uBase(3)+0     = sp+se(4032)  [u0 at iteration j=3]
-- uBase(3)-8     = sp+se(4024)  [u1]
-- uBase(3)-16    = sp+se(4016)  [u2]
-- uBase(3)-24    = sp+se(4008)  [u3]
-- uBase(3)-32    = sp+se(4000)  [uTop]

theorem n1_ub3_off0 (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) =
    sp + signExtend12 4032 := by
  divmod_addr
theorem n1_ub3_off4088 (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    sp + signExtend12 4024 := by
  divmod_addr
theorem n1_ub3_off4080 (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    sp + signExtend12 4016 := by
  divmod_addr
theorem n1_ub3_off4072 (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    sp + signExtend12 4008 := by
  divmod_addr
theorem n1_ub3_off4064 (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 =
    sp + signExtend12 4000 := by
  divmod_addr

-- uBase(2)+0 = sp+se(4040), already covered by n2_ub2_off0 (same addresses)
-- uBase(1)+0 = sp+se(4048), already covered by n3_ub1_off0
-- uBase(0)+0 = sp+se(4056), already covered by n3_ub0_off0

-- qAddr(j) = sp + se(4088) - j<<<3
theorem n1_qa3 (sp : Word) :
    sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4064 := by
  divmod_addr
-- n1_qa2 = n2_qa2 (same: sp + se(4088) - 16 = sp + se(4072))
-- n1_qa1 = n3_qa1 (same: sp + se(4088) - 8 = sp + se(4080))
-- n1_qa0 = n3_qa0 (same: sp + se(4088) - 0 = sp + se(4088))

-- ============================================================================
-- loopExitPostN1 at j=0: concrete address specialization
-- ============================================================================

/-- Specialize `loopExitPostN1` at `j=0`: all uBase/qAddr offsets become
    flat `sp + signExtend12 K` addresses. Uses the shared u_base_off*_j0 lemmas. -/
theorem loopExitPostN1_j0_eq (sp q_f c3 un0F un1F un2F un3F u4F
    v0 v1 v2 v3 : Word) :
    loopExitPostN1 sp (0 : Word) q_f c3 un0F un1F un2F un3F u4F v0 v1 v2 v3 =
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ signExtend12 4095) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ sp + signExtend12 4056) **
     (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
     (.x2 ↦ᵣ un3F) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ un0F) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ un1F) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ un2F) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ un3F) **
     ((sp + signExtend12 4024) ↦ₘ u4F) **
     ((sp + signExtend12 4088) ↦ₘ q_f)) := by
  simp only [loopExitPost_unfold]
  rw [u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
      u_base_off4072_j0, u_base_off4064_j0, u_base_j0, q_addr_j0]
  simp only [bv6_toNat_3, word_shl3_0]
  rw [show (0 : Word) + signExtend12 4095 = signExtend12 4095 from BitVec.zero_add _]

-- ============================================================================
-- Lift unified n=1  loop from sharedDivModCode to divCode
-- ============================================================================

/-- Lift the unified n=1 4-iteration  loop spec from sharedDivModCode to divCode. -/
theorem divK_loop_n1_unified_divCode (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_2 u0_orig_1 u0_orig_0
     q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_3 : bltu_3 = BitVec.ult u1 v0)
    (hbltu_2 : bltu_2 = BitVec.ult (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (divCode base)
      (loopN1PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) :=
  cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_n1_unified_spec bltu_3 bltu_2 bltu_1 bltu_0
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2)

end EvmAsm.Evm64
