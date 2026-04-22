/-
  EvmAsm.Evm64.DivMod.Compose.ModEpilogue

  MOD mirror of the Denorm body composition from Epilogue.lean.
  Same code, same pre/postconditions, just modCode instead of divCode.
  Block 9 (denorm at base+904) is identical between divCode and modCode.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (bv64_4mul_3)

-- ============================================================================
-- Denorm code subsumption for modCode (block 9, skip 9 blocks)
-- ============================================================================

/-- Denorm code (block 9) is subsumed by modCode. -/
private theorem divK_denorm_code_sub_modCode {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + denormOff) divK_denorm) a = some i → (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Full Denorm (shift body only) for modCode: denormalize u[0..3] by right-shifting.
    base+904+16 → base+904+100 (21 instructions: ADDI+SUB + 3×merge + last).
    Used when shift≠0. The BEQ and LD are handled separately.
    Mirror of divK_denorm_body_spec from Epilogue.lean with modCode. -/
theorem mod_denorm_body_spec (sp u0 u1 u2 u3 v2 v5 v7 shift : Word) (base : Word) :
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
    let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
    let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
    let u3' := u3 >>> (shift.toNat % 64)
    cpsTriple (base + 916) (base + epilogueOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u3') ** (.x7 ↦ᵣ (u3 <<< (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
       ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3')) := by
  intro antiShift u0' u1' u2' u3'
  -- ADDI x2 x0 0 + SUB x2 x2 x6 (base+916 → base+924): compute antiShift
  have haddi := addi_x0_spec_gen .x2 v2 0 (base + 916) (by nofun)
  rw [show (base + 916 : Word) + 4 = base + 920 from by bv_addr] at haddi
  have haddie := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_modCode a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + 916) divK_denorm
        [.ADDI .x2 .x0 0] 2
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) haddi
  -- Frame ADDI with x12, x5, x7, x6, and all memory
  have haddief := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ shift) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) haddie
  have hsub := sub_spec_gen_rd_eq_rs1 .x2 .x6
    (signExtend12 (0 : BitVec 12)) shift (base + 920) (by nofun)
  rw [show (base + 920 : Word) + 4 = base + 924 from by bv_addr] at hsub
  have hsube := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_modCode a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + denormOff) divK_denorm 3
          (by decide) (by decide)
        rw [bv64_4mul_3,
            show (base + denormOff : Word) + 12 = base + 920 from by bv_addr] at hlookup
        exact hlookup) a i h)) hsub
  -- Frame SUB with x12, x5, x7, x0, and all memory
  have hsubf := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hsube
  have h_anti := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) haddief hsubf
  -- Merge u[0] with u[1] (base+924 → base+948)
  have hm0 := divK_denorm_merge_spec 4056 4048 sp u0 u1 v5 v7 shift antiShift (base + 924)
  rw [show (base + 924 : Word) + 24 = base + 948 from by bv_addr] at hm0
  have hm0e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_modCode a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + 924) divK_denorm
        (divK_denorm_merge_prog 4056 4048) 4
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm0
  have hm0ef := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hm0e
  have h_m0 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_anti hm0ef
  -- Merge u[1] with u[2] (base+948 → base+972)
  have hm1 := divK_denorm_merge_spec 4048 4040 sp u1 u2
    u0' (u1 <<< (antiShift.toNat % 64)) shift antiShift (base + 948)
  rw [show (base + 948 : Word) + 24 = base + 972 from by bv_addr] at hm1
  have hm1e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_modCode a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + 948) divK_denorm
        (divK_denorm_merge_prog 4048 4040) 10
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm1
  have hm1ef := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hm1e
  have h_m1 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_m0 hm1ef
  -- Merge u[2] with u[3] (base+972 → base+996)
  have hm2 := divK_denorm_merge_spec 4040 4032 sp u2 u3
    u1' (u2 <<< (antiShift.toNat % 64)) shift antiShift (base + 972)
  rw [show (base + 972 : Word) + 24 = base + 996 from by bv_addr] at hm2
  have hm2e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_modCode a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + 972) divK_denorm
        (divK_denorm_merge_prog 4040 4032) 16
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm2
  have hm2ef := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1'))
    (by pcFree) hm2e
  have h_m2 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_m1 hm2ef
  -- Last u[3] (base+996 → base+1008)
  have hl := divK_denorm_last_spec 4032 sp u3 u2' shift (base + 996)
  rw [show (base + 996 : Word) + 12 = base + epilogueOff from by bv_addr] at hl
  have hle := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_modCode a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + 996) divK_denorm
        (divK_denorm_last_prog 4032) 22
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hl
  have hlef := cpsTriple_frameR
    ((.x7 ↦ᵣ (u3 <<< (antiShift.toNat % 64))) ** (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
     ((sp + signExtend12 4040) ↦ₘ u2'))
    (by pcFree) hle
  have h_all := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_m2 hlef
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h_all

end EvmAsm.Evm64
