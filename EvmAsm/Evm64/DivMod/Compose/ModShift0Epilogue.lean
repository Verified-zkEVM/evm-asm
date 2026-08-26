/-
  EvmAsm.Evm64.DivMod.Compose.ModShift0Epilogue

  MOD shift=0 post-loop composition split out of FullPath.lean.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPath

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Denorm code (block 9) is subsumed by modCode.
    Re-proved here because the version in ModEpilogue.lean is private. -/
private theorem divK_denorm_code_sub_modCode' (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + denormOff) divK_denorm) a = some i → (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left

theorem evm_mod_shift0_epilogue_spec_within (sp base : Word)
    (u0 u1 u2 u3 shift v2 v5 v6 v7 v10 : Word)
    (m0 m8 m16 m24 : Word)
    (hshift_z : shift = 0) :
    cpsTripleWithin 12 (base + denormOff) (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0) ** (.x6 ↦ᵣ u1) ** (.x7 ↦ᵣ u2) **
       (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ u3) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ u0) ** ((sp + 40) ↦ₘ u1) **
       ((sp + 48) ↦ₘ u2) ** ((sp + 56) ↦ₘ u3)) := by
  have hld := ld_spec_gen_within .x6 .x12 sp v6 shift (3992 : BitVec 12) (base + denormOff) (by nofun)
  have hlde := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact divK_denorm_code_sub_modCode' base a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff) divK_denorm
        [.LD .x6 .x12 3992] 0 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hld
  have hbeq := beq_spec_gen_within .x6 .x0 (96 : BitVec 13) shift (0 : Word) (base + denormOff + 4)
  rw [show (base + denormOff + 4 : Word) + signExtend13 (96 : BitVec 13) = base + epilogueOff from by rv64_addr,
      show (base + denormOff + 4 : Word) + 4 = base + denormOff + 8 from by bv_addr] at hbeq
  have hbeqe := cpsBranchWithin_extend_code (hmono := by
    intro a i h
    exact divK_denorm_code_sub_modCode' base a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 4) divK_denorm
        [.BEQ .x6 .x0 96] 1 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hbeq
  have hbeq_exit := cpsBranchWithin_takenStripPure2 hbeqe
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hshift_z ((sepConj_pure_right _).mp h_rest).2)
  have hldf := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10))
    (by pcFree) hlde
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq_exit
  have hPre := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hldf hbeqf
  have hPreF := cpsTripleWithin_frameR
    (((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hPre
  have hEpi := divK_mod_epilogue_spec_within sp base u0 u1 u2 u3
    v5 shift v7 v10 m0 m8 m16 m24
  have hEpiF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hEpi
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPreF hEpiF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Evm64
