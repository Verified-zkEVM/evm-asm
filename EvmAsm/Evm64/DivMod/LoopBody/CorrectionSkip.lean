/-
  EvmAsm.Evm64.DivMod.LoopBody.CorrectionSkip

  Extracted from `LoopBody.lean` (Section 6a).

  Correction skip spec: when mulsub borrow=0, BEQ at instr [70] is taken
  → jump to base+884. No addback. 1 instruction at base+728.

  Uses public helpers from `LoopBody.lean`:
  - `lb_sub`, `lb_beq_taken`, `lb_beq_ntaken` (now public, made
    non-`private` for this split).
-/

import EvmAsm.Evm64.DivMod.LoopBody

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Correction skip: when borrow=0, BEQ taken → jump to base+884. No addback.
    1 instruction. All registers and memory unchanged. -/
theorem divK_correction_skip_spec_within
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5Old v2Old : Word) (base : Word) :
    cpsTripleWithin 1 (base + correctionSkipBeqOff) (base + storeLoopOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4)) := by
  -- BEQ x7 x0 156 at base + correctionSkipBeqOff with x7=0, x0=0
  have hbeq := beq_spec_gen_within .x7 .x0 (156 : BitVec 13) (0 : Word) 0 (base + correctionSkipBeqOff)
  rw [lb_beq_taken, lb_beq_ntaken] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub 70 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  -- Eliminate not-taken path (⌜0 ≠ 0⌝ is False)
  have skip := cpsBranchWithin_takenPath hbeq_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure rfl)
  -- Strip pure fact from taken postcondition
  have skip_clean : cpsTripleWithin 1 (base + correctionSkipBeqOff) (base + storeLoopOff) (sharedDivModCode base)
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
      skip
  -- Frame with all other state and permute
  have skip_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) **
     (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ u4))
    (by pcFree) skip_clean
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    skip_framed

/-- Correction skip: when borrow=0, BEQ taken → jump to base+884. No addback.
    1 instruction. All registers and memory unchanged. -/

theorem divK_correction_skip_v2_spec_within
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5Old v2Old : Word) (base : Word) :
    cpsTripleWithin 1 (base + correctionSkipBeqOff) (base + storeLoopOff) (sharedDivModCode_v2 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4)) := by
  have hbeq := beq_spec_gen_within .x7 .x0 (156 : BitVec 13) (0 : Word) 0 (base + correctionSkipBeqOff)
  rw [lb_beq_taken, lb_beq_ntaken] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_v2 70 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have skip := cpsBranchWithin_takenPath hbeq_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure rfl)
  have skip_clean : cpsTripleWithin 1 (base + correctionSkipBeqOff) (base + storeLoopOff) (sharedDivModCode_v2 base)
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
      skip
  have skip_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) **
     (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ u4))
    (by pcFree) skip_clean
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    skip_framed

end EvmAsm.Evm64
