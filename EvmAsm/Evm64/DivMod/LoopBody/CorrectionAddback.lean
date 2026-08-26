/-
  EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddback

  Named-postcondition wrappers for `divK_correction_addback_spec_within` and
  `divK_correction_addback_spec_within_noNop`. These expose the correction
  addback spec with 0 statement lets via `addbackFullPost`.
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.DoubleAddbackBeq

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Correction addback over `sharedDivModCodeNoNop_v4`, with the addback
    result hidden behind `addbackFullPost`. -/
theorem divK_correction_addback_named_v4_spec_within_noNop
    (sp uBase borrow qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5Old v2Old : Word) (base : Word)
    (hb : borrow ≠ (0 : Word)) :
    cpsTripleWithin 38 (base + correctionSkipBeqOff) (base + addbackBeqOff) (sharedDivModCodeNoNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ borrow) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4))
      (addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4) := by
  have hbeq := beq_spec_gen_within .x7 .x0 (156 : BitVec 13) borrow 0 (base + correctionSkipBeqOff)
  rw [lb_beq_taken, lb_beq_ntaken] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop_v4 70 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have ntaken := cpsBranchWithin_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hb hpure)
  have ntaken_clean : cpsTripleWithin 1 (base + correctionSkipBeqOff) (base + addbackInitOff) (sharedDivModCodeNoNop_v4 base)
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
      ntaken
  have ntaken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) **
     (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ u4))
    (by pcFree) ntaken_clean
  have AB := divK_addback_full_named_v4_spec_within_noNop sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
    borrow v5Old v2Old base
  seqFrame ntaken_framed AB
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by exact hq)
    ntaken_framedAB

end EvmAsm.Evm64
