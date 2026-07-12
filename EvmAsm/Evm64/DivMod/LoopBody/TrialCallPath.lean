/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialCallPath

  V5 trial-call path specs; legacy and V4 declarations live in TrialCallPathBase.
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCallPathBase
import EvmAsm.Evm64.DivMod.Compose.Div128V5

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

private theorem lb_jal_target {base : Word} :
    (base + trialJalOff : Word) + signExtend21 (560 : BitVec 21) = base + div128Off := by
  rv64_addr

private theorem lb_jal_ret {base : Word} :
    (base + trialJalOff : Word) + 4 = base + div128CallRetOff := by
  bv_addr

/-- Trial call path over `sharedDivModCode_v5`: JAL x2 560 (instr [16]) +
    the v5 div128 subroutine, with exact x1 framing and the additional v5
    scratch cell threaded explicitly. -/
theorem divK_trial_call_path_v5_spec_within_exact_x1
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v1Old v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 84 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCode_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ v1Old))
      (div128V5SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
        regOwn .x1) := by
  have J := jal_spec_within .x2 v2Old (560 : BitVec 21) (base + trialJalOff) (by nofun)
  rw [lb_jal_target, lb_jal_ret] at J
  have Je := cpsTripleWithin_extend_code (hmono :=
    lb_sub_v5 16 _ _ (by decide) (by bv_addr) (by decide)) J
  have D := div128_v5_spec_shared sp (base + div128CallRetOff) vTop uLo uHi base
    j vtopBase v11Old retMem dMem dloMem un0Mem scratchMem
    halign
  have Df := cpsTripleWithin_frameR (.x1 ↦ᵣ v1Old) (by pcFree) D
  have Jf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ v1Old) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
     (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem) **
     (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) Je
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) Jf Df
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      apply sepConj_mono_right (regIs_implies_regOwn .x1) h
      xperm_hyp hq)
    full

/-- Trial call path over `sharedDivModCode_v5`, with `x1` existentially
    owned. -/
theorem divK_trial_call_path_v5_spec_within
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 84 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCode_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** regOwn .x1)
      (div128V5SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
        regOwn .x1) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v1Old
  exact divK_trial_call_path_v5_spec_within_exact_x1
    sp j uLo uHi vTop vtopBase base v1Old v2Old v11Old
    retMem dMem dloMem un0Mem scratchMem halign

/-- Trial call path over `sharedDivModCodeNoNop_v5`: JAL x2 560 (instr [16])
    plus the v5 div128 subroutine, preserving the framed concrete x1 value
    and threading the additional v5 scratch cell explicitly. -/
theorem divK_trial_call_path_v5_spec_within_noNop_preserving_x1
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v1Old v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 84 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ v1Old))
      (div128V5SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
        (.x1 ↦ᵣ v1Old)) := by
  have J := jal_spec_within .x2 v2Old (560 : BitVec 21) (base + trialJalOff) (by nofun)
  rw [lb_jal_target, lb_jal_ret] at J
  have Je := cpsTripleWithin_extend_code (hmono :=
    lb_sub_noNop_v5 16 _ _ (by decide) (by bv_addr) (by decide)) J
  have D := div128_v5_spec_shared_noNop sp (base + div128CallRetOff) vTop uLo uHi base
    j vtopBase v11Old retMem dMem dloMem un0Mem scratchMem
    halign
  have Df := cpsTripleWithin_frameR (.x1 ↦ᵣ v1Old) (by pcFree) D
  have Jf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ v1Old) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
     (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem) **
     (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) Je
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) Jf Df
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

/-- Trial call path over `sharedDivModCodeNoNop_v5`: JAL x2 560 (instr [16])
    plus the v5 div128 subroutine, with exact x1 framing and the additional
    v5 scratch cell threaded explicitly. -/
theorem divK_trial_call_path_v5_spec_within_noNop_exact_x1
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v1Old v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 84 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ v1Old))
      (div128V5SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
        regOwn .x1) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      apply sepConj_mono_right (regIs_implies_regOwn .x1) h
      xperm_hyp hq)
    (divK_trial_call_path_v5_spec_within_noNop_preserving_x1
      sp j uLo uHi vTop vtopBase base v1Old v2Old v11Old
      retMem dMem dloMem un0Mem scratchMem halign)

/-- Trial call path over `sharedDivModCodeNoNop_v5`, with `x1`
    existentially owned. -/
theorem divK_trial_call_path_v5_spec_within_noNop
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 84 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** regOwn .x1)
      (div128V5SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
        regOwn .x1) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v1Old
  exact divK_trial_call_path_v5_spec_within_noNop_exact_x1
    sp j uLo uHi vTop vtopBase base v1Old v2Old v11Old
    retMem dMem dloMem un0Mem scratchMem halign

end EvmAsm.Evm64
