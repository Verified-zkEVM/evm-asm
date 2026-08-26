/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialCallFullV5NamedExactX1

  Exact-x1 ("preserving the concrete caller return address") variant of the v5
  trial-call-full brick, with the compact NAMED post.  Mirror of
  `divK_trial_call_full_v5_spec_within_noNop` / `..._named_spec_within_noNop`
  (TrialCallFullV5 / TrialCallFullV5Named) but keeping `.x1 ↦ᵣ raVal` instead of
  collapsing it to `regOwn .x1` — needed by the n=2 (and n≥2) call-path loop
  bodies that thread the concrete return address through the loop-back.  The
  v5 trial-call-path already has the preserving-x1 form
  (`divK_trial_call_path_v5_spec_within_noNop_exact_x1`, #7210), so the only
  change from the regOwn version is dropping the
  `cpsTripleWithin_of_forall_regIs_to_regOwn` step and threading `raVal`.
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.TrialCallFullV5Named

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Raw exact-x1 v5 trial-call-full post (mirror of `divKTrialCallFullPostV5`
    with `.x1 ↦ᵣ raVal` in place of `regOwn .x1`). -/
def divKTrialCallFullPostV5ExactX1 (sp j n uHi uLo vTop base scratchMem raVal : Word) : Assertion :=
  let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
  let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
  div128V5SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
  (.x1 ↦ᵣ raVal) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
  (vtopBase + signExtend12 32 ↦ₘ vTop)

/-- Compact NAMED exact-x1 v5 trial-call-full post (mirror of
    `divKTrialCallFullPostV5Named` with `.x1 ↦ᵣ raVal`). -/
def divKTrialCallFullPostV5NamedExactX1
    (sp j n uHi uLo vTop base scratchMem raVal : Word) : Assertion :=
  let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
  let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV5DHi vTop
  let dLo := divKTrialCallV5DLo vTop
  let un0Div := divKTrialCallV5Un0 uLo
  let q1'' := divKTrialCallV5Q1dd uHi uLo vTop
  let q0'' := divKTrialCallV5Q0dd uHi uLo vTop
  let x7Exit := divKTrialCallV5X7Exit uHi uLo vTop
  let x9Exit := divKTrialCallV5X9Exit uHi uLo vTop
  let q := divKTrialCallV5QHat uHi uLo vTop
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ x9Exit) ** (.x1 ↦ᵣ raVal) **
  (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) **
  (.x7 ↦ᵣ x7Exit) ** (.x10 ↦ᵣ q1'') ** (.x11 ↦ᵣ q) **
  (.x2 ↦ᵣ (base + div128CallRetOff)) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
  (vtopBase + signExtend12 32 ↦ₘ vTop) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ vTop) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0Div) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut uHi uLo vTop scratchMem)

/-- Weaken the raw exact-x1 post to the compact NAMED exact-x1 post (same
    register-name bridge as `divKTrialCallFullPostV5_imp_named`, with the
    `.x1 ↦ᵣ raVal` atom riding along). -/
theorem divKTrialCallFullPostV5ExactX1_imp_named
    (sp j n uHi uLo vTop base scratchMem raVal : Word) :
    ∀ h, divKTrialCallFullPostV5ExactX1 sp j n uHi uLo vTop base scratchMem raVal h →
      divKTrialCallFullPostV5NamedExactX1 sp j n uHi uLo vTop base scratchMem raVal h := by
  intro h hq
  unfold divKTrialCallFullPostV5ExactX1 div128V5SpecPost at hq
  unfold divKTrialCallFullPostV5NamedExactX1
  rw [← div128V5_q1Final_eq_Q1dd uHi uLo vTop,
      ← div128V5_q0Final_eq_Q0dd uHi uLo vTop,
      div128V5_x7Exit_eq uHi uLo vTop,
      div128V5_x9Exit_eq uHi uLo vTop,
      ← div128V5CodeQuot_eq_divKTrialCallV5QHat uHi uLo vTop]
  unfold divKTrialCallV5ScratchOut
  rw [← div128V5_rhat2c_eq uHi uLo vTop, ← div128V5_un21_eq uHi uLo vTop]
  unfold div128V5CodeQuot divKTrialCallV5DHi divKTrialCallV5DLo
    divKTrialCallV5Un0 divKTrialCallV5Un1
  xperm_hyp hq

/-- Exact-x1 raw v5 trial-call-full path: mirror of
    `divK_trial_call_full_v5_spec_within_noNop` keeping `.x1 ↦ᵣ raVal`. -/
theorem divK_trial_call_full_v5_spec_within_noNop_exact_x1
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem raVal : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 98 (base + loopBodyOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ raVal))
      (divKTrialCallFullPostV5ExactX1 sp j n uHi uLo vTop base scratchMem raVal) := by
  intro uAddr vtopBase
  have STL := divK_save_trial_load_v5_spec_within_noNop
    sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop base
  dsimp only [] at STL
  have hbltu_raw := bltu_spec_gen_within .x7 .x10 (12 : BitVec 13) uHi vTop (base + trialCallOff)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop_v5 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  have taken := cpsBranchWithin_takenPath hbltu_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure hbltu)
  have taken_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) taken
  have TCP := divK_trial_call_path_v5_spec_within_noNop_preserving_x1
    sp j uLo uHi vTop vtopBase base raVal v2Old v11Old
    retMem dMem dloMem un0Mem scratchMem halign
  have STLf := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raVal) ** (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) STL
  have taken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ raVal) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) taken_clean
  have TCPf := cpsTripleWithin_frameR
    ((sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) TCP
  have STLf_taken_clean := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf taken_framed
  have STLf_taken_scratch := cpsTripleWithin_frameR
    (sp + signExtend12 3936 ↦ₘ scratchMem)
    (by pcFree) STLf_taken_clean
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf_taken_scratch TCPf
  unfold divKTrialCallFullPostV5ExactX1
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

/-- Exact-x1 v5 trial-call-full path with the **compact NAMED post**
    (`divKTrialCallFullPostV5NamedExactX1`).  The exact-x1 analog of
    `divK_trial_call_full_v5_named_spec_within_noNop`. -/
theorem divK_trial_call_full_v5_named_spec_within_noNop_exact_x1
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem raVal : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 98 (base + loopBodyOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ raVal))
      (divKTrialCallFullPostV5NamedExactX1 sp j n uHi uLo vTop base scratchMem raVal) := by
  intro uAddr vtopBase
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (divKTrialCallFullPostV5ExactX1_imp_named sp j n uHi uLo vTop base scratchMem raVal)
    (divK_trial_call_full_v5_spec_within_noNop_exact_x1
      sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop
      retMem dMem dloMem un0Mem scratchMem raVal base halign hbltu)

end EvmAsm.Evm64
