/-
  EvmAsm.Evm64.DivMod.LoopIterN1.NoX1ChainV5

  x1-PRESERVING (callable-ready) twins of the v5 n=1 ALL-CALL loop chain:
  trial-call-full → skip loop bodies → iteration-ready bodies → iter10 →
  iter210 → unified → at-shape.

  The bundled v5 chain (`loopN1UnifiedPreV5`/`loopN1UnifiedPostV5` etc.) carries
  `regOwn .x1`, which *discards* the concrete return address a callable must
  preserve (`raVal` cannot be recovered from ownership).  Since x1 appears in NO
  instruction of the v5 div body (the loop counter is x9, div128's link register
  is x2), every proof below is the bundled proof with the x1 atom kept CONCRETE
  (`.x1 ↦ᵣ x1Val` framed through) instead of owned.  The `NoX1` defs are the
  bundled defs minus the `regOwn .x1` atom (mirroring the existing
  `loopN1PreWithScratchNoX1` family, LoopDefs/Bundle.lean); the `_preserving_x1`
  theorems conjoin `(.x1 ↦ᵣ x1Val)` outside them.

  This is the loop core of the n=1 v5 callable exact-frame lane
  (`evm_div_callable_v5` / SDIV `.proven` track); mirror of how the n=2 lane
  threads x1 (`loopN2UnifiedPostV5NoX1` + `N2V5CallableExact`).
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.LoopAtShapeV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Level 1: trial-call-full (raw post), x1-preserving
-- ============================================================================

/-- `divKTrialCallFullPostV5` minus the `regOwn .x1` atom. -/
def divKTrialCallFullPostV5NoX1 (sp j n uHi uLo vTop base scratchMem : Word) : Assertion :=
  let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
  let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
  div128V5SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
  (vtopBase + signExtend12 32 ↦ₘ vTop)

/-- x1-preserving twin of `divK_trial_call_full_v5_spec_within_noNop`: the
    concrete `x1Val` is framed through (the trial call path links via x2). -/
theorem divK_trial_call_full_v5_spec_within_noNop_preserving_x1
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop x1Val : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
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
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ x1Val))
      (divKTrialCallFullPostV5NoX1 sp j n uHi uLo vTop base scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
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
    sp j uLo uHi vTop vtopBase base x1Val v2Old v11Old
    retMem dMem dloMem un0Mem scratchMem halign
  have STLf := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ x1Val) ** (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) STL
  have taken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ x1Val) **
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
  unfold divKTrialCallFullPostV5NoX1
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

-- ============================================================================
-- Level 2: trial-call-full (compact NAMED post), x1-preserving
-- ============================================================================

/-- `divKTrialCallFullPostV5Named` minus the `regOwn .x1` atom. -/
def divKTrialCallFullPostV5NamedNoX1
    (sp j n uHi uLo vTop base scratchMem : Word) : Assertion :=
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
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ x9Exit) **
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

/-- Weaken the raw x1-free trial-call-full post to the compact NAMED x1-free
    post (twin of `divKTrialCallFullPostV5_imp_named`). -/
theorem divKTrialCallFullPostV5NoX1_imp_named
    (sp j n uHi uLo vTop base scratchMem : Word) :
    ∀ h, divKTrialCallFullPostV5NoX1 sp j n uHi uLo vTop base scratchMem h →
      divKTrialCallFullPostV5NamedNoX1 sp j n uHi uLo vTop base scratchMem h := by
  intro h hq
  unfold divKTrialCallFullPostV5NoX1 div128V5SpecPost at hq
  unfold divKTrialCallFullPostV5NamedNoX1
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

/-- x1-preserving twin of `divK_trial_call_full_v5_named_spec_within_noNop`. -/
theorem divK_trial_call_full_v5_named_spec_within_noNop_preserving_x1
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop x1Val : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
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
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ x1Val))
      (divKTrialCallFullPostV5NamedNoX1 sp j n uHi uLo vTop base scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  intro uAddr vtopBase
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => sepConj_mono_left
      (divKTrialCallFullPostV5NoX1_imp_named sp j n uHi uLo vTop base scratchMem) h hq)
    (divK_trial_call_full_v5_spec_within_noNop_preserving_x1
      sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop x1Val
      retMem dMem dloMem un0Mem scratchMem base halign hbltu)

-- ============================================================================
-- Level 3: call+skip loop bodies (j=0 and j>0), x1-preserving
-- ============================================================================

/-- `loopBodyN1CallSkipJ0PostV5` minus the `regOwn .x1` atom. -/
@[irreducible]
def loopBodyN1CallSkipJ0PostV5NoX1
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV5DLo v0
  let div_un0 := divKTrialCallV5Un0 u0
  let qHat := divKTrialCallV5QHat u1 u0 v0
  loopBodyN1SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut u1 u0 v0 scratchMem)

/-- x1-preserving twin of `divK_loop_body_n1_call_skip_j0_v5_spec_within_noNop`. -/
theorem divK_loop_body_n1_call_skip_j0_v5_spec_within_noNop_preserving_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld x1Val : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
       (.x1 ↦ᵣ x1Val))
      (loopBodyN1CallSkipJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  unfold loopBodyN1CallSkipJ0PreV4NoX1
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV5DHi v0
  let dLo := divKTrialCallV5DLo v0
  let div_un0 := divKTrialCallV5Un0 u0
  let q1'' := divKTrialCallV5Q1dd u1 u0 v0
  let q0'' := divKTrialCallV5Q0dd u1 u0 v0
  let x7Exit := divKTrialCallV5X7Exit u1 u0 v0
  let x9Exit := divKTrialCallV5X9Exit u1 u0 v0
  let qHat := divKTrialCallV5QHat u1 u0 v0
  let scratchOut := divKTrialCallV5ScratchOut u1 u0 v0 scratchMem
  have TF := divK_trial_call_full_v5_named_spec_within_noNop_preserving_x1 sp (0 : Word) (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 x1Val retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV5NamedNoX1 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  have MCS0 := divK_mulsub_correction_skip_v5_spec_within_noNop sp qHat (0 : Word)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
    hborrow
  unfold divKMulsubCorrectionSkipPre at MCS0
  unfold n4McaNamedSkipPost at MCS0
  unfold mulsubN4 at MCS0
  dsimp only [] at MCS0
  have MCS0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ x1Val))
    (by pcFree) MCS0
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  have SL := divK_store_loop_j0_v5_spec_within_noNop sp qHat u4_new (0 : Word) qOld base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCS0f
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ x1Val))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallSkipJ0PostV5NoX1
      unfold loopBodyN1SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- `loopBodyN1CallSkipJgt0PostV5` minus the `regOwn .x1` atom. -/
def loopBodyN1CallSkipJgt0PostV5NoX1
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV5DLo v0
  let div_un0 := divKTrialCallV5Un0 u0
  let qHat := divKTrialCallV5QHat u1 u0 v0
  let scratchOut := divKTrialCallV5ScratchOut u1 u0 v0 scratchMem
  loopBodyN1SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut)

/-- x1-preserving twin of `divK_loop_body_n1_call_skip_jgt0_v5_spec_within_noNop`. -/
theorem divK_loop_body_n1_call_skip_jgt0_v5_spec_within_noNop_preserving_x1 (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld x1Val : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsTripleWithin 158 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val))
      (loopBodyN1CallSkipJgt0PostV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  intro uBase qAddr
  let dHi := divKTrialCallV5DHi v0
  let dLo := divKTrialCallV5DLo v0
  let div_un0 := divKTrialCallV5Un0 u0
  let q1'' := divKTrialCallV5Q1dd u1 u0 v0
  let q0'' := divKTrialCallV5Q0dd u1 u0 v0
  let x7Exit := divKTrialCallV5X7Exit u1 u0 v0
  let x9Exit := divKTrialCallV5X9Exit u1 u0 v0
  let qHat := divKTrialCallV5QHat u1 u0 v0
  let scratchOut := divKTrialCallV5ScratchOut u1 u0 v0 scratchMem
  have TF := divK_trial_call_full_v5_named_spec_within_noNop_preserving_x1 sp j (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 x1Val retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV5NamedNoX1 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  have MCS0 := divK_mulsub_correction_skip_v5_spec_within_noNop sp qHat j
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
    hborrow
  unfold divKMulsubCorrectionSkipPre at MCS0
  unfold n4McaNamedSkipPost at MCS0
  unfold mulsubN4 at MCS0
  dsimp only [] at MCS0
  have MCS0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ x1Val))
    (by pcFree) MCS0
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  have SL := divK_store_loop_jgt0_v5_spec_within_noNop sp j qHat u4_new (0 : Word) qOld base hpos
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCS0f
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ x1Val))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallSkipJgt0PostV5NoX1
      unfold loopBodyN1SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- Level 4: iteration-ready bodies, x1-preserving
-- ============================================================================

/-- `loopIterPostN1CallV5` minus the `regOwn .x1` atom. -/
@[irreducible] def loopIterPostN1CallV5NoX1
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let qHat := div128Quot_v5 u1 u0 v0
  let r := iterWithDoubleAddback qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let c3 := (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN1 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ divKTrialCallV5DLo v0) **
  (sp + signExtend12 3944 ↦ₘ divKTrialCallV5Un0 u0) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut u1 u0 v0 scratchMem)

/-- Skip bridge (j=0), x1-free twin of `loopIterPostN1CallV5_j0_skip`. -/
theorem loopIterPostN1CallV5NoX1_j0_skip
    {sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word}
    (hb : ¬BitVec.ult uTop
      (mulsubN4_c3 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN1CallSkipJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    loopIterPostN1CallV5NoX1 sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem := by
  unfold loopBodyN1CallSkipJ0PostV5NoX1 loopIterPostN1CallV5NoX1
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  delta loopBodyN1SkipPost loopBodySkipPost loopExitPostN1 loopExitPost
    iterWithDoubleAddback
  unfold mulsubN4_c3 at hb
  simp only [if_neg hb]

/-- Skip bridge (j>0), x1-free twin of `loopIterPostN1CallV5_jgt0_skip`. -/
theorem loopIterPostN1CallV5NoX1_jgt0_skip
    {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word}
    (hb : ¬BitVec.ult uTop
      (mulsubN4_c3 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN1CallSkipJgt0PostV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    loopIterPostN1CallV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem := by
  unfold loopBodyN1CallSkipJgt0PostV5NoX1 loopIterPostN1CallV5NoX1
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  delta loopBodyN1SkipPost loopBodySkipPost loopExitPostN1 loopExitPost
    iterWithDoubleAddback
  unfold mulsubN4_c3 at hb
  simp only [if_neg hb]

/-- From the v5 no-borrow hypothesis, the mulsub-c3 skip guard holds (local
    copy of the private `v5_skip_guard_of_noBorrow`, IterBodyV5). -/
private theorem v5_skip_guard_of_noBorrow' {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    ¬BitVec.ult uTop (mulsubN4_c3 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3) := by
  intro hult
  unfold mulsubN4NoBorrow at hborrow
  simp_rw [divKTrialCallV5QHat_eq_div128Quot_v5] at hborrow
  unfold mulsubN4_c3 at hult
  rw [if_pos hult] at hborrow
  exact absurd hborrow (by decide)

/-- x1-preserving twin of `divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop`. -/
theorem divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop_preserving_x1 (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld x1Val : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsTripleWithin 158 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val))
      (loopIterPostN1CallV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  intro uBase qAddr
  have J := divK_loop_body_n1_call_skip_jgt0_v5_spec_within_noNop_preserving_x1 j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld x1Val retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu hborrow
  intro_lets at J
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rw [← loopIterPostN1CallV5NoX1_jgt0_skip (v5_skip_guard_of_noBorrow' hborrow)]
      exact hp)
    J

/-- x1-preserving twin of `divK_loop_body_n1_call_iter_j0_v5_spec_within_noNop`. -/
theorem divK_loop_body_n1_call_iter_j0_v5_spec_within_noNop_preserving_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld x1Val : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
       (.x1 ↦ᵣ x1Val))
      (loopIterPostN1CallV5NoX1 sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  have J := divK_loop_body_n1_call_skip_j0_v5_spec_within_noNop_preserving_x1
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld x1Val retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rw [← loopIterPostN1CallV5NoX1_j0_skip (v5_skip_guard_of_noBorrow' hborrow)]
      exact hp)
    J

-- ============================================================================
-- Level 5: two-iteration (j=1, j=0) ALL-CALL composition, x1-preserving
-- ============================================================================

/-- v5 per-digit iteration post dispatcher, x1-free twin of `loopIterPostN1V5`. -/
def loopIterPostN1V5NoX1 (bltu : Bool)
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  match bltu with
  | true  => loopIterPostN1CallV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem
  | false => loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop ** empAssertion

@[simp] theorem loopIterPostN1V5NoX1_true
    {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word} :
    loopIterPostN1V5NoX1 true sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    loopIterPostN1CallV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem := rfl

/-- `loopN1Iter10PreV5` over the x1-free scratch bundle. -/
@[irreducible] def loopN1Iter10PreV5NoX1 (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  loopN1Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- `loopN1Iter10PostV5` minus the `regOwn .x1` atoms (all arms). -/
@[irreducible] def loopN1Iter10PostV5NoX1 (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
     retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  let r1 := iterN1V5 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut u1 u0 v0 scratchMem else scratchMem
  loopIterPostN1V5NoX1 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 scratch1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  match bltu_1, bltu_0 with
  | false, false =>
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0) **
    (sp + signExtend12 3936 ↦ₘ scratchMem)
  | true, false =>
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ divKTrialCallV5DLo v0) **
    (sp + signExtend12 3944 ↦ₘ divKTrialCallV5Un0 u0) **
    (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut u1 u0 v0 scratchMem)
  | _, true => empAssertion

private theorem iterN1Call_v5_unfold' (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    = iterWithDoubleAddback (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN1Call_v5
  rfl

/-- x1-preserving twin of `divK_loop_n1_call_iter10_v5_spec_within_noNop`. -/
theorem divK_loop_n1_call_iter10_v5_spec_within_noNop_preserving_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old x1Val : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u1 v0)
    (hbltu_0 : BitVec.ult (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hborrow_1 : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hborrow_0 : mulsubN4NoBorrow
      (divKTrialCallV5QHat (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 u0Orig v0)
      v0 v1 v2 v3 u0Orig
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1) :
    cpsTripleWithin 316 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopN1Iter10PreV5NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 scratchMem **
       (.x1 ↦ᵣ x1Val))
      (loopN1Iter10PostV5NoX1 true true sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0 scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  unfold loopN1Iter10PreV5NoX1 loopN1Iter10PreWithScratchNoX1 loopN1Iter10Pre
  let r1 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J1 := divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop_preserving_x1
    (1 : Word) EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old x1Val retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu_1 hborrow_1
  intro_lets at J1
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  have J0 := divK_loop_body_n1_call_iter_j0_v5_spec_within_noNop_preserving_x1
    sp (1 : Word) ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) r1.1 r1.2.2.2.2.1
    v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 q0Old x1Val
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) base
    halign hbltu_0 hborrow_0
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1))
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1CallV5NoX1 loopExitPostN1 loopExitPost at hp
      unfold loopBodyN1CallSkipJ0PreV4NoX1
      simp only [] at hp ⊢
      rw [← iterN1Call_v5_unfold'] at hp
      have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_1
      rw [hj', u_n1_j1_0_eq_j0_4088, u_n1_j1_4088_eq_j0_4080,
          u_n1_j1_4080_eq_j0_4072, u_n1_j1_4072_eq_j0_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter10PostV5NoX1
      simp only [loopIterPostN1V5NoX1_true, iterN1V5_true, if_true, sepConj_emp_right']
      xperm_hyp hp)
    full

-- ============================================================================
-- Level 6: three-iteration (j=2,1,0) ALL-CALL composition, x1-preserving
-- ============================================================================

/-- `loopN1Iter210PreV5` over the x1-free scratch bundle. -/
@[irreducible] def loopN1Iter210PreV5NoX1 (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  loopN1Iter210PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- `loopN1Iter210PostV5` over the x1-free iter10 post. -/
@[irreducible] def loopN1Iter210PostV5NoX1 (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0 scratchMem : Word) : Assertion :=
  let r2 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  loopN1Iter10PostV5NoX1 true true sp base v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 u0_orig_0
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) **
  ((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1)

/-- x1-preserving twin of `divK_loop_n1_call_iter210_v5_spec_within_noNop`. -/
theorem divK_loop_n1_call_iter210_v5_spec_within_noNop_preserving_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old x1Val : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : BitVec.ult u1 v0)
    (hbltu_1 : BitVec.ult
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_0 : BitVec.ult
      (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hborrow_2 : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hborrow_1 : mulsubN4NoBorrow
      (divKTrialCallV5QHat (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 u0_orig_1 v0)
      v0 v1 v2 v3 u0_orig_1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    (hborrow_0 : mulsubN4NoBorrow
      (divKTrialCallV5QHat
        (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
          (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 u0_orig_0 v0)
      v0 v1 v2 v3 u0_orig_0
      (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1) :
    cpsTripleWithin 474 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopN1Iter210PreV5NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 scratchMem **
       (.x1 ↦ᵣ x1Val))
      (loopN1Iter210PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  unfold loopN1Iter210PreV5NoX1 loopN1Iter210PreWithScratchNoX1 loopN1Iter210Pre
  let r2 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  have J2 := divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop_preserving_x1
    (2 : Word) EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old x1Val retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu_2 hborrow_2
  intro_lets at J2
  have J2f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat + signExtend12 0) ↦ₘ u0_orig_0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old))
    (by pcFree) J2
  have I10 := divK_loop_n1_call_iter10_v5_spec_within_noNop_preserving_x1
    sp (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3 u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 u0_orig_0 q1Old q0Old x1Val
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) base
    halign hbltu_1 hbltu_0 hborrow_1 hborrow_0
  have I10f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) I10
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1CallV5NoX1 loopExitPostN1 loopExitPost at hp
      unfold loopN1Iter10PreV5NoX1 loopN1Iter10PreWithScratchNoX1 loopN1Iter10Pre
      simp only [] at hp ⊢
      rw [← iterN1Call_v5_unfold'] at hp
      have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_2
      rw [hj', u_n1_j2_0_eq_j1_4088, u_n1_j2_4088_eq_j1_4080,
          u_n1_j2_4080_eq_j1_4072, u_n1_j2_4072_eq_j1_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f I10f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter210PostV5NoX1
      xperm_hyp hp)
    full

-- ============================================================================
-- Level 7: full-loop (j=3,2,1,0) ALL-CALL composition, x1-preserving
-- ============================================================================

/-- `loopN1UnifiedPreV5` over the x1-free scratch bundle. -/
@[irreducible] def loopN1UnifiedPreV5NoX1 (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- `loopN1UnifiedPostV5` over the x1-free iter210 post. -/
@[irreducible] def loopN1UnifiedPostV5NoX1 (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_2 u0_orig_1 u0_orig_0 scratchMem : Word) : Assertion :=
  let r3 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  loopN1Iter210PostV5NoX1 sp base v0 v1 v2 v3
    u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 u0_orig_1 u0_orig_0
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) **
  ((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1)

/-- x1-preserving twin of `divK_loop_n1_call_unified_v5_spec_within_noNop`. -/
theorem divK_loop_n1_call_unified_v5_spec_within_noNop_preserving_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
     q3Old q2Old q1Old q0Old x1Val : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : BitVec.ult u1 v0)
    (hbltu_2 : BitVec.ult (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : BitVec.ult (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.1 v0)
    (hbltu_0 : BitVec.ult (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.1 v0)
    (hborrow_3 : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hborrow_2 : mulsubN4NoBorrow
      (divKTrialCallV5QHat (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 u0_orig_2 v0)
      v0 v1 v2 v3 u0_orig_2
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    (hborrow_1 : mulsubN4NoBorrow
      (divKTrialCallV5QHat (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.1 u0_orig_1 v0)
      v0 v1 v2 v3 u0_orig_1
      (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.1
      (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.2.1
      (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.2.2.1
      (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.2.2.2.1)
    (hborrow_0 : mulsubN4NoBorrow
      (divKTrialCallV5QHat (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.1 u0_orig_0 v0)
      v0 v1 v2 v3 u0_orig_0
      (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.1
      (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.2.1
      (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.2.2.1
      (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.2.2.2.1) :
    cpsTripleWithin 632 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopN1UnifiedPreV5NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 scratchMem **
       (.x1 ↦ᵣ x1Val))
      (loopN1UnifiedPostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  unfold loopN1UnifiedPreV5NoX1 loopN1PreWithScratchNoX1 loopN1Pre
  let r3 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J3 := divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop_preserving_x1
    (3 : Word) EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_3
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q3Old x1Val retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu_3 hborrow_3
  intro_lets at J3
  have J3f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 0) ↦ₘ u0_orig_2) ** (q_addr_2 ↦ₘ q2Old) **
     ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J3
  have I210 := divK_loop_n1_call_iter210_v5_spec_within_noNop_preserving_x1
    sp (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) u_base_3 q_addr_3
    ((mulsubN4 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) r3.1 r3.2.2.2.2.1
    v0 v1 v2 v3 u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 u0_orig_1 u0_orig_0
    q2Old q1Old q0Old x1Val
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) base
    halign hbltu_2 hbltu_1 hbltu_0 hborrow_2 hborrow_1 hborrow_0
  have I210f := cpsTripleWithin_frameR
    (((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1))
    (by pcFree) I210
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1CallV5NoX1 loopExitPostN1 loopExitPost at hp
      unfold loopN1Iter210PreV5NoX1 loopN1Iter210PreWithScratchNoX1 loopN1Iter210Pre
      simp only [] at hp ⊢
      rw [← iterN1Call_v5_unfold'] at hp
      have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_3
      rw [hj', u_n1_j3_0_eq_j2_4088, u_n1_j3_4088_eq_j2_4080,
          u_n1_j3_4080_eq_j2_4072, u_n1_j3_4072_eq_j2_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J3f I210f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN1UnifiedPostV5NoX1
      xperm_hyp hp)
    full

-- ============================================================================
-- Level 8: at normalized shape, x1-preserving
-- ============================================================================

/-- x1-preserving twin of `divK_loop_n1_call_unified_v5_of_shape`: the full v5
    n=1 loop at the normalized inputs, keeping the concrete `x1Val` framed. -/
theorem divK_loop_n1_call_unified_v5_of_shape_preserving_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     q3Old q2Old q1Old q0Old x1Val : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    cpsTripleWithin 632 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopN1UnifiedPreV5NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 scratchMem **
       (.x1 ↦ᵣ x1Val))
      (loopN1UnifiedPostV5NoX1 sp base
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1 scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  refine divK_loop_n1_call_unified_v5_spec_within_noNop_preserving_x1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    q3Old q2Old q1Old q0Old x1Val retMem dMem dloMem scratch_un0 scratchMem base halign
    ?hb3 ?hb2 ?hb1 ?hb0 ?ho3 ?ho2 ?ho1 ?ho0
  case hb3 => exact n1v5_lane_bltu_3_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case hb2 =>
    rw [← fullDivN1R3V5_eq_iterN1Call_v5]
    exact n1v5_lane_bltu_2_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case hb1 =>
    rw [fullN1S2_eq_fullDivN1R2V5]
    exact n1v5_lane_bltu_1_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case hb0 =>
    rw [fullN1S1_eq_fullDivN1R1V5]
    exact n1v5_lane_bltu_0_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case ho3 => exact n1v5_lane_hborrow_3_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case ho2 =>
    rw [← fullDivN1R3V5_eq_iterN1Call_v5]
    exact n1v5_lane_hborrow_2_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case ho1 =>
    rw [fullN1S2_eq_fullDivN1R2V5]
    exact n1v5_lane_hborrow_1_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case ho0 =>
    rw [fullN1S1_eq_fullDivN1R1V5]
    exact n1v5_lane_hborrow_0_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz

end EvmAsm.Evm64
