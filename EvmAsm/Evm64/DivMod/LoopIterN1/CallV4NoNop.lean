/-
  EvmAsm.Evm64.DivMod.LoopIterN1.CallV4NoNop

  No-NOP/v4 replay of the n=1 BLTU-taken call+skip j=0 loop-body spec.
-/

import EvmAsm.Evm64.DivMod.N1CallBase

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

@[irreducible]
def loopBodyN1CallSkipJgt0PreV4NoX1
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
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
   (sp + signExtend12 3936 ↦ₘ scratchMem))

theorem loopBodyN1CallSkipJgt0PreV4NoX1_pcFree
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word) :
    (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem).pcFree := by
  delta loopBodyN1CallSkipJgt0PreV4NoX1
  pcFree

instance pcFreeInst_loopBodyN1CallSkipJgt0PreV4NoX1
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word) :
    Assertion.PCFree
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem) :=
  ⟨loopBodyN1CallSkipJgt0PreV4NoX1_pcFree sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem⟩

theorem loopBodyN1CallSkipJgt0PreV4NoX1_to_legacy
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    ∀ h,
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        regOwn .x1) h →
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
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
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1) h) := by
  intro uBase qAddr h hp
  simpa only [loopBodyN1CallSkipJgt0PreV4NoX1, sepConj_assoc'] using hp

@[irreducible]
def loopBodyN1CallSkipJgt0PostV4
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  loopBodyN1SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut) **
  regOwn .x1

@[irreducible]
def loopBodyN1CallSkipJgt0PostV4NoX1
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  loopBodyN1SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut)

theorem loopBodyN1CallSkipJgt0PostV4NoX1_unfold
    {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word} :
    loopBodyN1CallSkipJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    (
    let dLo := divKTrialCallV4DLo v0
    let div_un0 := divKTrialCallV4Un0 u0
    let qHat := divKTrialCallV4QHat u1 u0 v0
    let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
    loopBodyN1SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ dLo) **
    (sp + signExtend12 3944 ↦ₘ div_un0) **
    (sp + signExtend12 3936 ↦ₘ scratchOut)) := by
  delta loopBodyN1CallSkipJgt0PostV4NoX1
  rfl

theorem loopBodyN1CallSkipJgt0PostV4NoX1_pcFree
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    (loopBodyN1CallSkipJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem).pcFree := by
  delta loopBodyN1CallSkipJgt0PostV4NoX1 loopBodyN1SkipPost
        loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost
  pcFree

instance pcFreeInst_loopBodyN1CallSkipJgt0PostV4NoX1
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    Assertion.PCFree
      (loopBodyN1CallSkipJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  ⟨loopBodyN1CallSkipJgt0PostV4NoX1_pcFree sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem⟩

theorem loopBodyN1CallSkipJgt0PostV4NoX1_to_loopBodyN1CallSkipJgt0PostV4
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    ∀ h,
      (loopBodyN1CallSkipJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        regOwn .x1) h →
      loopBodyN1CallSkipJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem h := by
  intro h hp
  delta loopBodyN1CallSkipJgt0PostV4NoX1 loopBodyN1CallSkipJgt0PostV4 at hp ⊢
  simpa only [sepConj_assoc'] using hp

theorem loopBodyN1CallSkipJgt0PostV4NoX1_eq_scratch
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN1CallSkipJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN1CallSkipPostJScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN1CallSkipJgt0PostV4NoX1 loopBodyN1CallSkipPostJScratchNoX1
  rfl

theorem loopBodyN1CallSkipJ0PostV4NoX1_eq_scratch
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN1CallSkipJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN1CallSkipPostJScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN1CallSkipJ0PostV4NoX1 loopBodyN1CallSkipPostJScratchNoX1
  rfl

/-- No-NOP/v4 loop body cpsTripleWithin for n=1, call+skip, j=0.
    This consumes the v4 div128 call path and exits to denorm. -/
theorem divK_loop_body_n1_call_skip_j0_v4_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem)
      (loopBodyN1CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  unfold loopBodyN1CallSkipJ0PreV4
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v0
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let q1'' := divKTrialCallV4Q1dd u1 u0 v0
  let q0'' := divKTrialCallV4Q0dd u1 u0 v0
  let x7Exit := divKTrialCallV4X7Exit u1 u0 v0
  let x9Exit := divKTrialCallV4X9Exit u1 u0 v0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  have TF := divK_trial_call_full_v4_spec_within_noNop sp (0 : Word) (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV4 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  have hborrow' :
      mulsubN4NoBorrow qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
    unfold loopBodyN1CallSkipJ0BorrowV4 at hborrow
    exact hborrow
  have MCS := divK_mulsub_correction_skip_v4_spec_within_noNop sp qHat (0 : Word)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  have MCS0 := MCS hborrow'
  unfold divKMulsubCorrectionSkipPre at MCS0
  unfold n4McaNamedSkipPost at MCS0
  unfold mulsubN4 at MCS0
  dsimp only [] at MCS0
  have MCS0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
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
  have SL := divK_store_loop_j0_v4_spec_within_noNop sp qHat u4_new (0 : Word) qOld base
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
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallSkipJ0PostV4
      unfold loopBodyN1SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- No-NOP/v4 n=1 call+skip j=0 spec preserving the concrete caller `x1`
    through trial-call, mulsub/correction-skip, and store-loop exit. -/
theorem divK_loop_body_n1_call_skip_j0_v4_spec_within_noNop_exact_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN1CallSkipJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  unfold loopBodyN1CallSkipJ0PreV4NoX1
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v0
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let q1'' := divKTrialCallV4Q1dd u1 u0 v0
  let q0'' := divKTrialCallV4Q0dd u1 u0 v0
  let x7Exit := divKTrialCallV4X7Exit u1 u0 v0
  let x9Exit := divKTrialCallV4X9Exit u1 u0 v0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  have TF := divK_trial_call_full_v4_spec_within_noNop_exact_x1 sp (0 : Word) (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 scratchMem raVal base
    halign hbltu
  unfold divKTrialCallFullPostV4ExactX1 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  have hborrow' :
      mulsubN4NoBorrow qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
    unfold loopBodyN1CallSkipJ0BorrowV4 at hborrow
    exact hborrow
  have MCS := divK_mulsub_correction_skip_v4_spec_within_noNop sp qHat (0 : Word)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  have MCS0 := MCS hborrow'
  unfold divKMulsubCorrectionSkipPre at MCS0
  unfold n4McaNamedSkipPost at MCS0
  unfold mulsubN4 at MCS0
  dsimp only [] at MCS0
  have MCS0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ raVal))
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
  have SL := divK_store_loop_j0_v4_spec_within_noNop_exact_x1 sp qHat u4_new (0 : Word) qOld raVal base
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
     (sp + signExtend12 3936 ↦ₘ scratchOut))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallSkipJ0PostV4NoX1
      unfold loopBodyN1SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- No-NOP/v4 n=1 call+skip j=0 exact-`x1` spec exposing the
    scratch-parameterized post used by the callable loop surface. -/
theorem divK_loop_body_n1_call_skip_j0_v4_spec_within_noNop_exact_x1_scratch
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN1CallSkipPostJScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      rw [loopBodyN1CallSkipJ0PostV4NoX1_eq_scratch] at hp
      exact hp)
    (divK_loop_body_n1_call_skip_j0_v4_spec_within_noNop_exact_x1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow)

/-- No-NOP/v4 n=1 call+skip j=0 exact-`x1` spec lifted to the
    scratch-parameterized loop-iteration post. -/
theorem divK_loop_body_n1_call_skip_j0_v4_spec_within_noNop_exact_x1_loopIterScratch
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      ¬BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3) := by
    unfold loopBodyN1CallSkipJ0BorrowV4 mulsubN4NoBorrow at hborrow
    dsimp only [] at hborrow
    intro h_lt
    unfold mulsubN4_c3 at h_lt
    rw [if_pos h_lt] at hborrow
    exact (by decide : (1 : Word) ≠ (0 : Word)) hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      rw [loopIterPostN1CallScratchNoX1_skip hb] at hp
      exact hp)
    (divK_loop_body_n1_call_skip_j0_v4_spec_within_noNop_exact_x1_scratch
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow)

/-- No-NOP/v4 n=1 call+skip j=0 spec with the call frame split so future
    callers can keep `x1` outside the loop-body assertion. -/
theorem divK_loop_body_n1_call_skip_j0_v4_spec_within_noNop_noX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        regOwn .x1)
      (loopBodyN1CallSkipJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        regOwn .x1) := by
  exact cpsTripleWithin_weaken
    (loopBodyN1CallSkipJ0PreV4NoX1_to_loopBodyN1CallSkipJ0PreV4
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem)
    (fun h hp => by
      unfold loopBodyN1CallSkipJ0PostV4 at hp
      unfold loopBodyN1CallSkipJ0PostV4NoX1
      simpa only [sepConj_assoc'] using hp)
    (divK_loop_body_n1_call_skip_j0_v4_spec_within_noNop
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow)

/-- No-NOP/v4 loop body cpsTripleWithin for n=1, call+skip, j>0.
    This consumes the v4 div128 call path and loops back to the loop body. -/
theorem divK_loop_body_n1_call_skip_jgt0_v4_spec_within_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
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
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1)
      (loopBodyN1CallSkipJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  intro uBase qAddr
  let dHi := divKTrialCallV4DHi v0
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let q1'' := divKTrialCallV4Q1dd u1 u0 v0
  let q0'' := divKTrialCallV4Q0dd u1 u0 v0
  let x7Exit := divKTrialCallV4X7Exit u1 u0 v0
  let x9Exit := divKTrialCallV4X9Exit u1 u0 v0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  have TF := divK_trial_call_full_v4_spec_within_noNop sp j (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV4 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  have hborrow' :
      mulsubN4NoBorrow qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
    exact hborrow
  have MCS := divK_mulsub_correction_skip_v4_spec_within_noNop sp qHat j
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  have MCS0 := MCS hborrow'
  unfold divKMulsubCorrectionSkipPre at MCS0
  unfold n4McaNamedSkipPost at MCS0
  unfold mulsubN4 at MCS0
  dsimp only [] at MCS0
  have MCS0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
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
  have SL := divK_store_loop_jgt0_v4_spec_within_noNop sp j qHat u4_new (0 : Word) qOld base hpos
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
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallSkipJgt0PostV4
      unfold loopBodyN1SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- No-NOP/v4 n=1 call+skip j>0 spec preserving the concrete caller `x1`
    through trial-call, mulsub/correction-skip, and store-loop loop-back. -/
theorem divK_loop_body_n1_call_skip_jgt0_v4_spec_within_noNop_exact_x1 (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN1CallSkipJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  unfold loopBodyN1CallSkipJgt0PreV4NoX1
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v0
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let q1'' := divKTrialCallV4Q1dd u1 u0 v0
  let q0'' := divKTrialCallV4Q0dd u1 u0 v0
  let x7Exit := divKTrialCallV4X7Exit u1 u0 v0
  let x9Exit := divKTrialCallV4X9Exit u1 u0 v0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  have TF := divK_trial_call_full_v4_spec_within_noNop_exact_x1 sp j (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 scratchMem raVal base
    halign hbltu
  unfold divKTrialCallFullPostV4ExactX1 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  have hborrow' :
      mulsubN4NoBorrow qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
    exact hborrow
  have MCS := divK_mulsub_correction_skip_v4_spec_within_noNop sp qHat j
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  have MCS0 := MCS hborrow'
  unfold divKMulsubCorrectionSkipPre at MCS0
  unfold n4McaNamedSkipPost at MCS0
  unfold mulsubN4 at MCS0
  dsimp only [] at MCS0
  have MCS0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ raVal))
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
  have SL := divK_store_loop_jgt0_v4_spec_within_noNop_exact_x1 sp j qHat u4_new (0 : Word) qOld raVal base hpos
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
     (sp + signExtend12 3936 ↦ₘ scratchOut))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallSkipJgt0PostV4NoX1
      unfold loopBodyN1SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- No-NOP/v4 n=1 call+skip j>0 exact-`x1` spec exposing the
    scratch-parameterized post used by the callable loop surface. -/
theorem divK_loop_body_n1_call_skip_jgt0_v4_spec_within_noNop_exact_x1_scratch (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN1CallSkipPostJScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      rw [loopBodyN1CallSkipJgt0PostV4NoX1_eq_scratch] at hp
      exact hp)
    (divK_loop_body_n1_call_skip_jgt0_v4_spec_within_noNop_exact_x1 j hpos
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow)

/-- No-NOP/v4 n=1 call+skip j>0 exact-`x1` spec lifted to the
    scratch-parameterized loop-iteration post. -/
theorem divK_loop_body_n1_call_skip_jgt0_v4_spec_within_noNop_exact_x1_loopIterScratch (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      ¬BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3) := by
    unfold mulsubN4NoBorrow at hborrow
    dsimp only [] at hborrow
    intro h_lt
    unfold mulsubN4_c3 at h_lt
    rw [if_pos h_lt] at hborrow
    exact (by decide : (1 : Word) ≠ (0 : Word)) hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      rw [loopIterPostN1CallScratchNoX1_skip hb] at hp
      exact hp)
    (divK_loop_body_n1_call_skip_jgt0_v4_spec_within_noNop_exact_x1_scratch j hpos
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow)

/-- No-NOP/v4 n=1 call+skip j>0 spec with the call frame split so future
    callers can keep `x1` outside the loop-body assertion. -/
theorem divK_loop_body_n1_call_skip_jgt0_v4_spec_within_noNop_noX1 (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        regOwn .x1)
      (loopBodyN1CallSkipJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        regOwn .x1) := by
  have legacy := divK_loop_body_n1_call_skip_jgt0_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow
  dsimp only [] at legacy
  exact cpsTripleWithin_weaken
    (loopBodyN1CallSkipJgt0PreV4NoX1_to_legacy
      sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem)
    (fun h hp => by
      unfold loopBodyN1CallSkipJgt0PostV4 at hp
      unfold loopBodyN1CallSkipJgt0PostV4NoX1
      simpa only [sepConj_assoc'] using hp)
    legacy

end EvmAsm.Evm64
