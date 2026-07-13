/-
  Shared declaration home for the n=1 v5 loop iteration/call chain.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.CallV5NoNop
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallFullV5Named
import EvmAsm.Evm64.DivMod.LoopBody.MulsubSkipV5
import EvmAsm.Evm64.DivMod.LoopBody.StoreLoopV5
import EvmAsm.Evm64.DivMod.Spec.N1V5QuotNoBorrowShared
import EvmAsm.Evm64.DivMod.LoopIterN1.MaxSkipV5
import EvmAsm.Evm64.DivMod.Spec.N1V5LaneBltu
import EvmAsm.Evm64.DivMod.Spec.N1V5LaneHborrow

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_1 slt_jpos_1 jpred_2 slt_jpos_2 jpred_3 slt_jpos_3)

open EvmAsm.Rv64

/-- v5 n=1 call+skip j=0 loop body over `sharedDivModCodeNoNop_v5`: trial-call-full
    + mulsub + correction-skip + store-loop, with the exact v5 trial quotient
    `divKTrialCallV5QHat` (= `div128Quot_v5`).  Mirror of the v4 analog. -/
theorem divK_loop_body_n1_call_skip_j0_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopBodyN1CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem)
      (loopBodyN1CallSkipJ0PostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  unfold loopBodyN1CallSkipJ0PreV4
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
  have TF := divK_trial_call_full_v5_named_spec_within_noNop sp (0 : Word) (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV5Named at TF
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
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallSkipJ0PostV5
      unfold loopBodyN1SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

open EvmAsm.Rv64

/-- v5 n=1 call+skip j>0 loop-body post (mirror of `loopBodyN1CallSkipJgt0PostV4`
    with v5 trial defs): the exact v5 trial quotient `divKTrialCallV5QHat` is
    stored, the loop counter stays `j`, and the div128 scratch cells settle. -/
def loopBodyN1CallSkipJgt0PostV5
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
  (sp + signExtend12 3936 ↦ₘ scratchOut) **
  regOwn .x1

/-- v5 n=1 call+skip j>0 loop body over `sharedDivModCodeNoNop_v5` (158 steps,
    loopBodyOff → loopBodyOff loop-back).  Mirror of the v4 analog. -/
theorem divK_loop_body_n1_call_skip_jgt0_v5_spec_within_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
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
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1)
      (loopBodyN1CallSkipJgt0PostV5 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
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
  have TF := divK_trial_call_full_v5_named_spec_within_noNop sp j (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV5Named at TF
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
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallSkipJgt0PostV5
      unfold loopBodyN1SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

open EvmAsm.Rv64

/-- v5 n=1 call-path per-digit iteration post: the schoolbook digit result
    (`iterWithDoubleAddback` over `div128Quot_v5`) with the div128 scratch cells
    settled (via the named v5 scratch defs).  Mirror of `loopIterPostN1CallV4NoX1`
    plus `regOwn .x1`. -/
@[irreducible] def loopIterPostN1CallV5
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let qHat := div128Quot_v5 u1 u0 v0
  let r := iterWithDoubleAddback qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let c3 := (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN1 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ divKTrialCallV5DLo v0) **
  (sp + signExtend12 3944 ↦ₘ divKTrialCallV5Un0 u0) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) **
  regOwn .x1

/-- Skip bridge (j=0): the v5 j=0 loop-body post equals the iteration post when
    the mulsub does not borrow (which, for the exact v5 trial, always holds). -/
theorem loopIterPostN1CallV5_j0_skip
    {sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word}
    (hb : ¬BitVec.ult uTop
      (mulsubN4_c3 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN1CallSkipJ0PostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    loopIterPostN1CallV5 sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem := by
  unfold loopBodyN1CallSkipJ0PostV5 loopIterPostN1CallV5
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  delta loopBodyN1SkipPost loopBodySkipPost loopExitPostN1 loopExitPost
    iterWithDoubleAddback
  unfold mulsubN4_c3 at hb
  simp only [if_neg hb]

/-- Skip bridge (j>0): the v5 steady-state loop-body post equals the iteration
    post when the mulsub does not borrow. -/
theorem loopIterPostN1CallV5_jgt0_skip
    {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word}
    (hb : ¬BitVec.ult uTop
      (mulsubN4_c3 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN1CallSkipJgt0PostV5 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    loopIterPostN1CallV5 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem := by
  unfold loopBodyN1CallSkipJgt0PostV5 loopIterPostN1CallV5
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  delta loopBodyN1SkipPost loopBodySkipPost loopExitPostN1 loopExitPost
    iterWithDoubleAddback
  unfold mulsubN4_c3 at hb
  simp only [if_neg hb]

open EvmAsm.Rv64

/-- From the v5 no-borrow hypothesis (over `divKTrialCallV5QHat`), the mulsub-c3
    skip guard (over `div128Quot_v5`) holds. -/
private theorem v5_skip_guard_of_noBorrow {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    ¬BitVec.ult uTop (mulsubN4_c3 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3) := by
  intro hult
  unfold mulsubN4NoBorrow at hborrow
  simp_rw [divKTrialCallV5QHat_eq_div128Quot_v5] at hborrow
  unfold mulsubN4_c3 at hult
  rw [if_pos hult] at hborrow
  exact absurd hborrow (by decide)

/-- v5 n=1 call-path iteration-ready loop body, j>0 (loops back to loopBody). -/
theorem divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
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
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1)
      (loopIterPostN1CallV5 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  intro uBase qAddr
  have J := divK_loop_body_n1_call_skip_jgt0_v5_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu hborrow
  intro_lets at J
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by rw [← loopIterPostN1CallV5_jgt0_skip (v5_skip_guard_of_noBorrow hborrow)]; exact hp)
    J

/-- v5 n=1 call-path iteration-ready loop body, j=0 (exits to denorm). -/
theorem divK_loop_body_n1_call_iter_j0_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopBodyN1CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem)
      (loopIterPostN1CallV5 sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have J := divK_loop_body_n1_call_skip_j0_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by rw [← loopIterPostN1CallV5_j0_skip (v5_skip_guard_of_noBorrow hborrow)]; exact hp)
    J

open EvmAsm.Rv64

/-- v5 n=1 max-path iteration-ready loop body, j>0 (loops back to loopBody). -/
theorem divK_loop_body_n1_max_iter_jgt0_v5_spec_within_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v5 base)
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
       (qAddr ↦ₘ qOld))
      (loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  have hb : ¬BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) := by
    intro hult; rw [if_pos hult] at hborrow; exact absurd hborrow (by decide)
  have J := divK_loop_body_n1_max_skip_jgt0_v5_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow
  intro_lets at J
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by rw [← loopIterPostN1Max_skip hb]; exact hp)
    J

/-- v5 n=1 max-path iteration-ready loop body, j=0 (exits to denorm). -/
theorem divK_loop_body_n1_max_iter_j0_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopIterPostN1Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  have hb : ¬BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) := by
    intro hult; rw [if_pos hult] at hborrow; exact absurd hborrow (by decide)
  have J := divK_loop_body_n1_max_skip_j0_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow
  intro_lets at J
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by rw [← loopIterPostN1Max_skip hb]; exact hp)
    J

open EvmAsm.Rv64

/-- v5 n=1 per-digit iteration post, dispatched on the call/max branch.  Mirror
    of `loopIterPostN1`. -/
def loopIterPostN1V5 (bltu : Bool)
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  match bltu with
  | true  => loopIterPostN1CallV5 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem
  | false => loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop ** empAssertion

@[simp] theorem loopIterPostN1V5_true
    {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word} :
    loopIterPostN1V5 true sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    loopIterPostN1CallV5 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem := rfl

@[simp] theorem loopIterPostN1V5_false
    {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word} :
    loopIterPostN1V5 false sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    (loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop ** empAssertion) := rfl

open EvmAsm.Rv64

/-- v5 n=1 two-iteration loop precondition: the v4 iter10 PRE plus the extra v5
    div128 Phase-2 scratch cell `sp+3936 ↦ scratchMem`. -/
@[irreducible] def loopN1Iter10PreV5 (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  loopN1Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- v5 n=1 two-iteration (j=1, j=0) loop postcondition over the v5 model
    `iterN1V5` and per-digit dispatcher `loopIterPostN1V5`.  Mirror of
    `loopN1Iter10Post`, but the `sp+3936` scratch cell is threaded explicitly:
    when the final digit is MAX the surviving `sp+3936` value is whatever the
    earlier digit left. -/
@[irreducible] def loopN1Iter10PostV5 (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
     retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  let r1 := iterN1V5 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- sp+3936 after j=1: call overwrites with ScratchOut, max passes scratchMem.
  let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut u1 u0 v0 scratchMem else scratchMem
  loopIterPostN1V5 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 scratch1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  match bltu_1, bltu_0 with
  | false, false =>
    -- both max: nothing touched the div128 scratch region.
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0) **
    (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1
  | true, false =>
    -- j=1 call left its scratch; j=0 max kept it.
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ divKTrialCallV5DLo v0) **
    (sp + signExtend12 3944 ↦ₘ divKTrialCallV5Un0 u0) **
    (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) ** regOwn .x1
  | _, true => empAssertion

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_1 slt_jpos_1)

private theorem iterN1Call_v5_unfold (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    = iterWithDoubleAddback (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN1Call_v5
  rfl

theorem divK_loop_n1_call_iter10_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
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
      (loopN1Iter10PreV5 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 scratchMem)
      (loopN1Iter10PostV5 true true sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0 scratchMem) := by
  unfold loopN1Iter10PreV5 loopN1Iter10PreWithScratch loopN1Iter10Pre
  let r1 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- j=1 call body
  have J1 := divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop (1 : Word) slt_jpos_1
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu_1 hborrow_1
  intro_lets at J1
  -- Frame j=1 with digit-0 cells (call j=1 consumes the scratch region)
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  -- j=0 call body, inputs from j=1's call output (old regs = j=1 loopExitPostN1 output)
  have J0 := divK_loop_body_n1_call_iter_j0_v5_spec_within_noNop
    sp (1 : Word) ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) r1.1 r1.2.2.2.2.1
    v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 q0Old
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) base
    halign hbltu_0 hborrow_0
  -- Frame j=0 with j=1's carried atoms only
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1))
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1CallV5 loopExitPostN1 loopExitPost at hp
      unfold loopBodyN1CallSkipJ0PreV4
      simp only [] at hp ⊢
      rw [← iterN1Call_v5_unfold] at hp
      have hj' := jpred_1
      rw [hj', u_n1_j1_0_eq_j0_4088, u_n1_j1_4088_eq_j0_4080,
          u_n1_j1_4080_eq_j0_4072, u_n1_j1_4072_eq_j0_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter10PostV5
      simp only [loopIterPostN1V5_true, iterN1V5_true, if_true, sepConj_emp_right']
      xperm_hyp hp)
    full

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_2 slt_jpos_2)

private theorem iterN1Call_v5_unfold210 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    = iterWithDoubleAddback (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN1Call_v5
  rfl

/-- v5 n=1 three-iteration loop precondition (entry at j=2) with the v5 `sp+3936`
    scratch cell. -/
@[irreducible] def loopN1Iter210PreV5 (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  loopN1Iter210PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- v5 n=1 three-iteration (j=2,j=1,j=0) ALL-CALL loop postcondition.  (j=2 is
    always call, overwriting the div128 scratch, so the initial scratch values do
    not appear.) -/
@[irreducible] def loopN1Iter210PostV5 (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0 scratchMem : Word) : Assertion :=
  let r2 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  loopN1Iter10PostV5 true true sp base v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 u0_orig_0
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) **
  ((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1)

theorem divK_loop_n1_call_iter210_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old : Word)
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
      (loopN1Iter210PreV5 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 scratchMem)
      (loopN1Iter210PostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 scratchMem) := by
  unfold loopN1Iter210PreV5 loopN1Iter210PreWithScratch loopN1Iter210Pre
  let r2 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=2 call body
  have J2 := divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop (2 : Word) slt_jpos_2
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu_2 hborrow_2
  intro_lets at J2
  -- Frame j=2 with digits 1,0 cells (call j=2 consumes scratch)
  have J2f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat + signExtend12 0) ↦ₘ u0_orig_0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old))
    (by pcFree) J2
  -- inner iter10 over digits 1,0 with j=2 outputs as inputs
  have I10 := divK_loop_n1_call_iter10_v5_spec_within_noNop
    sp (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3 u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 u0_orig_0 q1Old q0Old
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) base
    halign hbltu_1 hbltu_0 hborrow_1 hborrow_0
  -- Frame iter10 with j=2's carried atoms
  have I10f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) I10
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1CallV5 loopExitPostN1 loopExitPost at hp
      unfold loopN1Iter10PreV5 loopN1Iter10PreWithScratch loopN1Iter10Pre
      simp only [] at hp ⊢
      rw [← iterN1Call_v5_unfold210] at hp
      have hj' := jpred_2
      rw [hj', u_n1_j2_0_eq_j1_4088, u_n1_j2_4088_eq_j1_4080,
          u_n1_j2_4080_eq_j1_4072, u_n1_j2_4072_eq_j1_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f I10f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter210PostV5
      xperm_hyp hp)
    full

open EvmAsm.Rv64

/-- v5 n=1 full-loop precondition (entry at j=3) with the v5 `sp+3936` scratch
    cell. -/
@[irreducible] def loopN1UnifiedPreV5 (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  loopN1PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- v5 n=1 full-loop (j=3,2,1,0) ALL-CALL postcondition.  (j=3 is always call,
    overwriting the div128 scratch, so the initial scratch values do not appear.) -/
@[irreducible] def loopN1UnifiedPostV5 (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_2 u0_orig_1 u0_orig_0 scratchMem : Word) : Assertion :=
  let r3 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  loopN1Iter210PostV5 sp base v0 v1 v2 v3
    u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 u0_orig_1 u0_orig_0
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) **
  ((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1)

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_3 slt_jpos_3)

/-- Unfold `iterN1Call_v5` to its `iterWithDoubleAddback (div128Quot_v5 …)` body.
    Public: the loop-post → denorm-epilogue bridge uses this to fold the j=0
    iteration (which the loop post expresses via `iterWithDoubleAddback`) back to
    `iterN1Call_v5` so it matches the schoolbook digit form. -/
theorem iterN1Call_v5_unfoldU (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    = iterWithDoubleAddback (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN1Call_v5
  rfl

/-- j=2-entry iteration state (after the j=3 digit). -/
def fullN1S2 (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 : Word) :=
  let s3 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  iterN1Call_v5 v0 v1 v2 v3 u0_orig_2 s3.2.1 s3.2.2.1 s3.2.2.2.1 s3.2.2.2.2.1

/-- j=1-entry iteration state (after the j=3, j=2 digits). -/
def fullN1S1 (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 : Word) :=
  let s2 := fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2
  iterN1Call_v5 v0 v1 v2 v3 u0_orig_1 s2.2.1 s2.2.2.1 s2.2.2.2.1 s2.2.2.2.2.1

theorem divK_loop_n1_call_unified_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
     q3Old q2Old q1Old q0Old : Word)
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
      (loopN1UnifiedPreV5 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 scratchMem)
      (loopN1UnifiedPostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 scratchMem) := by
  unfold loopN1UnifiedPreV5 loopN1PreWithScratch loopN1Pre
  let r3 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J3 := divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop (3 : Word) slt_jpos_3
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q3Old retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu_3 hborrow_3
  intro_lets at J3
  have J3f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 0) ↦ₘ u0_orig_2) ** (q_addr_2 ↦ₘ q2Old) **
     ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J3
  have I210 := divK_loop_n1_call_iter210_v5_spec_within_noNop
    sp (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) u_base_3 q_addr_3
    ((mulsubN4 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) r3.1 r3.2.2.2.2.1
    v0 v1 v2 v3 u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 u0_orig_1 u0_orig_0
    q2Old q1Old q0Old
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) base
    halign hbltu_2 hbltu_1 hbltu_0 hborrow_2 hborrow_1 hborrow_0
  have I210f := cpsTripleWithin_frameR
    (((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1))
    (by pcFree) I210
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1CallV5 loopExitPostN1 loopExitPost at hp
      unfold loopN1Iter210PreV5 loopN1Iter210PreWithScratch loopN1Iter210Pre
      simp only [] at hp ⊢
      rw [← iterN1Call_v5_unfoldU] at hp
      have hj' := jpred_3
      rw [hj', u_n1_j3_0_eq_j2_4088, u_n1_j3_4088_eq_j2_4080,
          u_n1_j3_4080_eq_j2_4072, u_n1_j3_4072_eq_j2_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J3f I210f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN1UnifiedPostV5
      xperm_hyp hp)
    full

open EvmAsm.Rv64

/-- `fullN1S2` at the normalized inputs equals the schoolbook j=1-entry digit
    `fullDivN1R2V5 true true`. -/
theorem fullN1S2_eq_fullDivN1R2V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullN1S2 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    = fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullN1S2 fullDivN1R2V5 fullDivN1R3V5
  simp only [iterN1V5_true]

/-- `fullN1S1` at the normalized inputs equals the schoolbook j=0-entry digit
    `fullDivN1R1V5 true true true`. -/
theorem fullN1S1_eq_fullDivN1R1V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullN1S1 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    = fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullN1S1 fullN1S2 fullDivN1R1V5 fullDivN1R2V5 fullDivN1R3V5
  simp only [iterN1V5_true]

/-- The first schoolbook digit `fullDivN1R3V5 true` equals the raw `iterN1Call_v5`
    over the normalized top window — the form the full loop's `hbltu_2`/`hborrow_3`
    hypotheses use. -/
theorem fullDivN1R3V5_eq_iterN1Call_v5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3
    = iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0 := by
  unfold fullDivN1R3V5
  simp only [iterN1V5_true]

open EvmAsm.Rv64

theorem divK_loop_n1_call_unified_v5_of_shape
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    cpsTripleWithin 632 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopN1UnifiedPreV5 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 scratchMem)
      (loopN1UnifiedPostV5 sp base
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1 scratchMem) := by
  refine divK_loop_n1_call_unified_v5_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 scratchMem base halign
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

open EvmAsm.Rv64

/-- j=0-entry iteration state (after the j=3, j=2, j=1 digits). -/
def fullN1S0 (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0 : Word) :=
  let s1 := fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1
  iterN1Call_v5 v0 v1 v2 v3 u0_orig_0 s1.2.1 s1.2.2.1 s1.2.2.2.1 s1.2.2.2.2.1

/-- `fullN1S0` at the normalized inputs equals the schoolbook final digit
    `fullDivN1R0V5 true true true true`. -/
theorem fullN1S0_eq_fullDivN1R0V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullN1S0 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1
    = fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullN1S0 fullN1S1 fullN1S2 fullDivN1R0V5 fullDivN1R1V5 fullDivN1R2V5 fullDivN1R3V5
  simp only [iterN1V5_true]

end EvmAsm.Evm64
