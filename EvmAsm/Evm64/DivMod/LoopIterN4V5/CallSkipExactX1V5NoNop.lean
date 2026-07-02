/-
  EvmAsm.Evm64.DivMod.LoopIterN4V5.CallSkipExactX1V5NoNop

  v5 n=4 call+skip j=0 loop body over `sharedDivModCodeNoNop_v5`, preserving the
  concrete caller `x1` (= `raVal`) through the v5 div128 trial call — the
  exact-x1 variant the n=4 callable exact-frame lane consumes.  Mirror of the
  n=3 exact-x1 body (`LoopIterN3V5/CallSkipExactX1V5NoNop`) at the n=4 trial
  window (uHi=uTop, uLo=u3, vTop=v3) / n=4 addresses, and of the bundled n=4
  body (`LoopIterN4V5/CallSkipV5NoNop`) with the x1 atom kept concrete: the v5
  NAMED exact-x1 trial (`divK_trial_call_full_v5_named_spec_within_noNop_exact_x1`)
  + mulsub-correction-skip + exact-x1 store brick.  Toward `evm_div_callable_v5`.
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCallFullV5NamedExactX1
import EvmAsm.Evm64.DivMod.LoopBody.MulsubSkipV5
import EvmAsm.Evm64.DivMod.LoopBody.StoreLoopV5ExactX1
import EvmAsm.Evm64.DivMod.LoopIterN4CallV4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `loopBodyN4CallSkipJ0PreV4` minus the `regOwn .x1` atom (the caller frames
    the exact `x1` cell alongside).  Shared by the n=4 call-skip and
    call-addback-beq exact-x1 bodies. -/
@[irreducible]
def loopBodyN4CallSkipJ0PreV4NoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
   (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
   (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
   (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
   (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
   ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
   ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
   ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
   ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
   ((uBase + signExtend12 4064) ↦ₘ uTop) **
   (qAddr ↦ₘ qOld) **
   (sp + signExtend12 3968 ↦ₘ retMem) **
   (sp + signExtend12 3960 ↦ₘ dMem) **
   (sp + signExtend12 3952 ↦ₘ dloMem) **
   (sp + signExtend12 3944 ↦ₘ scratchUn0) **
   (sp + signExtend12 3936 ↦ₘ scratchMem))

/-- v5 n=4 call+skip j=0 loop-body post (no x1; mirror of
    `loopBodyN4CallSkipJ0PostV5` minus the `regOwn .x1` atom). -/
@[irreducible]
def loopBodyN4CallSkipJ0PostV5NoX1
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV5DLo v3
  let divUn0 := divKTrialCallV5Un0 u3
  let qHat := divKTrialCallV5QHat uTop u3 v3
  let scratchOut := divKTrialCallV5ScratchOut uTop u3 v3 scratchMem
  loopBodyN4SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v3) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ divUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut)

/-- v5 n=4 call+skip j=0 loop body preserving concrete `x1 = raVal`. -/
theorem divK_loop_body_n4_call_skip_j0_v5_spec_within_noNop_exact_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopBodyN4CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN4CallSkipJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  unfold loopBodyN4CallSkipJ0PreV4NoX1
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV5DHi v3
  let dLo := divKTrialCallV5DLo v3
  let divUn0 := divKTrialCallV5Un0 u3
  let q1'' := divKTrialCallV5Q1dd uTop u3 v3
  let q0'' := divKTrialCallV5Q0dd uTop u3 v3
  let x7Exit := divKTrialCallV5X7Exit uTop u3 v3
  let x9Exit := divKTrialCallV5X9Exit uTop u3 v3
  let qHat := divKTrialCallV5QHat uTop u3 v3
  let scratchOut := divKTrialCallV5ScratchOut uTop u3 v3 scratchMem
  have TF := divK_trial_call_full_v5_named_spec_within_noNop_exact_x1 sp (0 : Word) (4 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    uTop u3 v3 retMem dMem dloMem scratchUn0 scratchMem raVal base
    halign hbltu
  unfold divKTrialCallFullPostV5NamedExactX1 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n4] at TF
  rw [u_addr8_eq_n4] at TF
  rw [vtop_eq_v3_n4] at TF
  have MCS := divK_mulsub_correction_skip_v5_spec_within_noNop sp qHat (0 : Word)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
    hborrow
  unfold divKMulsubCorrectionSkipPre at MCS
  unfold n4McaNamedSkipPost at MCS
  unfold mulsubN4 at MCS
  dsimp only [] at MCS
  have MCS0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ raVal))
    (by pcFree) MCS
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
  have SL := divK_store_loop_j0_v5_spec_within_noNop_exact_x1 sp qHat u4_new (0 : Word) qOld raVal base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
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
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v3) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ divUn0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN4CallSkipJ0PostV5NoX1
      unfold loopBodyN4SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

end EvmAsm.Evm64
