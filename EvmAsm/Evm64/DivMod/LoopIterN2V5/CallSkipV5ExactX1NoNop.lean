/-
  EvmAsm.Evm64.DivMod.LoopIterN2V5.CallSkipV5ExactX1NoNop

  Exact-x1 ("preserving the concrete caller return address") variants of the v5
  n=2 call+skip loop bodies (j=0 + j>0) over `sharedDivModCodeNoNop_v5`.  Mirror
  of `divK_loop_body_n2_call_skip_{j0,jgt0}_v4_spec_within_noNop_exact_x1`
  (LoopIterN2CallV4NoNop) with the v5 NAMED exact-x1 trial (#7385) + the v5
  mulsub correction-skip + the v5 exact-x1 store-loop (#7386).  Needed by the
  iter-ready loop-back bodies that thread `.x1 ↦ᵣ raVal` through the loop.
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.TrialCallFullV5NamedExactX1
public import EvmAsm.Evm64.DivMod.LoopBody.MulsubSkipV5
public import EvmAsm.Evm64.DivMod.LoopBody.StoreLoopV5ExactX1
public import EvmAsm.Evm64.DivMod.LoopIterN2CallV4NoNop

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=2 call+skip j=0 NoX1 post (mirror of `loopBodyN2CallSkipJ0PostV4NoX1`
    with v5 trial defs). -/
@[irreducible]
def loopBodyN2CallSkipJ0PostV5NoX1
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV5DLo v1
  let divUn0 := divKTrialCallV5Un0 u1
  let qHat := divKTrialCallV5QHat u2 u1 v1
  let scratchOut := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
  loopBodyN2SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ divUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut)

/-- v5 n=2 call+skip j>0 NoX1 post (mirror of `loopBodyN2CallSkipJgt0PostV4NoX1`
    with v5 trial defs). -/
@[irreducible]
def loopBodyN2CallSkipJgt0PostV5NoX1
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV5DLo v1
  let divUn0 := divKTrialCallV5Un0 u1
  let qHat := divKTrialCallV5QHat u2 u1 v1
  let scratchOut := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
  loopBodyN2SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ divUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut)

/-- v5 n=2 call+skip j=0 loop body preserving the concrete caller `x1`
    (158 steps, loopBodyOff → denormOff). -/
theorem divK_loop_body_n2_call_skip_j0_v5_spec_within_noNop_exact_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopBodyN2CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallSkipJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  unfold loopBodyN2CallSkipJ0PreV4NoX1
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV5DHi v1
  let dLo := divKTrialCallV5DLo v1
  let divUn0 := divKTrialCallV5Un0 u1
  let q1'' := divKTrialCallV5Q1dd u2 u1 v1
  let q0'' := divKTrialCallV5Q0dd u2 u1 v1
  let x7Exit := divKTrialCallV5X7Exit u2 u1 v1
  let x9Exit := divKTrialCallV5X9Exit u2 u1 v1
  let qHat := divKTrialCallV5QHat u2 u1 v1
  let scratchOut := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
  have TF := divK_trial_call_full_v5_named_spec_within_noNop_exact_x1 sp (0 : Word) (2 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u2 u1 v1 retMem dMem dloMem scratchUn0 scratchMem raVal base
    halign hbltu
  unfold divKTrialCallFullPostV5NamedExactX1 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n2] at TF
  rw [u_addr8_eq_n2] at TF
  rw [vtop_eq_v1_n2] at TF
  have MCS0 := divK_mulsub_correction_skip_v5_spec_within_noNop sp qHat (0 : Word)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
    hborrow
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
  have SL := divK_store_loop_j0_v5_spec_within_noNop_exact_x1 sp qHat u4_new (0 : Word) qOld raVal base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
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
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v1) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ divUn0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN2CallSkipJ0PostV5NoX1
      unfold loopBodyN2SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- v5 n=2 call+skip j>0 loop body preserving the concrete caller `x1`
    (158 steps, loopBodyOff → loopBodyOff loop-back). -/
theorem divK_loop_body_n2_call_skip_jgt0_v5_spec_within_noNop_exact_x1 (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v5 base)
      (loopBodyN2CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallSkipJgt0PostV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  unfold loopBodyN2CallSkipJgt0PreV4NoX1
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV5DHi v1
  let dLo := divKTrialCallV5DLo v1
  let divUn0 := divKTrialCallV5Un0 u1
  let q1'' := divKTrialCallV5Q1dd u2 u1 v1
  let q0'' := divKTrialCallV5Q0dd u2 u1 v1
  let x7Exit := divKTrialCallV5X7Exit u2 u1 v1
  let x9Exit := divKTrialCallV5X9Exit u2 u1 v1
  let qHat := divKTrialCallV5QHat u2 u1 v1
  let scratchOut := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
  have TF := divK_trial_call_full_v5_named_spec_within_noNop_exact_x1 sp j (2 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u2 u1 v1 retMem dMem dloMem scratchUn0 scratchMem raVal base
    halign hbltu
  unfold divKTrialCallFullPostV5NamedExactX1 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n2] at TF
  rw [u_addr8_eq_n2] at TF
  rw [vtop_eq_v1_n2] at TF
  have MCS0 := divK_mulsub_correction_skip_v5_spec_within_noNop sp qHat j
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
    hborrow
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
  have SL := divK_store_loop_jgt0_v5_spec_within_noNop_exact_x1 sp j qHat u4_new
    (0 : Word) qOld raVal base hpos
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
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
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v1) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ divUn0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN2CallSkipJgt0PostV5NoX1
      unfold loopBodyN2SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

end EvmAsm.Evm64
