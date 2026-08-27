/-
  EvmAsm.Evm64.DivMod.LoopIterN4V5.CallSkipV5NoNop

  v5 n=4 call+skip loop body (j=0) over `sharedDivModCodeNoNop_v5`.  Mirror of
  the v4 n=4 call+skip body (`LoopIterN4CallV4NoNop`,
  `divK_loop_body_n4_call_skip_j0_v4_spec_within_noNop`), but using the v5 NAMED
  trial-call-full post (`divKTrialCallFullPostV5Named`) — the compact named post
  that keeps the v5 Knuth-D quotient terms from blowing up `dsimp`/`xperm` — plus
  the v5 bricks (mulsub correction-skip, store-loop).  Same shape as the n=3 v5
  call+skip body (`LoopIterN3V5/CallSkipV5NoNop`) with the trial window at digit 4
  (uHi=uTop, uLo=u3, vTop=v3) and the n=4 glue lemmas / pre defs.
  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.LoopIterN4CallV4NoNop
public import EvmAsm.Evm64.DivMod.LoopBody.TrialCallFullV5Named
public import EvmAsm.Evm64.DivMod.LoopBody.MulsubSkipV5
public import EvmAsm.Evm64.DivMod.LoopBody.StoreLoopV5

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=4 call+skip j=0 loop-body post (mirror of `loopBodyN4CallSkipJ0PostV4`
    with v5 trial defs; n=4 trial window uHi=uTop uLo=u3 vTop=v3). -/
@[irreducible]
def loopBodyN4CallSkipJ0PostV5
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
  (sp + signExtend12 3936 ↦ₘ scratchOut) **
  regOwn .x1

/-- v5 n=4 call+skip j=0 loop body over `sharedDivModCodeNoNop_v5` (158 steps,
    loopBodyOff → denormOff).  Mirror of the v4 analog with the v5 NAMED trial. -/
theorem divK_loop_body_n4_call_skip_j0_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopBodyN4CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN4CallSkipJ0PostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  unfold loopBodyN4CallSkipJ0PreV4
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
  have TF := divK_trial_call_full_v5_named_spec_within_noNop sp (0 : Word) (4 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    uTop u3 v3 retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV5Named at TF
  dsimp only [] at TF
  rw [u_addr_eq_n4] at TF
  rw [u_addr8_eq_n4] at TF
  rw [vtop_eq_v3_n4] at TF
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
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN4CallSkipJ0Pre_unfold] at hp
      xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN4CallSkipJ0PostV5
      unfold loopBodyN4SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

end EvmAsm.Evm64
