/-
  EvmAsm.Evm64.DivMod.LoopBody.MulsubSkipV5

  v5 mulsub + correction-skip loop-body brick over `sharedDivModCodeNoNop_v5`.

  Brick 4 of the v5 n=1 loop-body execution layer (bead `evm-asm-wbc4i.7.2`).
  The mulsub and correction-skip instructions are SHARED between v4 and v5 (they
  run after the `div128` subroutine, which is the only differing block), so these
  are mechanical mirrors of the v4 specs, swapping the code surface
  `sharedDivModCodeNoNop_v4` → `_v5` and the code-subsumption lemma
  `lb_sub_noNop_v4` → `lb_sub_noNop_v5`.  `divK_mulsub_full` reuses the generic
  `divK_mulsub_full_spec_within_of_sub`; `divK_correction_skip` and
  `divK_mulsub_correction_skip` mirror the v4 proofs verbatim.

  Feeds `divK_loop_body_n1_call_skip_*_v5` (next): since the v5 trial is the exact
  floor (`div128Quot_v5 = floor`), the single-limb mulsub leaves no borrow, so the
  loop body always takes the correction-SKIP path (no addback, no `Carry2NzAll`).
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionSkip
public import EvmAsm.Evm64.DivMod.Compose.V5Code

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 mulsub-full over `sharedDivModCodeNoNop_v5` — instantiation of the generic
    `divK_mulsub_full_spec_within_of_sub` with the v5 code subsumption. -/
theorem divK_mulsub_full_v5_spec_within_noNop
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v9Old v5Old v6Old v7Old v10Old v2Old : Word) (base : Word) :
    cpsTripleWithin 53 (base + div128CallRetOff) (base + correctionSkipBeqOff) (sharedDivModCodeNoNop_v5 base)
      (divKMulsubFullPre sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
        v9Old v5Old v6Old v7Old v10Old v2Old)
      (divKMulsubFullPost sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  unfold divKMulsubFullPre divKMulsubFullPost
  exact divK_mulsub_full_spec_within_of_sub sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v9Old v5Old v6Old v7Old v10Old v2Old base (sharedDivModCodeNoNop_v5 base) lb_sub_noNop_v5

/-- v5 correction-skip over `sharedDivModCodeNoNop_v5`: when borrow = 0, the BEQ
    is taken → jump past the addback.  Mechanical mirror of
    `divK_correction_skip_v4_spec_within_noNop`. -/
theorem divK_correction_skip_v5_spec_within_noNop
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5Old v2Old : Word) (base : Word) :
    cpsTripleWithin 1 (base + correctionSkipBeqOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v5 base)
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
    lb_sub_noNop_v5 70 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have skip := cpsBranchWithin_takenPath hbeq_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure rfl)
  have skip_clean : cpsTripleWithin 1 (base + correctionSkipBeqOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v5 base)
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

/-- v5 mulsub + correction-skip over `sharedDivModCodeNoNop_v5`.  Mechanical
    mirror of `divK_mulsub_correction_skip_v4_spec_within_noNop`, composing the
    v5 mulsub-full and correction-skip above. -/
theorem divK_mulsub_correction_skip_v5_spec_within_noNop
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    mulsubN4NoBorrow qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop →
    cpsTripleWithin 54 (base + div128CallRetOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v5 base)
      (divKMulsubCorrectionSkipPre sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
        v1Old v5Old v6Old v7Old v10Old v2Old)
      (n4McaNamedSkipPost sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have MS := divK_mulsub_full_v5_spec_within_noNop sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v1Old v5Old v6Old v7Old v10Old v2Old base
  unfold divKMulsubFullPre divKMulsubFullPost at MS
  unfold mulsubN4NoBorrow mulsubN4 at hborrow
  dsimp only [] at MS hborrow
  rw [hborrow] at MS
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let p0_lo := qHat * v0
  let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0
  let c0 := pc0 + bs0
  let p1_lo := qHat * v1
  let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1
  let c1 := pc1 + bs1
  let p2_lo := qHat * v2
  let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2
  let c2 := pc2 + bs2
  let p3_lo := qHat * v3
  let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3
  let c3 := pc3 + bs3
  let u4_new := uTop - c3
  have CS := divK_correction_skip_v5_spec_within_noNop sp uBase qHat v0 v1 v2 v3 un0 un1 un2 un3 u4_new
    u4_new un3 base
  seqFrame MS CS
  exact cpsTripleWithin_weaken
    (fun h hp => by unfold divKMulsubCorrectionSkipPre at hp; xperm_hyp hp)
    (fun h hq => by simp only [n4McaNamedSkipPost_unfold]; unfold mulsubN4; xperm_hyp hq)
    MSCS

end EvmAsm.Evm64
