/-
  EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionAddbackV5NoNop

  v5 mulsub + correction-ADDBACK loop-body bricks over `sharedDivModCodeNoNop_v5`.

  The mulsub + addback instructions run AFTER the `div128` subroutine (the only
  block that differs between v4 and v5), so these are mechanical mirrors of the v4
  specs (`MulsubCorrectionAddback`), swapping the code surface
  `sharedDivModCodeNoNop_v4 → _v5` and the code-subsumption lemma
  `lb_sub_noNop_v4 → lb_sub_noNop_v5` (same pattern as `MulsubSkipV5`).

  Unlike the n=1 loop (single-limb divisor ⇒ exact floor ⇒ no borrow ⇒ skip
  path), the n=2/n=3/n=4 loops have a multi-limb divisor where the trial can
  overshoot and the addback FIRES — so these addback bricks are needed for the
  v5 n≥2 loop bodies.  First brick: the `BEQ` passthrough taken on the
  single-addback path (`carry ≠ 0`).  Bead `evm-asm-wbc4i.9.2`.
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionAddback
public import EvmAsm.Evm64.DivMod.LoopBody.DoubleAddbackBeqV4NoNop
public import EvmAsm.Evm64.DivMod.LoopBody.MulsubSkipV5
public import EvmAsm.Evm64.DivMod.Compose.V5Code

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- v5 no-NOP variant of `divK_beq_passthrough_v4_spec_within_noNop`: on the
    single-addback path (`carry ≠ 0`) the addback `BEQ` is not taken, so control
    falls through to the store-loop.  Mechanical mirror of the v4 proof with the
    v5 code subsumption. -/
theorem divK_beq_passthrough_v5_spec_within_noNop {carry : Word} (base : Word) (hne : carry ≠ 0) :
    cpsTripleWithin 1 (base + addbackBeqOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v5 base)
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x7 .x0 (8044 : BitVec 13) carry 0 (base + addbackBeqOff)
  rw [lb_beq_back_ntaken_local] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop_v5 108 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have ntaken := cpsBranchWithin_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hne hpure)
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    ntaken

/-- v5 full add-back correction over `sharedDivModCodeNoNop_v5` — instantiation of
    the generic `divK_addback_full_spec_within_of_sub` with the v5 code
    subsumption.  Mirror of `divK_addback_full_named_v4_spec_within_noNop`. -/
theorem divK_addback_full_named_v5_spec_within_noNop
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v7_init v5_init v2_init : Word) (base : Word) :
    cpsTripleWithin 37 (base + addbackInitOff) (base + addbackBeqOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ v7_init) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5_init) ** (.x2 ↦ᵣ v2_init) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4))
      (addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4) :=
  cpsTripleWithin_weaken
    (fun h hp => by unfold addbackFullPre; exact hp)
    (fun h hp => hp)
    (divK_addback_full_spec_within_of_sub sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
      v7_init v5_init v2_init base (sharedDivModCodeNoNop_v5 base) lb_sub_noNop_v5)

private theorem lb_double_addback_beq_ntaken_v5 {base : Word} :
    (base + addbackBeqOff : Word) + 4 = base + storeLoopOff := by bv_addr

private theorem lb_double_addback_beq_taken_v5 {base : Word} :
    (base + addbackBeqOff : Word) + signExtend13 (8044 : BitVec 13) = base + addbackInitOff := by rv64_addr

/-- v5 double-addback BEQ helper over `sharedDivModCodeNoNop_v5`.  Mirror of
    `divK_double_addback_beq_v4_spec_within_noNop` with the v5 code surface and the
    v5 addback-full / beq-passthrough bricks. -/
theorem divK_double_addback_beq_v5_spec_within_noNop
    (sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4 : Word)
    (base : Word)
    (hcarry2_nz : addbackN4_carry aun0 aun1 aun2 aun3 v0 v1 v2 v3 ≠ 0) :
    let upc0' := aun0 + (signExtend12 0 : Word)
    let ac1_0' := if BitVec.ult upc0' (signExtend12 0 : Word) then (1 : Word) else 0
    let aun0' := upc0' + v0
    let ac2_0' := if BitVec.ult aun0' v0 then (1 : Word) else 0
    let aco0' := ac1_0' ||| ac2_0'
    let upc1' := aun1 + aco0'
    let ac1_1' := if BitVec.ult upc1' aco0' then (1 : Word) else 0
    let aun1' := upc1' + v1
    let ac2_1' := if BitVec.ult aun1' v1 then (1 : Word) else 0
    let aco1' := ac1_1' ||| ac2_1'
    let upc2' := aun2 + aco1'
    let ac1_2' := if BitVec.ult upc2' aco1' then (1 : Word) else 0
    let aun2' := upc2' + v2
    let ac2_2' := if BitVec.ult aun2' v2 then (1 : Word) else 0
    let aco2' := ac1_2' ||| ac2_2'
    let upc3' := aun3 + aco2'
    let ac1_3' := if BitVec.ult upc3' aco2' then (1 : Word) else 0
    let aun3' := upc3' + v3
    let ac2_3' := if BitVec.ult aun3' v3 then (1 : Word) else 0
    let aco3' := ac1_3' ||| ac2_3'
    let aun4' := aun4 + aco3'
    let qHat'' := qHat' + signExtend12 4095
    cpsTripleWithin 39 (base + addbackBeqOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ qHat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
       ((uBase + signExtend12 4064) ↦ₘ aun4))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ aco3') **
       (.x11 ↦ᵣ qHat'') ** (.x5 ↦ᵣ aun4') ** (.x2 ↦ᵣ aun3') ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0') **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1') **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2') **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3') **
       ((uBase + signExtend12 4064) ↦ₘ aun4')) := by
  intro upc0' ac1_0' aun0' ac2_0' aco0' upc1' ac1_1' aun1' ac2_1' aco1'
        upc2' ac1_2' aun2' ac2_2' aco2' upc3' ac1_3' aun3' ac2_3' aco3' aun4' qHat''
  have hbeq := beq_spec_gen_within .x7 .x0 (8044 : BitVec 13) (0 : Word) 0 (base + addbackBeqOff)
  rw [lb_double_addback_beq_taken_v5, lb_double_addback_beq_ntaken_v5] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop_v5 108 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have beq_taken := cpsBranchWithin_takenPath hbeq_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure rfl)
  have beq_taken' := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    beq_taken
  have AB2 := divK_addback_full_named_v5_spec_within_noNop sp uBase qHat' v0 v1 v2 v3
    aun0 aun1 aun2 aun3 aun4 (0 : Word) aun4 aun3 base
  simp only [addbackFullPost_unfold] at AB2
  have haco3_nz : aco3' ≠ 0 := by
    unfold addbackN4_carry at hcarry2_nz
    simp only [] at hcarry2_nz
    exact hcarry2_nz
  have BPT := divK_beq_passthrough_v5_spec_within_noNop base haco3_nz
  have beq_f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) **
     (.x11 ↦ᵣ qHat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
     ((uBase + signExtend12 4064) ↦ₘ aun4))
    (by pcFree) beq_taken'
  have beq_ab2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) beq_f AB2
  have BPTf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) **
     (.x11 ↦ᵣ qHat'') ** (.x5 ↦ᵣ aun4') ** (.x2 ↦ᵣ aun3') **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0') **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1') **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2') **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3') **
     ((uBase + signExtend12 4064) ↦ₘ aun4'))
    (by pcFree) BPT
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) beq_ab2 BPTf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    full

/-- Named-postcondition v5 wrapper for the double-addback BEQ helper. -/
theorem divK_double_addback_beq_named_v5_spec_within_noNop
    (sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4 : Word)
    (base : Word)
    (hcarry2_nz : addbackN4_carry aun0 aun1 aun2 aun3 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 39 (base + addbackBeqOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ qHat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
       ((uBase + signExtend12 4064) ↦ₘ aun4))
      (n4DoubleAddbackNamedPost sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4) :=
  cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by simp only [n4DoubleAddbackNamedPost_unfold]; exact hp)
    (divK_double_addback_beq_v5_spec_within_noNop sp uBase qHat' v0 v1 v2 v3
      aun0 aun1 aun2 aun3 aun4 base hcarry2_nz)

/-- v5 correction addback over `sharedDivModCodeNoNop_v5` (addback result hidden
    behind `addbackFullPost`).  Mirror of `divK_correction_addback_named_v4`. -/
theorem divK_correction_addback_named_v5_spec_within_noNop
    (sp uBase borrow qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5Old v2Old : Word) (base : Word)
    (hb : borrow ≠ (0 : Word)) :
    cpsTripleWithin 38 (base + correctionSkipBeqOff) (base + addbackBeqOff) (sharedDivModCodeNoNop_v5 base)
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
    lb_sub_noNop_v5 70 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have ntaken := cpsBranchWithin_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hb hpure)
  have ntaken_clean : cpsTripleWithin 1 (base + correctionSkipBeqOff) (base + addbackInitOff) (sharedDivModCodeNoNop_v5 base)
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
  have AB := divK_addback_full_named_v5_spec_within_noNop sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
    borrow v5Old v2Old base
  seqFrame ntaken_framed AB
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by exact hq)
    ntaken_framedAB

/-- v5 mulsub + correction-addback (91 steps, div128CallRetOff→addbackBeqOff) over
    `sharedDivModCodeNoNop_v5`.  Mirror of
    `divK_mulsub_correction_addback_named_880_v4`: `divK_mulsub_full_v5` seqFrame
    `divK_correction_addback_named_v5`. -/
theorem divK_mulsub_correction_addback_named_880_v5_spec_within_noNop
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 then (1 : Word) else 0) ≠
      (0 : Word) →
    cpsTripleWithin 91 (base + div128CallRetOff) (base + addbackBeqOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x9 ↦ᵣ v1Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop))
      (n4McaNamed880Post sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase hborrow
  have MS := divK_mulsub_full_v5_spec_within_noNop sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v1Old v5Old v6Old v7Old v10Old v2Old base
  unfold divKMulsubFullPre divKMulsubFullPost at MS
  unfold mulsubN4 at hborrow
  dsimp only [] at MS hborrow
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  have CA := divK_correction_addback_named_v5_spec_within_noNop sp uBase
    (if BitVec.ult uTop c3 then (1 : Word) else 0)
    qHat v0 v1 v2 v3 un0 un1 un2 un3 u4_new
    u4_new un3 base hborrow
  seqFrame MS CA
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      rw [addbackFullPost_unfold] at hq
      simp only [n4McaNamed880Post_unfold]
      unfold mulsubN4 addbackN4 addbackN4_carry
      xperm_hyp hq)
    MSCA

/-- v5 mulsub + correction-addback + BEQ (130 steps, div128CallRetOff→storeLoopOff)
    over `sharedDivModCodeNoNop_v5`.  Mirror of
    `divK_mulsub_correction_addback_beq_v4_spec_within_noNop`. -/
theorem divK_mulsub_correction_addback_beq_v5_spec_within_noNop
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
    let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
                 else qHat + signExtend12 4095
    let un0Out := if carry = 0 then ab'.1 else ab.1
    let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
    let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
    let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
    let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
    let carryOut := if carry = 0 then
        addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
      else carry
    (carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) →
    (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 130 (base + div128CallRetOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x9 ↦ᵣ v1Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_out) **
       (.x9 ↦ᵣ j) ** (.x5 ↦ᵣ u4_out) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ carryOut) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
       ((uBase + signExtend12 4064) ↦ₘ u4_out)) := by
  intro uBase ms c3 carry ab ab' q_out un0Out un1Out un2Out un3Out u4_out carryOut
        hcarry2_nz hborrow
  by_cases hcarry : carry = 0
  · have hq : q_out = qHat + signExtend12 4095 + signExtend12 4095 := if_pos hcarry
    have h0 : un0Out = ab'.1 := if_pos hcarry
    have h1 : un1Out = ab'.2.1 := if_pos hcarry
    have h2 : un2Out = ab'.2.2.1 := if_pos hcarry
    have h3 : un3Out = ab'.2.2.2.1 := if_pos hcarry
    have h4 : u4_out = ab'.2.2.2.2 := if_pos hcarry
    have hc : carryOut = addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 := if_pos hcarry
    rw [hq, h0, h1, h2, h3, h4, hc]
    have MCA_N := (divK_mulsub_correction_addback_named_880_v5_spec_within_noNop
      sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
      v1Old v5Old v6Old v7Old v10Old v2Old base) hborrow
    simp only [n4McaNamed880Post_unfold] at MCA_N
    rw [show addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = (0 : Word) from hcarry] at MCA_N
    have hcarry2 : addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 :=
      hcarry2_nz hcarry
    have DA := divK_double_addback_beq_named_v5_spec_within_noNop sp uBase
      (qHat + signExtend12 4095) v0 v1 v2 v3
      ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2
      base hcarry2
    rw [n4DoubleAddbackNamedPost_unfold] at DA
    have DAf := cpsTripleWithin_frameR
      ((.x9 ↦ᵣ j) ** (.x10 ↦ᵣ c3) **
       (sp + signExtend12 3976 ↦ₘ j))
      (by pcFree) DA
    have full := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) MCA_N DAf
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      full
  · have hq : q_out = qHat + signExtend12 4095 := if_neg hcarry
    have h0 : un0Out = ab.1 := if_neg hcarry
    have h1 : un1Out = ab.2.1 := if_neg hcarry
    have h2 : un2Out = ab.2.2.1 := if_neg hcarry
    have h3 : un3Out = ab.2.2.2.1 := if_neg hcarry
    have h4 : u4_out = ab.2.2.2.2 := if_neg hcarry
    have hc : carryOut = carry := if_neg hcarry
    rw [hq, h0, h1, h2, h3, h4, hc]
    have MCA_N := (divK_mulsub_correction_addback_named_880_v5_spec_within_noNop
      sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
      v1Old v5Old v6Old v7Old v10Old v2Old base) hborrow
    simp only [n4McaNamed880Post_unfold] at MCA_N
    have BEQ := divK_beq_passthrough_v5_spec_within_noNop base hcarry
    have BEQf := cpsTripleWithin_frameR
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ (qHat + signExtend12 4095)) **
       (.x9 ↦ᵣ j) ** (.x5 ↦ᵣ ab.2.2.2.2) ** (.x6 ↦ᵣ uBase) **
       (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ ab.2.2.2.1) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ ab.1) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ ab.2.1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ ab.2.2.1) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ ab.2.2.2.1) **
       ((uBase + signExtend12 4064) ↦ₘ ab.2.2.2.2))
      (by pcFree) BEQ
    have full := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) MCA_N BEQf
    exact cpsTripleWithin_mono_nSteps (nSteps' := 130) (by decide) <|
      cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      full

end EvmAsm.Evm64
