module

public import EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionAddback

public section

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

private theorem lb_double_addback_beq_ntaken_v4 {base : Word} :
    (base + addbackBeqOff : Word) + 4 = base + storeLoopOff := by
  bv_addr

private theorem lb_double_addback_beq_taken_v4 {base : Word} :
    (base + addbackBeqOff : Word) + signExtend13 (8044 : BitVec 13) = base + addbackInitOff := by
  rv64_addr

/-- v4 no-NOP variant of the double-addback BEQ helper. -/
private theorem divK_double_addback_beq_v4_spec_within_noNop
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
    cpsTripleWithin 39 (base + addbackBeqOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v4 base)
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
  rw [lb_double_addback_beq_taken_v4, lb_double_addback_beq_ntaken_v4] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop_v4 108 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have beq_taken := cpsBranchWithin_takenPath hbeq_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure rfl)
  have beq_taken' := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    beq_taken
  have AB2 := divK_addback_full_named_v4_spec_within_noNop sp uBase qHat' v0 v1 v2 v3
    aun0 aun1 aun2 aun3 aun4 (0 : Word) aun4 aun3 base
  simp only [addbackFullPost_unfold] at AB2
  have haco3_nz : aco3' ≠ 0 := by
    unfold addbackN4_carry at hcarry2_nz
    simp only [] at hcarry2_nz
    exact hcarry2_nz
  have BPT := divK_beq_passthrough_v4_spec_within_noNop base haco3_nz
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

/-- Named-postcondition v4 no-NOP wrapper for the double-addback BEQ helper. -/
theorem divK_double_addback_beq_named_v4_spec_within_noNop
    (sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4 : Word)
    (base : Word)
    (hcarry2_nz : addbackN4_carry aun0 aun1 aun2 aun3 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 39 (base + addbackBeqOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ qHat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
       ((uBase + signExtend12 4064) ↦ₘ aun4))
      (n4DoubleAddbackNamedPost sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4) := by
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by simp only [n4DoubleAddbackNamedPost_unfold]; exact hp)
    (divK_double_addback_beq_v4_spec_within_noNop sp uBase qHat' v0 v1 v2 v3
      aun0 aun1 aun2 aun3 aun4 base hcarry2_nz)

end EvmAsm.Evm64
