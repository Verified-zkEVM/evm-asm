/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopLoopBodyConditional

  Conditional-carry wrappers for the n=1 v4/no-NOP full DIV loop body.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopLoopBody

public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)
open EvmAsm.Evm64.DivMod.AddrNorm
  (jpred_1 jpred_2 jpred_3 slt_jpos_1 slt_jpos_2 slt_jpos_3)

/-- Loop body n=1, max path, j>0 over `divCode_noNop_v4`, requiring the
    double-addback progress fact only when the addback branch is taken. -/
theorem divK_loop_body_n1_max_jgt0_exact_loopIter_v4_noNop_if_borrow (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_if : isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 j
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hb : BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hb]
      decide
    have raw := divK_loop_body_n1_max_addback_jgt0_beq_v4_spec_within_noNop
      j hpos
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      base hbltu (hcarry2_if hborrow)
    change (let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
      let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
      (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
       then (1 : Word) else 0) ≠ (0 : Word) →
      cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff)
        (sharedDivModCodeNoNop_v4 base)
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
        (loopBodyN1AddbackBeqPost sp j (signExtend12 4095 : Word)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop)) at raw
    have raw0 := raw hborrow
    have raw' := cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw0
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw'
    exact cpsTripleWithin_weaken
      (fun h hp => by
        delta loopBodyN1MaxSkipJgt0NormPreV4 at hp
        xperm_hyp hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_addback hb]
        exact hp)
      framed
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have raw := divK_loop_body_n1_max_skip_jgt0_norm_v4_noNop
      j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_skip hb]
        exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) framed)

/-- Loop body n=1, max path, j=0 over `divCode_noNop_v4`, requiring the
    double-addback progress fact only when the addback branch is taken. -/
theorem divK_loop_body_n1_max_j0_exact_loopIter_v4_noNop_if_borrow (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_if : isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN1MaxSkipJ0NormPreV4
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hb : BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hb]
      decide
    have raw := divK_loop_body_n1_max_addback_j0_beq_v4_spec_within_noNop
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      base hbltu (hcarry2_if hborrow)
    change (let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
      let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
      (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
       then (1 : Word) else 0) ≠ (0 : Word) →
      cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff)
        (sharedDivModCodeNoNop_v4 base)
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
        (loopBodyN1AddbackBeqPost sp (0 : Word) (signExtend12 4095 : Word)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop)) at raw
    have raw0 := raw hborrow
    have raw' := cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw0
    simp only [se12_32, se12_40, se12_48, se12_56,
               u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
               u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw'
    exact cpsTripleWithin_weaken
      (fun h hp => by
        delta loopBodyN1MaxSkipJ0NormPreV4 at hp
        xperm_hyp hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_addback hb]
        exact hp)
      framed
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have raw := divK_loop_body_n1_max_skip_j0_norm_v4_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_skip hb]
        exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) framed)

/-- Exact-`x1` N1 two-iteration max/max path over `divCode_noNop_v4`,
    threading max carry evidence only through taken addback branches. -/
theorem divK_loop_n1_iter10_maxmax_exact_x1_v4_noNop_selected_carry_if_borrow (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_1 : ¬BitVec.ult u1 v0)
    (hbltu_0 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hcarry2_j1 : isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_j0 : isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0Orig
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1) :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN1Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1Iter10PostNoX1 false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J1 := divK_loop_body_n1_max_jgt0_exact_loopIter_v4_noNop_if_borrow
    (1 : Word) sp base slt_jpos_1
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old raVal hbltu_1
    hcarry2_j1
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J1
  have J0 := divK_loop_body_n1_max_j0_exact_loopIter_v4_noNop_if_borrow
    sp base (1 : Word) ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old raVal hbltu_0
    hcarry2_j0
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      (q_addr_1 ↦ₘ (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1) **
      (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
      (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1Max loopExitPostN1 loopExitPost at hp
      delta loopBodyN1MaxSkipJ0NormPreV4 at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_n1_j1_0_eq_j0_4088, u_n1_j1_4088_eq_j0_4080,
          u_n1_j1_4080_eq_j0_4072, u_n1_j1_4072_eq_j0_4064] at hp
      dsimp only [u_base_0, u_base_1, q_addr_0, q_addr_1] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56,
                 u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
                 u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN1Iter10PreWithScratchNoX1 loopN1Iter10Pre at hp
      delta loopBodyN1MaxSkipJgt0NormPreV4 at ⊢
      xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter10PostNoX1 loopIterPostN1NoX1 loopIterPostN1Max at hp ⊢
      simp only [iterN1_false, sepConj_emp_right'] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- Exact-`x1` N1 three-iteration all-max path over `divCode_noNop_v4`,
    threading max carry evidence only through taken addback branches. -/
theorem divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry_if_borrow (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_2 : ¬BitVec.ult u1 v0)
    (hbltu_1 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_0 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hcarry2_j2 : isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_j1 : isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0Orig1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    (hcarry2_j0 : isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0Orig0
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1) :
    cpsTripleWithin 556 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN1Iter210PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1Iter210PostNoX1 false false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0 retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  let r2 := iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J2 := divK_loop_body_n1_max_jgt0_exact_loopIter_v4_noNop_if_borrow
    (2 : Word) sp base slt_jpos_2
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old raVal hbltu_2
    hcarry2_j2
  have J2f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 0) ↦ₘ u0Orig1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0Orig0) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J2
  have H10 := divK_loop_n1_iter10_maxmax_exact_x1_v4_noNop_selected_carry_if_borrow
    sp base (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3
    u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    u0Orig0 q1Old q0Old
    retMem dMem dloMem scratch_un0 raVal hbltu_1 hbltu_0 hcarry2_j1 hcarry2_j0
  have H10f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) H10
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1Max loopExitPostN1 loopExitPost at hp
      delta loopN1Iter10PreWithScratchNoX1 loopN1Iter10Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_2
      rw [hj', u_n1_j2_0_eq_j1_4088, u_n1_j2_4088_eq_j1_4080,
          u_n1_j2_4080_eq_j1_4072, u_n1_j2_4072_eq_j1_4064] at hp
      dsimp only [u_base_0, u_base_1, u_base_2, q_addr_0, q_addr_1, q_addr_2] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f H10f
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN1Iter210PreWithScratchNoX1 loopN1Iter210Pre at hp
      delta loopBodyN1MaxSkipJgt0NormPreV4 at ⊢
      dsimp only [u_base_0, u_base_1, u_base_2, q_addr_0, q_addr_1, q_addr_2] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter210PostNoX1 loopN1Iter10PostNoX1
        loopIterPostN1NoX1 loopIterPostN1Max at hp ⊢
      simp only [iterN1_false, Bool.false_eq_true, if_false, sepConj_emp_right'] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- Exact-`x1` N1 four-iteration all-max path over `divCode_noNop_v4`,
    threading max carry evidence only through taken addback branches. -/
theorem divK_loop_n1_maxmaxmaxmax_exact_x1_v4_noNop_selected_carry_if_borrow (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_3 : ¬BitVec.ult u1 v0)
    (hbltu_2 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hbltu_0 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1 v0)
    (hcarry2_j3 : isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_j2 : isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0Orig2
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    (hcarry2_j1 : isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0Orig1
      (iterN1Max v0 v1 v2 v3 u0Orig2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
      (iterN1Max v0 v1 v2 v3 u0Orig2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
      (iterN1Max v0 v1 v2 v3 u0Orig2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0Orig2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1)
    (hcarry2_j0 : isAddbackCarry2NzN1MaxIfBorrow v0 v1 v2 v3 u0Orig0
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.2.1
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.2.2.2.1) :
    cpsTripleWithin 758 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1UnifiedPostNoX1 false false false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  let r3 := iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := iterN1Max v0 v1 v2 v3 u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
  let r1 := iterN1Max v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J3 := divK_loop_body_n1_max_jgt0_exact_loopIter_v4_noNop_if_borrow
    (3 : Word) sp base slt_jpos_3
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q3Old raVal hbltu_3
    hcarry2_j3
  have J3f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 0) ↦ₘ u0Orig2) ** (q_addr_2 ↦ₘ q2Old) **
     ((u_base_1 + signExtend12 0) ↦ₘ u0Orig1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0Orig0) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J3
  have H210 := divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry_if_borrow
    sp base (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) u_base_3 q_addr_3
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r3.1 r3.2.2.2.2.1
    v0 v1 v2 v3
    u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    u0Orig1 u0Orig0 q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 raVal hbltu_2 hbltu_1 hbltu_0
    hcarry2_j2 hcarry2_j1 hcarry2_j0
  have H210f := cpsTripleWithin_frameR
    (((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1))
    (by pcFree) H210
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1Max loopExitPostN1 loopExitPost at hp
      delta loopN1Iter210PreWithScratchNoX1 loopN1Iter210Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_3
      rw [hj', u_n1_j3_0_eq_j2_4088, u_n1_j3_4088_eq_j2_4080,
          u_n1_j3_4080_eq_j2_4072, u_n1_j3_4072_eq_j2_4064] at hp
      dsimp only [u_base_0, u_base_1, u_base_2, u_base_3,
        q_addr_0, q_addr_1, q_addr_2, q_addr_3] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J3f H210f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN1PreWithScratchNoX1 loopN1Pre at hp
      delta loopBodyN1MaxSkipJgt0NormPreV4 at ⊢
      dsimp only [u_base_0, u_base_1, u_base_2, u_base_3,
        q_addr_0, q_addr_1, q_addr_2, q_addr_3] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      delta loopN1UnifiedPostNoX1 loopN1Iter210PostNoX1 loopN1Iter10PostNoX1
        loopIterPostN1NoX1 loopIterPostN1Max at hp ⊢
      simp only [iterN1_false, Bool.false_eq_true, if_false, sepConj_emp_right'] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

end EvmAsm.Evm64
