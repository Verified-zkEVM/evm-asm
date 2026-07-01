/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopCallExactX1Mod

  v5/no-NOP n=3 call-path exact-x1 loop-iteration wrappers over `modCode_noNop_v5`,
  exposing the unified scratch loop-iteration post `loopIterPostN3CallScratchNoX1`
  (with concrete `x1 = raVal`).  Lifts the four v5 call exact-x1 raws
  (CallSkipExactX1V5NoNop #7513, CallAddbackBeqExactX1V5NoNop #7515) via
  `cpsTripleWithin_extend_code`, converts each to the scratch post through the
  shared `loopIterPostN3CallScratchNoX1_{skip,addback}` rewrites, then dispatches
  on the computed mulsub borrow bit (`by_cases`) to give the call exact-jN bodies
  (j=0 / j=1).  Mirror of the v4 analogs (`FullPathN3V4NoNop` :338/:390/:442/
  :494/:547/:588); the only deviation is the v5 inline borrow/carry hypotheses
  (vs the v4 named props) bridged through `mulsubN4_c3 = (mulsubN4 …).2.2.2.2`.
  Bead `evm-asm-wbc4i.9.3.3.2.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN3V5.CallSkipExactX1V5NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3V5.CallAddbackBeqExactX1V5NoNop
import EvmAsm.Evm64.DivMod.Compose.V5NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Loop body n=3, call+skip, j=0 over `modCode_noNop_v5`, preserving concrete
    `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_skip_j0_exact_loopIterScratch_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopBodyN3CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV5QHat u3 u2 v2)
        (divKTrialCallV5DLo v2)
        (divKTrialCallV5Un0 u2)
        (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      ¬BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) := by
    unfold mulsubN4NoBorrow at hborrow
    dsimp only [] at hborrow
    intro hlt
    unfold mulsubN4_c3 at hlt
    rw [if_pos hlt] at hborrow
    exact (by decide : (1 : Word) ≠ (0 : Word)) hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      have hpost :
          ((loopBodyN3CallSkipPostJScratchNoX1 sp base (0 : Word)
            (divKTrialCallV5QHat u3 u2 v2)
            (divKTrialCallV5DLo v2)
            (divKTrialCallV5Un0 u2)
            (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop) ** (.x1 ↦ᵣ raVal)) h := by
        unfold loopBodyN3CallSkipJ0PostV5NoX1 at hp
        unfold loopBodyN3CallSkipPostJScratchNoX1
        simpa only [sepConj_assoc'] using hp
      rw [loopIterPostN3CallScratchNoX1_skip hb] at hpost
      exact hpost)
    (cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5)
      (divK_loop_body_n3_call_skip_j0_v5_spec_within_noNop_exact_x1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow))

/-- Loop body n=3, call+skip, j=1 over `modCode_noNop_v5`, preserving concrete
    `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_skip_j1_exact_loopIterScratch_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
      (loopBodyN3CallSkipJgt0PreV4NoX1 sp (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base (1 : Word)
        (divKTrialCallV5QHat u3 u2 v2)
        (divKTrialCallV5DLo v2)
        (divKTrialCallV5Un0 u2)
        (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      ¬BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) := by
    unfold mulsubN4NoBorrow at hborrow
    dsimp only [] at hborrow
    intro hlt
    unfold mulsubN4_c3 at hlt
    rw [if_pos hlt] at hborrow
    exact (by decide : (1 : Word) ≠ (0 : Word)) hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      have hpost :
          ((loopBodyN3CallSkipPostJScratchNoX1 sp base (1 : Word)
            (divKTrialCallV5QHat u3 u2 v2)
            (divKTrialCallV5DLo v2)
            (divKTrialCallV5Un0 u2)
            (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop) ** (.x1 ↦ᵣ raVal)) h := by
        unfold loopBodyN3CallSkipJgt0PostV5NoX1 at hp
        unfold loopBodyN3CallSkipPostJScratchNoX1
        simpa only [sepConj_assoc'] using hp
      rw [loopIterPostN3CallScratchNoX1_skip hb] at hpost
      exact hpost)
    (cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5)
      (divK_loop_body_n3_call_skip_j1_v5_spec_within_noNop_exact_x1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow))

/-- Loop body n=3, call+addback, j=0 over `modCode_noNop_v5`, preserving concrete
    `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_addback_j0_exact_loopIterScratch_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u3 u2 v2
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopBodyN3CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV5QHat u3 u2 v2)
        (divKTrialCallV5DLo v2)
        (divKTrialCallV5Un0 u2)
        (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) := by
    by_contra hlt
    unfold mulsubN4_c3 at hlt
    rw [if_neg hlt] at hborrow
    exact hborrow rfl
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      have hpost :
          ((loopBodyN3CallAddbackBeqPostJScratchNoX1 sp base (0 : Word)
            (divKTrialCallV5QHat u3 u2 v2)
            (divKTrialCallV5DLo v2)
            (divKTrialCallV5Un0 u2)
            (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop) ** (.x1 ↦ᵣ raVal)) h := by
        unfold loopBodyN3CallAddbackJ0PostV5NoX1 at hp
        unfold loopBodyN3CallAddbackBeqPostJScratchNoX1
        simpa only [sepConj_assoc'] using hp
      rw [loopIterPostN3CallScratchNoX1_addback hb] at hpost
      exact hpost)
    (cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5)
      (divK_loop_body_n3_call_addback_j0_beq_v5_spec_within_noNop_exact_x1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz))

/-- Loop body n=3, call+addback, j>0 over `modCode_noNop_v5`, preserving concrete
    `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_addback_jgt0_exact_loopIterScratch_v5_noNop_modCode (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u3 u2 v2
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
      (loopBodyN3CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base j
        (divKTrialCallV5QHat u3 u2 v2)
        (divKTrialCallV5DLo v2)
        (divKTrialCallV5Un0 u2)
        (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) := by
    by_contra hlt
    unfold mulsubN4_c3 at hlt
    rw [if_neg hlt] at hborrow
    exact hborrow rfl
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      have hpost :
          ((loopBodyN3CallAddbackBeqPostJScratchNoX1 sp base j
            (divKTrialCallV5QHat u3 u2 v2)
            (divKTrialCallV5DLo v2)
            (divKTrialCallV5Un0 u2)
            (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop) ** (.x1 ↦ᵣ raVal)) h := by
        unfold loopBodyN3CallAddbackJgt0PostV5NoX1 at hp
        unfold loopBodyN3CallAddbackBeqPostJScratchNoX1
        simpa only [sepConj_assoc'] using hp
      rw [loopIterPostN3CallScratchNoX1_addback hb] at hpost
      exact hpost)
    (cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5)
      (divK_loop_body_n3_call_addback_jgt0_beq_v5_spec_within_noNop_exact_x1 j hpos
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz))

/-- Loop body n=3, call path, j=0 over `modCode_noNop_v5`, selecting the skip or
    addback correction from the computed mulsub borrow bit (call exact-jN). -/
theorem divK_loop_body_n3_call_j0_exact_loopIterScratch_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u3 u2 v2
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopBodyN3CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV5QHat u3 u2 v2)
        (divKTrialCallV5DLo v2)
        (divKTrialCallV5Un0 u2)
        (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow : BitVec.ult uTop
      (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word) := by
      unfold mulsubN4_c3 at hborrow
      rw [if_pos hborrow]; decide
    exact divK_loop_body_n3_call_addback_j0_exact_loopIterScratch_v5_noNop_modCode
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_nz hcarry2_nz
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      divK_loop_body_n3_call_skip_j0_exact_loopIterScratch_v5_noNop_modCode
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_zero

/-- Loop body n=3, call path, j=1 over `modCode_noNop_v5`, selecting the skip or
    addback correction from the computed mulsub borrow bit (call exact-jN). -/
theorem divK_loop_body_n3_call_j1_exact_loopIterScratch_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u3 u2 v2
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
      (loopBodyN3CallSkipJgt0PreV4NoX1 sp (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base (1 : Word)
        (divKTrialCallV5QHat u3 u2 v2)
        (divKTrialCallV5DLo v2)
        (divKTrialCallV5Un0 u2)
        (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow : BitVec.ult uTop
      (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word) := by
      unfold mulsubN4_c3 at hborrow
      rw [if_pos hborrow]; decide
    exact divK_loop_body_n3_call_addback_jgt0_exact_loopIterScratch_v5_noNop_modCode
      (1 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_nz hcarry2_nz
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      divK_loop_body_n3_call_skip_j1_exact_loopIterScratch_v5_noNop_modCode
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_zero

end EvmAsm.Evm64
