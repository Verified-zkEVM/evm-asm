/-
  Shared declaration home for the n=2 v5/no-NOP call, j=0 exit, and source.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNop
import EvmAsm.Evm64.DivMod.Compose.V5NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopMax
import EvmAsm.Evm64.DivMod.LoopIterN2V5.CallSkipV5ExactX1NoNop
import EvmAsm.Evm64.DivMod.LoopIterN2V5.CallAddbackV5ExactX1NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopMaxIter

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=2, call+skip, j=0 over `divCode_noNop_v5`, preserving `x1`. -/
theorem divK_loop_body_n2_call_skip_j0_norm_v5_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopBodyN2CallSkipJ0NormPreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallSkipJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5)
      (divK_loop_body_n2_call_skip_j0_v5_spec_within_noNop_exact_x1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow)
  unfold loopBodyN2CallSkipJ0PreV4NoX1 at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJ0NormPreV4NoX1 loopBodyN2MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=2, call+skip, j>0 over `divCode_noNop_v5`, preserving `x1`. -/
theorem divK_loop_body_n2_call_skip_jgt0_norm_v5_noNop_exact_x1 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallSkipJgt0PostV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5)
      (divK_loop_body_n2_call_skip_jgt0_v5_spec_within_noNop_exact_x1 j hpos
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow)
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJgt0NormPreV4NoX1 loopBodyN2MaxSkipJgt0NormPreV4 at hp
      unfold loopBodyN2CallSkipJgt0PreV4NoX1
      rw [loopBodyN2MaxJgt0Pre_unfold] at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=2, call+addback, j=0 over `divCode_noNop_v5`, preserving `x1`. -/
theorem divK_loop_body_n2_call_addback_j0_beq_norm_v5_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopBodyN2CallSkipJ0NormPreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallAddbackBeqJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5)
      (divK_loop_body_n2_call_addback_j0_beq_v5_spec_within_noNop_exact_x1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow hcarry2_nz)
  unfold loopBodyN2CallSkipJ0PreV4NoX1 at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJ0NormPreV4NoX1 loopBodyN2MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=2, call+addback, j>0 over `divCode_noNop_v5`, preserving `x1`. -/
theorem divK_loop_body_n2_call_addback_jgt0_beq_norm_v5_noNop_exact_x1 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallAddbackBeqJgt0PostV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop
        scratchMem ** (.x1 ↦ᵣ raVal)) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5)
      (divK_loop_body_n2_call_addback_jgt0_beq_v5_spec_within_noNop_exact_x1 j hpos
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow hcarry2_nz)
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJgt0NormPreV4NoX1 loopBodyN2MaxSkipJgt0NormPreV4 at hp
      unfold loopBodyN2CallSkipJgt0PreV4NoX1
      rw [loopBodyN2MaxJgt0Pre_unfold] at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- v5 n=2 max+addback j=0 norm body (mirror of the v4 analog; #7383 supplied
    only the j>0 case). -/
theorem divK_loop_body_n2_max_addback_j0_beq_norm_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopBodyN2MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2AddbackBeqPost sp (0 : Word) (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_addback_j0_beq_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hcarry2_nz hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5) raw
  rw [loopBodyN2MaxSkipJ0Pre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN2MaxSkipJ0NormPreV4
  exact raw'

/-- The v5 call+skip j=0 NoX1 post equals the generic scratch-form post with the
    v5 trial values (mirror of `loopBodyN2CallSkipJ0PostV4NoX1_eq_scratch`). -/
theorem loopBodyN2CallSkipJ0PostV5NoX1_eq_scratch
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN2CallSkipJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN2CallSkipPostJScratchNoX1 sp base (0 : Word)
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN2CallSkipJ0PostV5NoX1 loopBodyN2CallSkipPostJScratchNoX1
  rfl

/-- The v5 call+addback j=0 NoX1 post equals the generic scratch-form post with
    the v5 trial values (mirror of `loopBodyN2CallAddbackBeqJ0PostV4NoX1_eq_scratch`). -/
theorem loopBodyN2CallAddbackBeqJ0PostV5NoX1_eq_scratch
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN2CallAddbackBeqJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN2CallAddbackBeqPostJScratchNoX1 sp base (0 : Word)
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN2CallAddbackBeqJ0PostV5NoX1 loopBodyN2CallAddbackBeqPostJScratchNoX1
  rfl

/-- Unified j=0 N2 call iteration over v5/no-NOP code (loop exit), preserving
    concrete `x1` and exposing the v5 scratch cell in the final post. -/
theorem divK_loop_body_n2_call_j0_exact_loopIterScratch_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopBodyN2CallSkipJ0NormPreV4NoX1 sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
      (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word) := by
      unfold mulsubN4_c3 at hborrow
      rw [if_pos hborrow]; decide
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [loopBodyN2CallAddbackBeqJ0PostV5NoX1_eq_scratch] at hp
        rw [loopIterPostN2CallScratchNoX1_addback hborrow] at hp
        xperm_hyp hp)
      (divK_loop_body_n2_call_addback_j0_beq_norm_v5_noNop_exact_x1
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu hborrow_nz hcarry2_nz)
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          rw [loopBodyN2CallSkipJ0PostV5NoX1_eq_scratch] at hp
          rw [loopIterPostN2CallScratchNoX1_skip hborrow] at hp
          xperm_hyp hp)
        (divK_loop_body_n2_call_skip_j0_norm_v5_noNop_exact_x1
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

/-- Unified j=0 N2 max iteration over v5/no-NOP code (loop exit), preserving
    concrete `x1` and carrying the v5 scratch cells as frame. -/
theorem divK_loop_body_n2_max_j0_exact_loopIterScratch_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      ((loopBodyN2MaxSkipJ0NormPreV4 sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hborrow]
      decide
    have J := divK_loop_body_n2_max_addback_j0_beq_norm_v5_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hcarry2_nz hborrow_nz
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        rw [loopIterPostN2Max_addback hborrow] at hp
        xperm_hyp hp)
      Jf
  · have hborrow_zero :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := by
      rw [if_neg hborrow]
    have J := divK_loop_body_n2_max_skip_j0_norm_v5_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow_zero
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun h hp => by
          rw [loopIterPostN2Max_skip hborrow] at hp
          xperm_hyp hp)
        Jf

open EvmAsm.Rv64

/-- The v5 call+skip j>0 NoX1 post equals the generic scratch-form post with the
    v5 trial values (mirror of `loopBodyN2CallSkipJgt0PostV4NoX1_eq_scratch`). -/
theorem loopBodyN2CallSkipJgt0PostV5NoX1_eq_scratch
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN2CallSkipJgt0PostV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN2CallSkipPostJScratchNoX1 sp base j
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN2CallSkipJgt0PostV5NoX1 loopBodyN2CallSkipPostJScratchNoX1
  rfl

/-- The v5 call+addback j>0 NoX1 post equals the generic scratch-form post with
    the v5 trial values (mirror of `loopBodyN2CallAddbackBeqJgt0PostV4NoX1_eq_scratch`). -/
theorem loopBodyN2CallAddbackBeqJgt0PostV5NoX1_eq_scratch
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN2CallAddbackBeqJgt0PostV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN2CallAddbackBeqPostJScratchNoX1 sp base j
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN2CallAddbackBeqJgt0PostV5NoX1 loopBodyN2CallAddbackBeqPostJScratchNoX1
  rfl

/-- Unified j=2 N2 call iteration over v5/no-NOP code, preserving concrete `x1`
    and exposing the v5 scratch cell in the postcondition. -/
theorem divK_loop_body_n2_call_j2_exact_loopIterScratch_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 (2 : Word) sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
      (loopIterPostN2CallScratchNoX1 sp base (2 : Word)
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word) := by
      unfold mulsubN4_c3 at hborrow
      rw [if_pos hborrow]; decide
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [loopBodyN2CallAddbackBeqJgt0PostV5NoX1_eq_scratch] at hp
        rw [loopIterPostN2CallScratchNoX1_addback hborrow] at hp
        xperm_hyp hp)
      (divK_loop_body_n2_call_addback_jgt0_beq_norm_v5_noNop_exact_x1
        (2 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu hborrow_nz hcarry2_nz)
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          rw [loopBodyN2CallSkipJgt0PostV5NoX1_eq_scratch] at hp
          rw [loopIterPostN2CallScratchNoX1_skip hborrow] at hp
          xperm_hyp hp)
        (divK_loop_body_n2_call_skip_jgt0_norm_v5_noNop_exact_x1
          (2 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
          jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

/-- Unified j=1 N2 call iteration over v5/no-NOP code, preserving concrete `x1`
    and exposing the v5 scratch cell in the postcondition. -/
theorem divK_loop_body_n2_call_j1_exact_loopIterScratch_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 (1 : Word) sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
      (loopIterPostN2CallScratchNoX1 sp base (1 : Word)
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word) := by
      unfold mulsubN4_c3 at hborrow
      rw [if_pos hborrow]; decide
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [loopBodyN2CallAddbackBeqJgt0PostV5NoX1_eq_scratch] at hp
        rw [loopIterPostN2CallScratchNoX1_addback hborrow] at hp
        xperm_hyp hp)
      (divK_loop_body_n2_call_addback_jgt0_beq_norm_v5_noNop_exact_x1
        (1 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu hborrow_nz hcarry2_nz)
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          rw [loopBodyN2CallSkipJgt0PostV5NoX1_eq_scratch] at hp
          rw [loopIterPostN2CallScratchNoX1_skip hborrow] at hp
          xperm_hyp hp)
        (divK_loop_body_n2_call_skip_jgt0_norm_v5_noNop_exact_x1
          (1 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
          jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- First n=2 call iteration from the callable-ready v5 loop source, preserving
    concrete `x1` and carrying the j=1/j=0 source atoms as a frame. -/
theorem divK_loop_n2_call_j2_from_source_exact_loopIterScratch_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2CallScratchNoX1 sp base (2 : Word)
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) **
        ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) := by
  have J2 := divK_loop_body_n2_call_j2_exact_loopIterScratch_v5_noNop sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_nz
  have J2f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig1) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      have hp' := loopN2PreWithScratchV4NoX1_to_call_j2_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem h hp
      xperm_hyp hp')
    (fun h hp => hp)
    J2f

/-- First n=2 max iteration from the callable-ready v5 loop source, preserving
    concrete `x1`, scratch, and the j=1/j=0 source atoms as a frame. -/
theorem divK_loop_n2_max_j2_from_source_exact_loopIterScratch_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2Max sp (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) := by
  have J2 := divK_loop_body_n2_max_j2_exact_loopIterScratch_v5_noNop sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu hcarry2_nz
  have J2f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig1) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      have hp' := loopN2PreWithScratchV4NoX1_to_max_j2_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem h hp
      xperm_hyp hp')
    (fun h hp => hp)
    J2f

open EvmAsm.Rv64

/-- Full n=2 call×call prefix from the callable-ready v5 loop source. -/
theorem divK_loop_n2_call_call_from_source_exact_loopIterScratch_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : BitVec.ult u2 v1)
    (hcarry2_nz_2 :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0)
    (hbltu_1 :
      BitVec.ult
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2_nz_1 :
      let r2 := iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      let qHat := divKTrialCallV5QHat r2.2.2.1 r2.2.1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (r2.2.2.2.2.1 - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    let r2 := iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let qHat1 := divKTrialCallV5QHat r2.2.2.1 r2.2.1 v1
    let dLo1 := divKTrialCallV5DLo v1
    let divUn01 := divKTrialCallV5Un0 r2.2.1
    let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (234 + 234) (base + loopBodyOff) (base + loopBodyOff)
      (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2CallScratchNoX1 sp base (1 : Word)
        qHat1 dLo1 divUn01 scratch1
        v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
          (qAddr2 ↦ₘ r2.1)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) := by
  intro r2 qHat1 dLo1 divUn01 scratch2 scratch1 uBase2 qAddr2 uBase0 qAddr0
  have J2 := divK_loop_n2_call_j2_from_source_exact_loopIterScratch_v5_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_2 hcarry2_nz_2
  subst r2
  subst qHat1
  subst dLo1
  subst divUn01
  subst scratch2
  subst scratch1
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  have J1 := divK_loop_body_n2_call_j1_exact_loopIterScratch_v5_noNop sp base
    (2 : Word)
    ((2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig1
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q1Old raVal
    (base + div128CallRetOff) v1 (divKTrialCallV5DLo v1)
    (divKTrialCallV5Un0 u1) (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
    halign hbltu_1 hcarry2_nz_1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2CallScratchNoX1_j2_to_call_j1_pre
      sp base (divKTrialCallV5QHat u2 u1 v1) (divKTrialCallV5DLo v1)
      (divKTrialCallV5Un0 u1) (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal)
    J2 J1f

end EvmAsm.Evm64
