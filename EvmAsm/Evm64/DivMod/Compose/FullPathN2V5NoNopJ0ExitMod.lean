/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopJ0ExitMod

  MOD mirror of `FullPathN2V5NoNopJ0Exit`: the n=2 j=0 EXIT iter bodies (call + max,
  loopBodyOff → denormOff) over `modCode_noNop_v5`.  Byte-for-byte the DIV proofs —
  the max+addback j=0 norm body is an extend-swap (`_sub_modCode_noNop_v5`); the
  base call/max j=0 iters case on the c3 borrow guard and dispatch to the MOD j=0
  norm bodies (#7687/#7689).  The two J0 call post-eq lemmas
  (`loopBodyN2Call{Skip,AddbackBeq}J0PostV5NoX1_eq_scratch`) are code-agnostic and
  reused from the DIV `FullPathN2V5NoNopJ0Exit`.  Brick 14 of the n=2 MOD loop body
  (j=0 exit iters — prerequisite for the j0 iter-bc + 3-combos).
  Bead `evm-asm-wbc4i.10.3.2.4.5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopSourceShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopMaxMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallExactX1Mod

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- v5 n=2 max+addback j=0 norm body over `modCode_noNop_v5`. -/
theorem divK_loop_body_n2_max_addback_j0_beq_norm_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
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
    (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5) raw
  rw [loopBodyN2MaxSkipJ0Pre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN2MaxSkipJ0NormPreV4
  exact raw'

/-- Unified j=0 N2 call iteration over `modCode_noNop_v5` (loop exit). -/
theorem divK_loop_body_n2_call_j0_exact_loopIterScratch_v5_noNop_modCode (sp base : Word)
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
    cpsTripleWithin 234 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
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
      (divK_loop_body_n2_call_addback_j0_beq_norm_v5_noNop_exact_x1_modCode
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
        (divK_loop_body_n2_call_skip_j0_norm_v5_noNop_exact_x1_modCode
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

/-- Unified j=0 N2 max iteration over `modCode_noNop_v5` (loop exit). -/
theorem divK_loop_body_n2_max_j0_exact_loopIterScratch_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
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
    have J := divK_loop_body_n2_max_addback_j0_beq_norm_v5_noNop_modCode
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
    have J := divK_loop_body_n2_max_skip_j0_norm_v5_noNop_modCode
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

end EvmAsm.Evm64
