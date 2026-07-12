/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallIterMod

  MOD mirror of `FullPathN2V5NoNopCallIter`: the iter-ready n=2 call-path loop
  bodies (j=2 and j=1) over `modCode_noNop_v5`.  Byte-for-byte the DIV proof —
  case on the c3 borrow guard, dispatch to the MOD call-path exact-x1 norm bodies
  (#7689), and weaken the post to `loopIterPostN2CallScratchNoX1` via the
  code-agnostic V5 post-eq lemmas (`loopBodyN2Call*JgtPostV5NoX1_eq_scratch`,
  reused from the DIV `FullPathN2V5NoNopCallIter`) + the producer bridges.
  Brick 7 of the n=2 MOD loop body (call iter layer).
  Bead `evm-asm-wbc4i.10.3.2.4.5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopSourceShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallExactX1Mod

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Unified j=2 N2 call iteration over `modCode_noNop_v5`, preserving concrete `x1`. -/
theorem divK_loop_body_n2_call_j2_exact_loopIterScratch_v5_noNop_modCode (sp base : Word)
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
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
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
      (divK_loop_body_n2_call_addback_jgt0_beq_norm_v5_noNop_exact_x1_modCode
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
        (divK_loop_body_n2_call_skip_jgt0_norm_v5_noNop_exact_x1_modCode
          (2 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
          jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

/-- Unified j=1 N2 call iteration over `modCode_noNop_v5`, preserving concrete `x1`. -/
theorem divK_loop_body_n2_call_j1_exact_loopIterScratch_v5_noNop_modCode (sp base : Word)
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
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
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
      (divK_loop_body_n2_call_addback_jgt0_beq_norm_v5_noNop_exact_x1_modCode
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
        (divK_loop_body_n2_call_skip_jgt0_norm_v5_noNop_exact_x1_modCode
          (1 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
          jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

end EvmAsm.Evm64
