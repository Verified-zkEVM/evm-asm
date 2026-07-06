/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopCallExactBorrowCarryMod

  Borrow-dispatched variants of the n=3 v5 call exact-jN loop bodies: each takes
  the second-addback carry obligation only CONDITIONALLY on that iteration's
  runtime mulsub borrow (`borrow → carry`), instead of unconditionally.  Thin
  variants of `divK_loop_body_n3_call_j{0,1}_exact_loopIterScratch_v5_noNop_modCode`
  (FullPathN3V5NoNopCallExact) — the by_cases on the borrow is identical, and in
  the addback (borrow) branch the unconditional carry is recovered as
  `hcarry2_borrow hborrow`.  These are the per-digit bodies the n=3 borrowCarry
  combos consume (the from-shape carry being borrow-conditional, #7527).
  Bead `evm-asm-wbc4i.9.3.3.3.4`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopCallExactX1Mod

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Call exact-jN j=0, carry required only on the runtime borrow branch. -/
theorem divK_loop_body_n3_call_j0_exact_loopIterScratch_v5_noNop_modCode_borrowCarry (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_borrow :
      BitVec.ult uTop (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) →
      (let qHat := divKTrialCallV5QHat u3 u2 v2
       let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
       let c3 := ms.2.2.2.2
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
       let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
       carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0)) :
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
  · have hcarry2_nz := hcarry2_borrow hborrow
    have hborrow_nz : (if BitVec.ult uTop
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

/-- Call exact-jN j=1, carry required only on the runtime borrow branch. -/
theorem divK_loop_body_n3_call_j1_exact_loopIterScratch_v5_noNop_modCode_borrowCarry (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_borrow :
      BitVec.ult uTop (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) →
      (let qHat := divKTrialCallV5QHat u3 u2 v2
       let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
       let c3 := ms.2.2.2.2
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
       let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
       carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0)) :
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
  · have hcarry2_nz := hcarry2_borrow hborrow
    have hborrow_nz : (if BitVec.ult uTop
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
