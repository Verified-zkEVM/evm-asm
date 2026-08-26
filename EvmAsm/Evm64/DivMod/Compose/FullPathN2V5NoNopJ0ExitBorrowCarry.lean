/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopJ0ExitBorrowCarry

  Borrow-dispatched variant of `divK_loop_body_n2_call_j0_exact_loopIterScratch_v5_noNop`
  (FullPathN2V5NoNopJ0Exit) that requires carry2nz ONLY conditionally on the
  runtime borrow, instead of the over-strong unconditional `hcarry2_nz` (which is
  false when the call digit's trial is exact, c3 = 0).

  In the borrow branch we delegate to the original body (supplying carry2nz from
  the conditional hypothesis); in the no-borrow branch we inline the SKIP path
  (mirror of the original body's no-borrow branch), which needs no carry2nz.  The
  conditional hypothesis is dischargeable from shape via
  `callAddbackCarry2NzV5_of_borrow_n2` (#7431).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopJ0Exit
public import EvmAsm.Evm64.DivMod.Spec.N2V5CallCarryBorrowN2

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- j=0 N2 call iteration over v5/no-NOP code, with carry2nz required only on the
    runtime-borrow branch. -/
theorem divK_loop_body_n2_call_j0_exact_loopIterScratch_v5_noNop_borrowCarry
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_borrow :
      BitVec.ult uTop (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3) →
      callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
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
  · exact divK_loop_body_n2_call_j0_exact_loopIterScratch_v5_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu (hcarry2_borrow hborrow)
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

end EvmAsm.Evm64
