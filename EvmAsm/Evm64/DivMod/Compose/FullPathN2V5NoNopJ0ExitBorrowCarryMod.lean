/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopJ0ExitBorrowCarryMod

  MOD mirror of `FullPathN2V5NoNopJ0ExitBorrowCarry`: the borrow-dispatched j=0 N2
  call iteration body over `modCode_noNop_v5`, requiring carry2nz only conditionally
  on the runtime borrow.  Byte-for-byte the DIV proof — delegate on borrow to the
  MOD base call j0 iter (#7701), inline the SKIP path on no-borrow via the MOD
  call-skip j0 exact-x1 norm body (#7689).  Brick 16 of the n=2 MOD loop body
  (call j0 iter-bc — completes the j0 iter-bc layer).  Bead `evm-asm-wbc4i.10.3.2.4.5`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopJ0ExitMod
public import EvmAsm.Evm64.DivMod.Spec.N2V5CallCarryBorrowN2

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- j=0 N2 call iteration over `modCode_noNop_v5`, with carry2nz required only on
    the runtime-borrow branch. -/
theorem divK_loop_body_n2_call_j0_exact_loopIterScratch_v5_noNop_borrowCarry_modCode
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
  · exact divK_loop_body_n2_call_j0_exact_loopIterScratch_v5_noNop_modCode
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
        (divK_loop_body_n2_call_skip_j0_norm_v5_noNop_exact_x1_modCode
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

end EvmAsm.Evm64
