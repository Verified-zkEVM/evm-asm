/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopMaxJ0BorrowCarryMod

  MOD mirror of `FullPathN2V5NoNopMaxJ0BorrowCarry`: the borrow-dispatched j=0 N2
  MAX iteration body over `modCode_noNop_v5`, requiring `isAddbackCarry2NzN2Max`
  only conditionally on the runtime borrow.  Byte-for-byte the DIV proof —
  delegate on borrow to the MOD base max j0 iter (#7701), inline the SKIP path on
  no-borrow via the MOD max-skip j0 norm body (#7687).  Brick 15 of the n=2 MOD
  loop body (max j0 iter-bc).  Bead `evm-asm-wbc4i.10.3.2.4.5`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopJ0ExitMod

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- j=0 N2 max iteration over `modCode_noNop_v5`, carry required only on the
    runtime-borrow branch. -/
theorem divK_loop_body_n2_max_j0_exact_loopIterScratch_v5_noNop_borrowCarry_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_borrow :
      BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) →
      isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
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
  · exact divK_loop_body_n2_max_j0_exact_loopIterScratch_v5_noNop_modCode
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem hbltu (hcarry2_borrow hborrow)
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
