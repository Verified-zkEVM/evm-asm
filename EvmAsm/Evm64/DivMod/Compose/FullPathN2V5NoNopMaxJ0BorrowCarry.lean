/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopMaxJ0BorrowCarry

  Borrow-dispatched variant of the j=0 N2 MAX iteration body
  (FullPathN2V5NoNopJ0Exit), requiring `isAddbackCarry2NzN2Max` only conditionally
  on the runtime borrow.  Like the call digit, the max body case-splits on
  `BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095) …)` and uses the carry only in
  the borrow branch; for the saturated max trial the path is in fact always
  no-borrow, so the conditional hypothesis is vacuously dischargeable.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopJ0Exit

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- j=0 N2 max iteration, carry required only on the runtime-borrow branch. -/
theorem divK_loop_body_n2_max_j0_exact_loopIterScratch_v5_noNop_borrowCarry (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_borrow :
      BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) →
      isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
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
  · exact divK_loop_body_n2_max_j0_exact_loopIterScratch_v5_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem hbltu (hcarry2_borrow hborrow)
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

end EvmAsm.Evm64
