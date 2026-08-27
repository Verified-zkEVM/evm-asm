/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopDenormBridge

  The four per-case heap bridges `loopN3UnifiedPostV5NoX1 →
  fullDivN3DenormPreV5` (FF/FT/TF/TT), connecting the n=3 v5 loop's unified post
  to the denorm-epilogue precondition.  v5 mirror of the v4 bridges
  (`FullPathN3V4.lean` :401–650).  Unlike v4, `iterN3V5`/`fullDivN3R{0,1}V5` are
  `@[irreducible]`, so the goal's `fullDivN3R1V5`/`R0V5`/`C3V5` are rewritten to the
  named `iterN3Max`/`iterWithDoubleAddback` forms via the `_eq` lemmas
  (`fullDivN3R1V5_false`/`_true`, `fullDivN3R0V5_eq`, `iterN3V5_false_eq_max`,
  `iterN3V5_true_eq`) rather than unfolded with `delta`.  Bead `evm-asm-wbc4i.9.3.3.6`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopDenormDefs

public section

open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- FF (max × max) bridge: `loopN3UnifiedPostV5NoX1 false false → fullDivN3DenormPreV5`. -/
theorem loopN3UnifiedPostV5NoX1_to_fullDivN3DenormPreV5_frame_FF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN3UnifiedPostV5NoX1 false false sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h) :
    (fullDivN3DenormPreV5 false false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN3FrameNoX1V5 false false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV5 false false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  -- reduce hp: unfold the unified post + the max iter post, then the j=0 exit post
  delta loopN3UnifiedPostV5NoX1 loopIterPostN3Max at hp
  simp (config := { decide := true }) only [] at hp
  rw [loopExitPostN3_j0_eq] at hp
  -- rewrite the goal's v5 quotient/remainder accessors to the named iterN3Max form
  delta fullDivN3DenormPreV5 fullDivN3FrameNoX1V5 fullDivN3ScratchNoX1V5
    fullDivN3ScratchMemV5 fullDivN3Shift
  rw [fullDivN3R0V5_eq]
  simp only [fullDivN3R1V5_false, fullDivN3C3V5, iterN3V5_false_eq_max]
  simp (config := { decide := true }) only
    [ite_false, n3_ub1_off4064, n3_qa1, se12_32, se12_40, se12_48, se12_56] at hp ⊢
  xperm_hyp hp

/-- FT (max × call) bridge: `loopN3UnifiedPostV5NoX1 false true → fullDivN3DenormPreV5`. -/
theorem loopN3UnifiedPostV5NoX1_to_fullDivN3DenormPreV5_frame_FT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN3UnifiedPostV5NoX1 false true sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h) :
    (fullDivN3DenormPreV5 false true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN3FrameNoX1V5 false true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV5 false true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN3UnifiedPostV5NoX1 loopIterPostN3CallScratchNoX1 at hp
  simp (config := { decide := true }) only [] at hp
  rw [loopExitPostN3_j0_eq] at hp
  delta fullDivN3DenormPreV5 fullDivN3FrameNoX1V5 fullDivN3ScratchNoX1V5
    fullDivN3ScratchMemV5 fullDivN3Shift
  rw [fullDivN3R0V5_eq]
  simp only [fullDivN3R1V5_false, fullDivN3C3V5, iterN3V5_true_eq]
  simp (config := { decide := true }) only
    [ite_true, ite_false, n3_ub1_off4064, n3_qa1, se12_32, se12_40, se12_48, se12_56] at hp ⊢
  xperm_hyp hp

/-- TF (call × max) bridge: `loopN3UnifiedPostV5NoX1 true false → fullDivN3DenormPreV5`. -/
theorem loopN3UnifiedPostV5NoX1_to_fullDivN3DenormPreV5_frame_TF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN3UnifiedPostV5NoX1 true false sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h) :
    (fullDivN3DenormPreV5 true false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN3FrameNoX1V5 true false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV5 true false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN3UnifiedPostV5NoX1 loopIterPostN3Max at hp
  simp (config := { decide := true }) only [] at hp
  rw [loopExitPostN3_j0_eq] at hp
  delta fullDivN3DenormPreV5 fullDivN3FrameNoX1V5 fullDivN3ScratchNoX1V5
    fullDivN3ScratchMemV5 fullDivN3Shift
  rw [fullDivN3R0V5_eq]
  simp only [fullDivN3R1V5_true, fullDivN3C3V5, iterN3V5_false_eq_max]
  simp (config := { decide := true }) only
    [ite_true, ite_false, n3_ub1_off4064, n3_qa1, se12_32, se12_40, se12_48, se12_56] at hp ⊢
  xperm_hyp hp

/-- TT (call × call) bridge: `loopN3UnifiedPostV5NoX1 true true → fullDivN3DenormPreV5`. -/
theorem loopN3UnifiedPostV5NoX1_to_fullDivN3DenormPreV5_frame_TT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN3UnifiedPostV5NoX1 true true sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h) :
    (fullDivN3DenormPreV5 true true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN3FrameNoX1V5 true true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV5 true true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN3UnifiedPostV5NoX1 loopIterPostN3CallScratchNoX1 at hp
  simp (config := { decide := true }) only [] at hp
  rw [loopExitPostN3_j0_eq] at hp
  delta fullDivN3DenormPreV5 fullDivN3FrameNoX1V5 fullDivN3ScratchNoX1V5
    fullDivN3ScratchMemV5 fullDivN3Shift
  rw [fullDivN3R0V5_eq]
  simp only [fullDivN3R1V5_true, fullDivN3C3V5, iterN3V5_true_eq]
  simp (config := { decide := true }) only
    [ite_true, n3_ub1_off4064, n3_qa1, se12_32, se12_40, se12_48, se12_56] at hp ⊢
  xperm_hyp hp

end EvmAsm.Evm64
