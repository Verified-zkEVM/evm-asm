/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5FamiliesMod

  v5 MOD n=2 denorm + epilogue bundle (denormOff → nopOff), over `modCode_noNop_v5`.
  The MOD mirror of the DIV `evm_div_n2_denorm_epilogue_bundled_spec_noNop_v5Final`
  family (`FullPathN2V5Families.lean`): it shares the DIV denorm PRE
  (`fullDivN2DenormPreV5`) and the loop frame (`fullDivN2FrameNoX1V5` /
  `fullDivN2ScratchMemV5`) — the loop computes both quotient and remainder — and
  swaps in the MOD epilogue (`evm_mod_preamble_denorm_epilogue_spec_v5_noNop`,
  #7677) which loads the denormalized remainder.  Defines the MOD post bundles
  `fullModN2DenormPostV5` / `fullModN2UnifiedPostNoX1V5` (mirroring the v4 MOD
  `fullModN2DenormPost` / `fullModN2UnifiedPost` in `ModFullPathN2LoopUnified.lean`,
  but with the v5 digit families and the extra `sp+3936` scratch cell).
  First sub-unit of the n=2 MOD lane.  Bead `evm-asm-wbc4i.10.3.2.4.1`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5FamiliesShapeShared
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- v5 MOD n=2 denorm post: the denormalized remainder (`denormModPost`) plus the
    untouched shift cell and the four quotient cells (framed, MOD never reads
    them).  Mirror of the v4 `fullModN2DenormPost` with v5 digit families. -/
@[irreducible]
def fullModN2DenormPostV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN2Shift b1
  let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  denormModPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + signExtend12 4088) ↦ₘ r0.1) **
  ((sp + signExtend12 4080) ↦ₘ r1.1) **
  ((sp + signExtend12 4072) ↦ₘ r2.1) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word))

/-- v5 MOD n=2 unified post (NoX1 form): MOD denorm post plus the shared loop
    frame and the `sp+3936` div128 scratch cell.  Mirror of the DIV
    `fullDivN2UnifiedPostNoX1V5`, reusing the DIV frame. -/
@[irreducible]
def fullModN2UnifiedPostNoX1V5 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word) :
    Assertion :=
  fullModN2DenormPostV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
  fullDivN2FrameNoX1V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratchUn0 **
  ((sp + signExtend12 3936) ↦ₘ
    fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)

theorem fullModN2DenormPostV5_unfold {bltu_2 bltu_1 bltu_0 : Bool}
    {sp a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    fullModN2DenormPostV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 =
    (let shift := fullDivN2Shift b1
     let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
     let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
     let r0 := fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
     denormModPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 **
     ((sp + signExtend12 3992) ↦ₘ shift) **
     ((sp + signExtend12 4088) ↦ₘ r0.1) **
     ((sp + signExtend12 4080) ↦ₘ r1.1) **
     ((sp + signExtend12 4072) ↦ₘ r2.1) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word))) := by
  delta fullModN2DenormPostV5; rfl

theorem fullModN2UnifiedPostNoX1V5_unfold {bltu_2 bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word} :
    fullModN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem =
    (fullModN2DenormPostV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) := by
  delta fullModN2UnifiedPostNoX1V5; rfl

/-- v5 MOD n=2 denorm + epilogue (denormOff → nopOff): the SHARED DIV denorm pre
    drives the MOD epilogue (loads the denormalized remainder), yielding the MOD
    denorm post.  Mirror of `evm_div_n2_denorm_epilogue_bundled_spec_noNop_v5Final`
    and the v4 `evm_mod_n2_denorm_epilogue_bundled_spec`. -/
theorem evm_mod_n2_denorm_epilogue_bundled_spec_noNop_v5Final
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : fullDivN2Shift b1 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (modCode_noNop_v5 base)
      (fullDivN2DenormPreV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3)
      (fullModN2DenormPostV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := fullDivN2Shift b1
  let v := fullDivN2NormV b0 b1 b2 b3
  let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let c3 := fullDivN2C3V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  have h := evm_mod_preamble_denorm_epilogue_spec_v5_noNop sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3 v.1 v.2.1 v.2.2.1 v.2.2.2 hshift_nz
  have hF := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ r0.1) **
     ((sp + signExtend12 4080) ↦ₘ r1.1) **
     ((sp + signExtend12 4072) ↦ₘ r2.1) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)))
    (by pcFree) h
  exact cpsTripleWithin_weaken
    (fun h hp => by
      subst shift; subst v; subst r2; subst r1; subst r0; subst c3
      delta fullDivN2DenormPreV5 at hp
      simp only [se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by
      subst shift; subst r2; subst r1; subst r0
      delta fullModN2DenormPostV5
      xperm_hyp hq)
    hF

/-- v5 MOD n=2 denorm + epilogue, framed with the loop frame + scratch cell + x1
    (the direct shape for the n=2 MOD path composition).  Mirror of
    `evm_div_n2_denorm_epilogue_bundled_spec_noNop_v5Final_exact_x1_frame`. -/
theorem evm_mod_n2_denorm_epilogue_bundled_spec_noNop_v5Final_exact_x1_frame
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hshift_nz : fullDivN2Shift b1 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff)
      (modCode_noNop_v5 base)
      (fullDivN2DenormPreV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
       fullDivN2FrameNoX1V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
         retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ
         fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
       (.x1 ↦ᵣ raVal))
      (fullModN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hDenorm := evm_mod_n2_denorm_epilogue_bundled_spec_noNop_v5Final
    bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz
  have hFramed := cpsTripleWithin_frameR
    (fullDivN2FrameNoX1V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal))
    (by
      delta fullDivN2FrameNoX1V5 fullDivN2ScratchNoX1V5
      pcFree) hDenorm
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      delta fullModN2UnifiedPostNoX1V5
      xperm_hyp hq)
    hFramed

end EvmAsm.Evm64
