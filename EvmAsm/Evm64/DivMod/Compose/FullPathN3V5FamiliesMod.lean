/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5FamiliesMod

  v5 MOD n=3 denorm + epilogue bundle (denormOff → nopOff), over `modCode_noNop_v5`.
  The MOD mirror of the DIV n=3 denorm-epilogue families (`FullPathN3V5NoNopDenormDefs`):
  it shares the DIV denorm PRE (`fullDivN3DenormPreV5`) and the loop frame
  (`fullDivN3FrameNoX1V5` / `fullDivN3ScratchMemV5`) — the loop computes both quotient
  and remainder — and swaps in the MOD epilogue (`evm_mod_preamble_denorm_epilogue_spec_v5_noNop`)
  which loads the denormalized remainder.  Defines the MOD post bundles
  `fullModN3DenormPostV5` / `fullModN3UnifiedPostNoX1V5`, mirroring the n=2 MOD
  `FullPathN2V5FamiliesMod`.  First sub-unit of Milestone D of the n=3 MOD lane.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopDenormDefs
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- v5 MOD n=3 denorm post: the denormalized remainder (`denormModPost`) plus the
    untouched shift cell and the two quotient cells (framed, MOD never reads them). -/
@[irreducible]
def fullModN3DenormPostV5 (bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN3Shift b2
  let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  denormModPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + signExtend12 4088) ↦ₘ r0.1) **
  ((sp + signExtend12 4080) ↦ₘ r1.1) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word))

/-- v5 MOD n=3 unified post (NoX1 form): MOD denorm post plus the shared loop
    frame and the `sp+3936` div128 scratch cell.  Reuses the DIV n=3 frame. -/
@[irreducible]
def fullModN3UnifiedPostNoX1V5 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word) :
    Assertion :=
  fullModN3DenormPostV5 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
  fullDivN3FrameNoX1V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratchUn0 **
  ((sp + signExtend12 3936) ↦ₘ
    fullDivN3ScratchMemV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)

theorem fullModN3DenormPostV5_unfold {bltu_1 bltu_0 : Bool}
    {sp a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    fullModN3DenormPostV5 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 =
    (let shift := fullDivN3Shift b2
     let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
     let r0 := fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
     denormModPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 **
     ((sp + signExtend12 3992) ↦ₘ shift) **
     ((sp + signExtend12 4088) ↦ₘ r0.1) **
     ((sp + signExtend12 4080) ↦ₘ r1.1) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word))) := by
  delta fullModN3DenormPostV5; rfl

theorem fullModN3UnifiedPostNoX1V5_unfold {bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word} :
    fullModN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem =
    (fullModN3DenormPostV5 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN3FrameNoX1V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) := by
  delta fullModN3UnifiedPostNoX1V5; rfl

/-- v5 MOD n=3 denorm + epilogue (denormOff → nopOff): the SHARED DIV denorm pre
    drives the MOD epilogue (loads the denormalized remainder), yielding the MOD
    denorm post.  Mirror of `evm_mod_n2_denorm_epilogue_bundled_spec_noNop_v5Final`. -/
theorem evm_mod_n3_denorm_epilogue_bundled_spec_noNop_v5Final
    (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (modCode_noNop_v5 base)
      (fullDivN3DenormPreV5 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3)
      (fullModN3DenormPostV5 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := fullDivN3Shift b2
  let v := fullDivN3NormV b0 b1 b2 b3
  let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let c3 := fullDivN3C3V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  have h := evm_mod_preamble_denorm_epilogue_spec_v5_noNop sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3 v.1 v.2.1 v.2.2.1 v.2.2.2 hshift_nz
  have hF := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ r0.1) **
     ((sp + signExtend12 4080) ↦ₘ r1.1) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)))
    (by pcFree) h
  exact cpsTripleWithin_weaken
    (fun h hp => by
      subst shift; subst v; subst r1; subst r0; subst c3
      delta fullDivN3DenormPreV5 at hp
      simp only [se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by
      subst shift; subst r1; subst r0
      delta fullModN3DenormPostV5
      xperm_hyp hq)
    hF

/-- v5 MOD n=3 denorm + epilogue, framed with the loop frame + scratch cell + x1
    (the direct shape for the n=3 MOD path composition). -/
theorem evm_mod_n3_denorm_epilogue_bundled_spec_noNop_v5Final_exact_x1_frame
    (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff)
      (modCode_noNop_v5 base)
      (fullDivN3DenormPreV5 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
       fullDivN3FrameNoX1V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
         retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ
         fullDivN3ScratchMemV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
       (.x1 ↦ᵣ raVal))
      (fullModN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hDenorm := evm_mod_n3_denorm_epilogue_bundled_spec_noNop_v5Final
    bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz
  have hFramed := cpsTripleWithin_frameR
    (fullDivN3FrameNoX1V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal))
    (by
      delta fullDivN3FrameNoX1V5 fullDivN3ScratchNoX1V5
      pcFree) hDenorm
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      delta fullModN3UnifiedPostNoX1V5
      xperm_hyp hq)
    hFramed

end EvmAsm.Evm64
