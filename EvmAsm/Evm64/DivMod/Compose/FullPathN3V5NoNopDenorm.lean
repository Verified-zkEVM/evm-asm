/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopDenorm

  The n=3 v5 denormalization-epilogue cpsTriple (denormOff → nopOff), wrapping the
  shared v5 denorm code spec `evm_div_preamble_denorm_epilogue_spec_v5_noNop`
  (DenormEpilogueV5) for the n=3 callable-trial-v5 quotient/remainder families.
  v5 mirror of `evm_div_n3_denorm_epilogue_bundled_spec_v4_noNop_v4Final`
  (`FullPathN3V4.lean` :335) and its exact-`x1`/scratch framed form (:367).
  Bead `evm-asm-wbc4i.9.3.3.6`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopDenormDefs
public import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- N3 denormalization and DIV epilogue over v5/no-NOP for the v5 callable-trial
    final computation family. -/
theorem evm_div_n3_denorm_epilogue_bundled_spec_v5_noNop
    (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode_noNop_v5 base)
      (fullDivN3DenormPreV5 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN3DenormPostV5 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := fullDivN3Shift b2
  let v := fullDivN3NormV b0 b1 b2 b3
  let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let c3 := fullDivN3C3V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  have h := evm_div_preamble_denorm_epilogue_spec_v5_noNop sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3 r0.1 r1.1 (0 : Word) (0 : Word)
    v.1 v.2.1 v.2.2.1 v.2.2.2 hshift_nz
  exact cpsTripleWithin_weaken
    (fun h hp => by
      subst shift; subst v; subst r1; subst r0; subst c3
      delta fullDivN3DenormPreV5 at hp
      simp only [se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by
      subst shift; subst r1; subst r0
      delta fullDivN3DenormPostV5
      xperm_hyp hq)
    h

/-- N3 denormalization and DIV epilogue over v5/no-NOP for the v5 callable-trial
    final computation family, preserving exact caller `x1` and the final v5 div128
    scratch cell. -/
theorem evm_div_n3_denorm_epilogue_bundled_spec_v5_noNop_exact_x1_scratch_frame
    (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff)
      (divCode_noNop_v5 base)
      (fullDivN3DenormPreV5 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
       fullDivN3FrameNoX1V5 bltu_1 bltu_0 sp base
         a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ
         fullDivN3ScratchMemV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
       (.x1 ↦ᵣ raVal))
      (fullDivN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hDenorm := evm_div_n3_denorm_epilogue_bundled_spec_v5_noNop
    bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz
  have hFramed := cpsTripleWithin_frameR
    (fullDivN3FrameNoX1V5 bltu_1 bltu_0 sp base
     a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal))
    (by
      delta fullDivN3FrameNoX1V5 fullDivN3ScratchNoX1V5
      pcFree) hDenorm
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      delta fullDivN3UnifiedPostNoX1V5
      xperm_hyp hq)
    hFramed

end EvmAsm.Evm64
