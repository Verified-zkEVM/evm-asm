/-
  EvmAsm.Evm64.DivMod.Compose.CopyAUV5Mod

  v5 copy-AU brick (9 steps, copyAUOff → loopSetupOff) over `modCode_noNop_v5`.
  On the shift = 0 branch normalization is a no-op, so the dividend `a[0..3]` is
  copied verbatim into the `u`-cells (`u[4]` zeroed).  Lifts the version-agnostic
  limb spec `divK_copyAU_spec_within` (relocated to `base + copyAUOff`) onto the
  v5 code surface via the block-6 subsumption `sharedNoNop_v5_b6_mod`.  Second
  brick of the v5 n=1 shift=0 preloop.  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.LimbSpec.CopyAU
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 copy-AU (shift = 0): copy `a[0..3]` into `u[0..3]`, zero `u[4]`, over
    `modCode_noNop_v5`, from `copyAUOff` to `loopSetupOff`. -/
theorem divK_copyAU_spec_within_v5_noNop_mod (sp base : Word)
    (a0 a1 a2 a3 u0 u1 u2 u3 u4 v5 : Word) :
    cpsTripleWithin 9 (base + copyAUOff) (base + loopSetupOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
       ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word))) := by
  have hbody := divK_copyAU_spec_within sp (base + copyAUOff)
    a0 a1 a2 a3 u0 u1 u2 u3 u4 v5
  simp only [divK_copyAU_code] at hbody
  rw [show (base + copyAUOff) + 36 = base + loopSetupOff from by
    simp only [copyAUOff, loopSetupOff]; bv_addr] at hbody
  exact cpsTripleWithin_extend_code sharedNoNop_v5_b6_mod hbody

end EvmAsm.Evm64
