/-
  EvmAsm.Evm64.DivMod.LimbSpec.CopyAU

  CPS spec for the Knuth Algorithm D unshifted copy phase (C4):
    * `divK_copyAU_code` / `divK_copyAU_spec_within` — 9-instruction straight-line
      copy of `a[0..3]` into `u[0..3]`, with `u[4]` zeroed.

  Taken on the shift = 0 branch, where normalization is a no-op and the
  dividend can be copied verbatim.

  Fifth chunk of the `LimbSpec.lean` split tracked by issue #312. The
  consumer surface is unchanged: `LimbSpec.lean` re-exports this file so
  every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the spec.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

abbrev divK_copyAU_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_copyAU

/-- Copy a[0..3] to u[0..3] and set u[4] = 0 (no shift needed). -/
theorem divK_copyAU_spec_within (sp : Word) (base : Word)
    (a0 a1 a2 a3 u0 u1 u2 u3 u4 : Word) (v5 : Word) :
    let cr := divK_copyAU_code base
    cpsTripleWithin 9 base (base + 36) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
       ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word))) := by
  have I0 := ld_spec_gen_within .x5 .x12 sp v5 a0 0 base (by nofun)
  have I1 := sd_spec_gen_within .x12 .x5 sp a0 u0 4056 (base + 4)
  have I2 := ld_spec_gen_within .x5 .x12 sp a0 a1 8 (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x5 sp a1 u1 4048 (base + 12)
  have I4 := ld_spec_gen_within .x5 .x12 sp a1 a2 16 (base + 16) (by nofun)
  have I5 := sd_spec_gen_within .x12 .x5 sp a2 u2 4040 (base + 20)
  have I6 := ld_spec_gen_within .x5 .x12 sp a2 a3 24 (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x5 sp a3 u3 4032 (base + 28)
  have I8 := sd_x0_spec_gen_within .x12 sp u4 4024 (base + 32)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8

end EvmAsm.Evm64
