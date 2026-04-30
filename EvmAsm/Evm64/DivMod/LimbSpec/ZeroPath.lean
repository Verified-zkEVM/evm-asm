/-
  EvmAsm.Evm64.DivMod.LimbSpec.ZeroPath

  CPS spec for the Knuth Algorithm D zero path:
    * `divK_zeroPath_code` / `divK_zeroPath_spec_within` — 5-instruction
      ADDI+SD*4 block taken when `b = 0`. Advances the stack pointer by
      32 and writes four zero words at the output location (DIV and MOD
      both return 0 on division by zero).

  Sixth chunk of the `LimbSpec.lean` split tracked by issue #312. The
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

abbrev divK_zeroPath_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_zeroPath

/-- Zero path: advance sp by 32, store four zeros at the output location.
    Used when b = 0 (both DIV and MOD return 0). -/
theorem divK_zeroPath_spec_within (sp : Word) (base : Word)
    (m32 m40 m48 m56 : Word) :
    let cr := divK_zeroPath_code base
    cpsTripleWithin 5 base (base + 20) cr
      ((.x12 ↦ᵣ sp) **
       ((sp + 32) ↦ₘ m32) ** ((sp + 40) ↦ₘ m40) **
       ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))
      ((.x12 ↦ᵣ (sp + 32)) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  have I0 := addi_spec_gen_same_within .x12 sp 32 base (by nofun)
  have I1 := sd_x0_spec_gen_within .x12 (sp + 32) m32 0 (base + 4)
  have I2 := sd_x0_spec_gen_within .x12 (sp + 32) m40 8 (base + 8)
  have I3 := sd_x0_spec_gen_within .x12 (sp + 32) m48 16 (base + 12)
  have I4 := sd_x0_spec_gen_within .x12 (sp + 32) m56 24 (base + 16)
  runBlock I0 I1 I2 I3 I4

end EvmAsm.Evm64
