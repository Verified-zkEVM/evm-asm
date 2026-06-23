/-
  EvmAsm.Evm64.DivMod.LimbSpec.FastN1

  Per-block CPS specs for the n=1 single-limb fast path (issue #9303):
  `divK_fastDenorm`, `divK_fastSetup`, `divK_fastDigit`, `divK_dispatchN1`.
  The reused blocks (`divK_clz`, `divK_normA`, `divK_copyAU`,
  `divK_div_epilogue`) keep their existing specs.
-/

import EvmAsm.Evm64.DivMod.FastN1Program
import EvmAsm.Evm64.DivMod.Compose.Div128V5
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

abbrev divK_fastDenorm_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_fastDenorm

/-- Single-limb remainder de-normalization (MOD): `u[0] := u[0] >> s` and zero
    the upper remainder limbs `u[1..3]`. `s` (the CLZ shift) is read from the
    scratch slot at `sp + 3992`. 7 instructions. -/
theorem divK_fastDenorm_spec_within (sp : Word) (base : Word)
    (s u0 u1m u2m u3m v5 v6 : Word) :
    let cr := divK_fastDenorm_code base
    cpsTripleWithin 7 base (base + 28) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1m) **
       ((sp + signExtend12 4040) ↦ₘ u2m) ** ((sp + signExtend12 4032) ↦ₘ u3m))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (u0 >>> (s.toNat % 64))) ** (.x6 ↦ᵣ s) **
       (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 4056) ↦ₘ (u0 >>> (s.toNat % 64))) **
       ((sp + signExtend12 4048) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4040) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4032) ↦ₘ (0 : Word))) := by
  intro cr
  have I0 := ld_spec_gen_within .x6 .x12 sp v6 s 3992 base (by nofun)
  have I1 := ld_spec_gen_within .x5 .x12 sp v5 u0 4056 (base + 4) (by nofun)
  have I2 := srl_spec_gen_rd_eq_rs1_within .x5 .x6 u0 s (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x5 sp (u0 >>> (s.toNat % 64)) u0 4056 (base + 12)
  have I4 := sd_x0_spec_gen_within .x12 sp u1m 4048 (base + 16)
  have I5 := sd_x0_spec_gen_within .x12 sp u2m 4040 (base + 20)
  have I6 := sd_x0_spec_gen_within .x12 sp u3m 4032 (base + 24)
  runBlock I0 I1 I2 I3 I4 I5 I6

end EvmAsm.Evm64
