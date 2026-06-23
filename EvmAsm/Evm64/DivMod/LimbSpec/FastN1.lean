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

abbrev divK_fastSetup_b0prime_code (base : Word) : CodeReq :=
  CodeReq.ofProg base [.LD .x5 .x12 32, .SLL .x5 .x5 .x6, .SD .x12 .x5 3984]

/-- `divK_fastSetup` divisor-normalization block (the 3 instructions after the
    antiShift setup, which is `divK_phaseC2_body`): load `b0` from `sp + 32`,
    compute `b0' = b0 <<< s` (`s` = CLZ shift in `x6`), and store `b0'` at
    `sp + 3984`. Mirror of `divK_normB_last`. -/
theorem divK_fastSetup_b0prime_spec_within (sp : Word) (base : Word)
    (s b0 v5 m3984 : Word) :
    let result := b0 <<< (s.toNat % 64)
    let cr := divK_fastSetup_b0prime_code base
    cpsTripleWithin 3 base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) **
       ((sp + signExtend12 32) ↦ₘ b0) ** ((sp + signExtend12 3984) ↦ₘ m3984))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ s) **
       ((sp + signExtend12 32) ↦ₘ b0) ** ((sp + signExtend12 3984) ↦ₘ result)) := by
  intro result cr
  have I0 := ld_spec_gen_within .x5 .x12 sp v5 b0 32 base (by nofun)
  have I1 := sll_spec_gen_rd_eq_rs1_within .x5 .x6 b0 s (base + 4) (by nofun)
  have I2 := sd_spec_gen_within .x12 .x5 sp result m3984 3984 (base + 8)
  runBlock I0 I1 I2

-- ============================================================================
-- Digit step: load window/divisor, (call div128), recover threaded remainder
-- ============================================================================

abbrev divK_fastDigit_loads_code (uHiOff uLoOff : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base [.LD .x7 .x12 uHiOff, .LD .x5 .x12 uLoOff, .LD .x10 .x12 3984]

/-- Digit-step argument loads (3 instructions): `x7 = uHi = u[j+1]` (the running
    remainder), `x5 = uLo = u[j]`, `x10 = d = b0'`. Establishes the
    `div128_v5_spec` input registers. -/
theorem divK_fastDigit_loads_spec_within (uHiOff uLoOff : BitVec 12)
    (sp uHi uLo d v5 v7 v10 : Word) (base : Word) :
    let cr := divK_fastDigit_loads_code uHiOff uLoOff base
    cpsTripleWithin 3 base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
       ((sp + signExtend12 3984) ↦ₘ d))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ uHi) ** (.x5 ↦ᵣ uLo) ** (.x10 ↦ᵣ d) **
       ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
       ((sp + signExtend12 3984) ↦ₘ d)) := by
  intro cr
  have I0 := ld_spec_gen_within .x7 .x12 sp v7 uHi uHiOff base (by nofun)
  have I1 := ld_spec_gen_within .x5 .x12 sp v5 uLo uLoOff (base + 4) (by nofun)
  have I2 := ld_spec_gen_within .x10 .x12 sp v10 d 3984 (base + 8) (by nofun)
  runBlock I0 I1 I2

abbrev divK_fastDigit_post_code (uLoOff qOff : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    [.SD .x12 .x11 qOff, .LD .x5 .x12 uLoOff, .LD .x10 .x12 3984,
     .MUL .x7 .x11 .x10, .SUB .x5 .x5 .x7, .SD .x12 .x5 uLoOff]

/-- Digit-step post-call block (6 instructions): store the exact quotient digit
    `q[j] = x11` to `qOff`; recover the threaded remainder
    `u[j] := u[j] -₆₄ q·b0'` (`b0'` reloaded from `sp + 3984`) and store it to
    `uLoOff`. Valid since the true 128-bit remainder is `< b0' < 2^64`, so its
    low 64 bits are exact. -/
theorem divK_fastDigit_post_spec_within (uLoOff qOff : BitVec 12)
    (sp q uLo d v5 v7 v10 qm : Word) (base : Word) :
    let cr := divK_fastDigit_post_code uLoOff qOff base
    cpsTripleWithin 6 base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x7 ↦ᵣ v7) **
       ((sp + signExtend12 qOff) ↦ₘ qm) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
       ((sp + signExtend12 3984) ↦ₘ d))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q) ** (.x5 ↦ᵣ (uLo - q * d)) ** (.x10 ↦ᵣ d) **
       (.x7 ↦ᵣ (q * d)) **
       ((sp + signExtend12 qOff) ↦ₘ q) ** ((sp + signExtend12 uLoOff) ↦ₘ (uLo - q * d)) **
       ((sp + signExtend12 3984) ↦ₘ d)) := by
  intro cr
  have I0 := sd_spec_gen_within .x12 .x11 sp q qm qOff base
  have I1 := ld_spec_gen_within .x5 .x12 sp v5 uLo uLoOff (base + 4) (by nofun)
  have I2 := ld_spec_gen_within .x10 .x12 sp v10 d 3984 (base + 8) (by nofun)
  have I3 := mul_spec_gen_within .x7 .x11 .x10 v7 q d (base + 12) (by nofun)
  have I4 := sub_spec_gen_rd_eq_rs1_within .x5 .x7 uLo (q * d) (base + 16) (by nofun)
  have I5 := sd_spec_gen_within .x12 .x5 sp (uLo - q * d) uLo uLoOff (base + 20)
  runBlock I0 I1 I2 I3 I4 I5

end EvmAsm.Evm64
