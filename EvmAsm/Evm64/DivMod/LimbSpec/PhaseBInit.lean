/-
  EvmAsm.Evm64.DivMod.LimbSpec.PhaseBInit

  CPS specs for the two halves of Knuth Algorithm D "phase B init":
    * `divK_phaseB_init1_code` / `divK_phaseB_init1_spec_within` — 7 SD .x0's
      zeroing `q[0..3]` and `u[5..7]` in scratch.
    * `divK_phaseB_init2_code` / `divK_phaseB_init2_spec_within` — 2 LDs that
      preload `b[1]` and `b[2]` into `x6` and `x7`.

  Split at the 7/2 boundary because runBlock with 9 mixed SD/LD atoms
  hits the normalization slowdown documented in the MEMORY notes.

  Eighth chunk of the `LimbSpec.lean` split tracked by issue #312. The
  consumer surface is unchanged: `LimbSpec.lean` re-exports this file so
  every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees both
  specs.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

abbrev divK_phaseB_init1_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseB.take 7)

/-- Phase B init part 1: zero scratch q[0..3] and u[5..7]. 7 instructions. -/
theorem divK_phaseB_init1_spec_within (sp : Word) (base : Word)
    (q0 q1 q2 q3 u5 u6 u7 : Word) :
    let cr := divK_phaseB_init1_code base
    cpsTripleWithin 7 base (base + 28) cr
      (
       (.x12 ↦ᵣ sp) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7))
      (
       (.x12 ↦ᵣ sp) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word))) := by
  have I0 := sd_x0_spec_gen_within .x12 sp q0 4088 base
  have I1 := sd_x0_spec_gen_within .x12 sp q1 4080 (base + 4)
  have I2 := sd_x0_spec_gen_within .x12 sp q2 4072 (base + 8)
  have I3 := sd_x0_spec_gen_within .x12 sp q3 4064 (base + 12)
  have I4 := sd_x0_spec_gen_within .x12 sp u5 4016 (base + 16)
  have I5 := sd_x0_spec_gen_within .x12 sp u6 4008 (base + 20)
  have I6 := sd_x0_spec_gen_within .x12 sp u7 4000 (base + 24)
  runBlock I0 I1 I2 I3 I4 I5 I6

abbrev divK_phaseB_init2_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseB.drop 7 |>.take 2)

/-- Phase B init part 2: load b[1] and b[2]. 2 instructions. -/
theorem divK_phaseB_init2_spec_within (sp : Word) (base : Word)
    (b1 b2 : Word) (v6 v7 : Word) :
    let cr := divK_phaseB_init2_code base
    cpsTripleWithin 2 base (base + 8) cr
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2))
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2)) := by
  have I0 := ld_spec_gen_within .x6 .x12 sp v6 b1 40 base (by nofun)
  have I1 := ld_spec_gen_within .x7 .x12 sp v7 b2 48 (base + 4) (by nofun)
  runBlock I0 I1

end EvmAsm.Evm64
