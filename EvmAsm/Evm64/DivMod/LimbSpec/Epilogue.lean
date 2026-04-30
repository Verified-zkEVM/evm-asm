/-
  EvmAsm.Evm64.DivMod.LimbSpec.Epilogue

  Per-limb CPS specs for the DIV/MOD epilogue — copy the 4-limb result
  (q[0..3] for DIV, u[0..3] for MOD) from scratch space out to the stack:
    * `divK_epilogue_load_*` — 4-instruction load phase: LD×4.
      Loads the four limbs into x5, x6, x7, x10.
    * `divK_epilogue_store_*` — 6-instruction store phase: ADDI sp+32,
      SD×4, JAL to exit.

  Fourth chunk of the `LimbSpec.lean` split tracked by issue #312. The
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

def divK_epilogue_load_prog (off0 off1 off2 off3 : BitVec 12) : List Instr :=
  [.LD .x5 .x12 off0, .LD .x6 .x12 off1, .LD .x7 .x12 off2, .LD .x10 .x12 off3]

abbrev divK_epilogue_load_code (off0 off1 off2 off3 : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_epilogue_load_prog off0 off1 off2 off3)

/-- Epilogue load phase: load 4 values from scratch space. 4 instructions.
    Loads q[0..3] (for DIV) or u[0..3] (for MOD) into x5, x6, x7, x10. -/
theorem divK_epilogue_load_spec_within (off0 off1 off2 off3 : BitVec 12)
    (sp r0 r1 r2 r3 v5 v6 v7 v10 : Word) (base : Word) :
    let cr := divK_epilogue_load_code off0 off1 off2 off3 base
    cpsTripleWithin 4 base (base + 16) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 off0) ↦ₘ r0) ** ((sp + signExtend12 off1) ↦ₘ r1) **
       ((sp + signExtend12 off2) ↦ₘ r2) ** ((sp + signExtend12 off3) ↦ₘ r3))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) ** (.x10 ↦ᵣ r3) **
       ((sp + signExtend12 off0) ↦ₘ r0) ** ((sp + signExtend12 off1) ↦ₘ r1) **
       ((sp + signExtend12 off2) ↦ₘ r2) ** ((sp + signExtend12 off3) ↦ₘ r3)) := by
  have I0 := ld_spec_gen_within .x5 .x12 sp v5 r0 off0 base (by nofun)
  have I1 := ld_spec_gen_within .x6 .x12 sp v6 r1 off1 (base + 4) (by nofun)
  have I2 := ld_spec_gen_within .x7 .x12 sp v7 r2 off2 (base + 8) (by nofun)
  have I3 := ld_spec_gen_within .x10 .x12 sp v10 r3 off3 (base + 12) (by nofun)
  runBlock I0 I1 I2 I3

/-- Epilogue load phase: load 4 values from scratch space. 4 instructions.
    Loads q[0..3] (for DIV) or u[0..3] (for MOD) into x5, x6, x7, x10. -/
def divK_epilogue_store_prog (jal_off : BitVec 21) : List Instr :=
  [.ADDI .x12 .x12 32, .SD .x12 .x5 0, .SD .x12 .x6 8,
   .SD .x12 .x7 16, .SD .x12 .x10 24, .JAL .x0 jal_off]

abbrev divK_epilogue_store_code (jal_off : BitVec 21) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_epilogue_store_prog jal_off)

/-- Epilogue store phase: ADDI sp+32, store 4 values, JAL to exit. 6 instructions. -/
theorem divK_epilogue_store_spec_within (sp : Word) (base : Word)
    (r0 r1 r2 r3 m0 m8 m16 m24 : Word) (jal_off : BitVec 21) :
    let cr := divK_epilogue_store_code jal_off base
    cpsTripleWithin 6 base (base + 20 + signExtend21 jal_off) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) ** (.x10 ↦ᵣ r3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (
       (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) ** (.x10 ↦ᵣ r3) **
       ((sp + 32) ↦ₘ r0) ** ((sp + 40) ↦ₘ r1) **
       ((sp + 48) ↦ₘ r2) ** ((sp + 56) ↦ₘ r3)) := by
  have I0 := addi_spec_gen_same_within .x12 sp 32 base (by nofun)
  have I1 := sd_spec_gen_within .x12 .x5 (sp + 32) r0 m0 0 (base + 4)
  have I2 := sd_spec_gen_within .x12 .x6 (sp + 32) r1 m8 8 (base + 8)
  have I3 := sd_spec_gen_within .x12 .x7 (sp + 32) r2 m16 16 (base + 12)
  have I4 := sd_spec_gen_within .x12 .x10 (sp + 32) r3 m24 24 (base + 16)
  have I5 := jal_x0_spec_gen_within jal_off (base + 20)
  runBlock I0 I1 I2 I3 I4 I5

end EvmAsm.Evm64
