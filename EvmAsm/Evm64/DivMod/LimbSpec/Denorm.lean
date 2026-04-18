/-
  EvmAsm.Evm64.DivMod.LimbSpec.Denorm

  Per-limb CPS specs for the Knuth Algorithm D denormalize phase:
    * `divK_denorm_merge_prog` / `divK_denorm_merge_code` / `divK_denorm_merge_spec`
      — 6-instruction merge: LD curr, LD next, SRL curr>>shift,
        SLL next<<anti_shift, OR, SD curr. Computes
        `result = (curr >>> shift) ||| (next <<< anti_shift)`.
    * `divK_denorm_last_prog` / `divK_denorm_last_code` / `divK_denorm_last_spec`
      — 3-instruction last-limb: LD, SRL, SD. Computes `val >>> shift`.

  Same structure as the `NormB` merge/last pair but with SRL/SLL swapped
  (right-shift with merge from the *higher* limb), since denormalization
  undoes the left-shift applied during normalization.

  Extracted from the monolithic `EvmAsm/Evm64/DivMod/LimbSpec.lean` as a
  first chunk of the split tracked by issue #312. The consumer surface
  is unchanged: `LimbSpec.lean` re-exports this file so every existing
  `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the two specs.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

def divK_denorm_merge_prog (curr_off next_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 curr_off, .LD .x7 .x12 next_off, .SRL .x5 .x5 .x6,
   .SLL .x7 .x7 .x2, .OR .x5 .x5 .x7, .SD .x12 .x5 curr_off]

abbrev divK_denorm_merge_code (curr_off next_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_denorm_merge_prog curr_off next_off)

/-- Denorm merge limb (6 instructions): LD curr, LD next, SRL, SLL, OR, SD.
    Computes result = (curr >>> shift) ||| (next <<< anti_shift) and stores to curr_off.
    x6 = shift, x2 = anti_shift. -/
theorem divK_denorm_merge_spec (curr_off next_off : BitVec 12)
    (sp curr next v5 v7 shift anti_shift : Word) (base : Word) :
    let shifted_curr := curr >>> (shift.toNat % 64)
    let shifted_next := next <<< (anti_shift.toNat % 64)
    let result := shifted_curr ||| shifted_next
    let cr := divK_denorm_merge_code curr_off next_off base
    cpsTriple base (base + 24) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 curr_off) ↦ₘ curr) **
       ((sp + signExtend12 next_off) ↦ₘ next))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ shifted_next) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 curr_off) ↦ₘ result) **
       ((sp + signExtend12 next_off) ↦ₘ next)) := by
  intro shifted_curr shifted_next result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 curr curr_off base (by nofun)
  have I1 := ld_spec_gen .x7 .x12 sp v7 next next_off (base + 4) (by nofun)
  have I2 := srl_spec_gen_rd_eq_rs1 .x5 .x6 curr shift (base + 8) (by nofun)
  have I3 := sll_spec_gen_rd_eq_rs1 .x7 .x2 next anti_shift (base + 12) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x7 shifted_curr shifted_next (base + 16) (by nofun)
  have I5 := sd_spec_gen .x12 .x5 sp result curr curr_off (base + 20)
  runBlock I0 I1 I2 I3 I4 I5

def divK_denorm_last_prog (off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 off, .SRL .x5 .x5 .x6, .SD .x12 .x5 off]

abbrev divK_denorm_last_code (off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_denorm_last_prog off)

/-- Denorm last limb (3 instructions): LD, SRL, SD.
    Computes result = val >>> shift and stores to off. -/
theorem divK_denorm_last_spec (off : BitVec 12)
    (sp val v5 shift : Word) (base : Word) :
    let result := val >>> (shift.toNat % 64)
    let cr := divK_denorm_last_code off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ val))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ result)) := by
  intro result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 val off base (by nofun)
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 val shift (base + 4) (by nofun)
  have I2 := sd_spec_gen .x12 .x5 sp result val off (base + 8)
  runBlock I0 I1 I2

end EvmAsm.Evm64
