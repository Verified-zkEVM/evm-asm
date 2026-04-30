/-
  EvmAsm.Evm64.DivMod.LimbSpec.NormB

  Per-limb CPS specs for the Knuth Algorithm D normalize-b phase:
    * `divK_normB_merge_prog` / `divK_normB_merge_code` / `divK_normB_merge_spec_within`
      — 6-instruction merge: LD high, LD low, SLL high<<shift,
        SRL low>>antiShift, OR, SD high. Computes
        `result = (high <<< shift) ||| (low >>> antiShift)`.
    * `divK_normB_last_prog` / `divK_normB_last_code` / `divK_normB_last_spec_within`
      — 3-instruction last-limb: LD, SLL, SD. Computes `val <<< shift`.

  Mirror of the `Denorm` merge/last pair with SLL/SRL swapped: NormB is
  the left-shift that the divisor and dividend undergo before the Knuth
  loop, and `Denorm` undoes it on the remainder.

  Second chunk of the `LimbSpec.lean` split tracked by issue #312. The
  consumer surface is unchanged: `LimbSpec.lean` re-exports this file so
  every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the
  two specs.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

def divK_normB_merge_prog (high_off low_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 high_off, .LD .x7 .x12 low_off, .SLL .x5 .x5 .x6,
   .SRL .x7 .x7 .x2, .OR .x5 .x5 .x7, .SD .x12 .x5 high_off]

abbrev divK_normB_merge_code (high_off low_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normB_merge_prog high_off low_off)

/-- NormB merge limb (6 instructions): LD high, LD low, SLL, SRL, OR, SD.
    Computes result = (high <<< shift) ||| (low >>> antiShift) and stores to high_off.
    x6 = shift, x2 = antiShift (= 64 - shift as unsigned). -/
theorem divK_normB_merge_spec_within (high_off low_off : BitVec 12)
    (sp high low v5 v7 shift antiShift : Word) (base : Word) :
    let shiftedHigh := high <<< (shift.toNat % 64)
    let shiftedLow := low >>> (antiShift.toNat % 64)
    let result := shiftedHigh ||| shiftedLow
    let cr := divK_normB_merge_code high_off low_off base
    cpsTripleWithin 6 base (base + 24) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 high_off) ↦ₘ high) **
       ((sp + signExtend12 low_off) ↦ₘ low))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ shiftedLow) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 high_off) ↦ₘ result) **
       ((sp + signExtend12 low_off) ↦ₘ low)) := by
  intro shiftedHigh shiftedLow result cr
  have I0 := ld_spec_gen_within .x5 .x12 sp v5 high high_off base (by nofun)
  have I1 := ld_spec_gen_within .x7 .x12 sp v7 low low_off (base + 4) (by nofun)
  have I2 := sll_spec_gen_rd_eq_rs1_within .x5 .x6 high shift (base + 8) (by nofun)
  have I3 := srl_spec_gen_rd_eq_rs1_within .x7 .x2 low antiShift (base + 12) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1_within .x5 .x7 shiftedHigh shiftedLow (base + 16) (by nofun)
  have I5 := sd_spec_gen_within .x12 .x5 sp result high high_off (base + 20)
  runBlock I0 I1 I2 I3 I4 I5

/-- NormB merge limb (6 instructions): LD high, LD low, SLL, SRL, OR, SD.
    Computes result = (high <<< shift) ||| (low >>> antiShift) and stores to high_off.
    x6 = shift, x2 = antiShift (= 64 - shift as unsigned). -/
def divK_normB_last_prog (off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 off, .SLL .x5 .x5 .x6, .SD .x12 .x5 off]

abbrev divK_normB_last_code (off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normB_last_prog off)

/-- NormB last limb (3 instructions): LD, SLL, SD.
    Computes result = val <<< shift and stores to off. -/
theorem divK_normB_last_spec_within (off : BitVec 12)
    (sp val v5 shift : Word) (base : Word) :
    let result := val <<< (shift.toNat % 64)
    let cr := divK_normB_last_code off base
    cpsTripleWithin 3 base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ val))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ result)) := by
  intro result cr
  have I0 := ld_spec_gen_within .x5 .x12 sp v5 val off base (by nofun)
  have I1 := sll_spec_gen_rd_eq_rs1_within .x5 .x6 val shift (base + 4) (by nofun)
  have I2 := sd_spec_gen_within .x12 .x5 sp result val off (base + 8)
  runBlock I0 I1 I2

end EvmAsm.Evm64
