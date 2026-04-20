/-
  EvmAsm.Evm64.DivMod.LimbSpec.NormA

  Per-limb CPS specs for the Knuth Algorithm D normalize-a phase:
    * `divK_normA_top_*` — 3-instruction top: LD, SRL, SD.
      Computes `u[4] = a[3] >>> antiShift` (overflow bits from top limb).
    * `divK_normA_mergeA_*` — 5-instruction merge, x5 holds current limb.
      Computes `(current <<< shift) ||| (next >>> antiShift)`; used for u[3]/u[1].
    * `divK_normA_mergeB_*` — 5-instruction merge, x7 holds current limb.
      Same shape as mergeA with registers swapped; used for u[2].
    * `divK_normA_last_*` — 2-instruction last: SLL, SD.
      Computes `u[0] = a[0] <<< shift`.

  Third chunk of the `LimbSpec.lean` split tracked by issue #312. The
  consumer surface is unchanged: `LimbSpec.lean` re-exports this file so
  every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the
  four specs.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

def divK_normA_top_prog (src_off dst_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 src_off, .SRL .x7 .x5 .x2, .SD .x12 .x7 dst_off]

abbrev divK_normA_top_code (src_off dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_top_prog src_off dst_off)

/-- NormA top: LD a[3], SRL to x7, SD u[4]. 3 instructions.
    Computes u[4] = a[3] >>> antiShift (overflow bits from top limb). -/
theorem divK_normA_top_spec (src_off dst_off : BitVec 12)
    (sp val v5 v7 antiShift dst_old : Word) (base : Word) :
    let result := val >>> (antiShift.toNat % 64)
    let cr := divK_normA_top_code src_off dst_off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 src_off) ↦ₘ val) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ val) ** (.x7 ↦ᵣ result) ** (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 src_off) ↦ₘ val) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 val src_off base (by nofun)
  have I1 := srl_spec_gen .x7 .x5 .x2 v7 val antiShift (base + 4) (by nofun)
  have I2 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 8)
  runBlock I0 I1 I2

def divK_normA_mergeA_prog (next_off dst_off : BitVec 12) : List Instr :=
  [.LD .x7 .x12 next_off, .SLL .x5 .x5 .x6, .SRL .x10 .x7 .x2,
   .OR .x5 .x5 .x10, .SD .x12 .x5 dst_off]

abbrev divK_normA_mergeA_code (next_off dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_mergeA_prog next_off dst_off)

/-- NormA merge type A (5 instructions): x5 holds current limb.
    LD next into x7, SLL x5 by shift, SRL x10 from x7 by antiShift, OR into x5, SD.
    Used for u[3] and u[1] computation. -/
theorem divK_normA_mergeA_spec (next_off dst_off : BitVec 12)
    (sp current next v7 v10 shift antiShift dst_old : Word) (base : Word) :
    let shiftedCurr := current <<< (shift.toNat % 64)
    let shiftedNext := next >>> (antiShift.toNat % 64)
    let result := shiftedCurr ||| shiftedNext
    let cr := divK_normA_mergeA_code next_off dst_off base
    cpsTriple base (base + 20) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ current) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ next) ** (.x10 ↦ᵣ shiftedNext) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro shiftedCurr shiftedNext result cr
  have I0 := ld_spec_gen .x7 .x12 sp v7 next next_off base (by nofun)
  have I1 := sll_spec_gen_rd_eq_rs1 .x5 .x6 current shift (base + 4) (by nofun)
  have I2 := srl_spec_gen .x10 .x7 .x2 v10 next antiShift (base + 8) (by nofun)
  have I3 := or_spec_gen_rd_eq_rs1 .x5 .x10 shiftedCurr shiftedNext (base + 12) (by nofun)
  have I4 := sd_spec_gen .x12 .x5 sp result dst_old dst_off (base + 16)
  runBlock I0 I1 I2 I3 I4

def divK_normA_mergeB_prog (next_off dst_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 next_off, .SLL .x7 .x7 .x6, .SRL .x10 .x5 .x2,
   .OR .x7 .x7 .x10, .SD .x12 .x7 dst_off]

abbrev divK_normA_mergeB_code (next_off dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_mergeB_prog next_off dst_off)

/-- NormA merge type B (5 instructions): x7 holds current limb.
    LD next into x5, SLL x7 by shift, SRL x10 from x5 by antiShift, OR into x7, SD.
    Used for u[2] computation. -/
theorem divK_normA_mergeB_spec (next_off dst_off : BitVec 12)
    (sp current next v5 v10 shift antiShift dst_old : Word) (base : Word) :
    let shiftedCurr := current <<< (shift.toNat % 64)
    let shiftedNext := next >>> (antiShift.toNat % 64)
    let result := shiftedCurr ||| shiftedNext
    let cr := divK_normA_mergeB_code next_off dst_off base
    cpsTriple base (base + 20) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ current) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ next) ** (.x7 ↦ᵣ result) ** (.x10 ↦ᵣ shiftedNext) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro shiftedCurr shiftedNext result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 next next_off base (by nofun)
  have I1 := sll_spec_gen_rd_eq_rs1 .x7 .x6 current shift (base + 4) (by nofun)
  have I2 := srl_spec_gen .x10 .x5 .x2 v10 next antiShift (base + 8) (by nofun)
  have I3 := or_spec_gen_rd_eq_rs1 .x7 .x10 shiftedCurr shiftedNext (base + 12) (by nofun)
  have I4 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 16)
  runBlock I0 I1 I2 I3 I4

def divK_normA_last_prog (dst_off : BitVec 12) : List Instr :=
  [.SLL .x7 .x7 .x6, .SD .x12 .x7 dst_off]

abbrev divK_normA_last_code (dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_last_prog dst_off)

/-- NormA last limb (2 instructions): SLL x7 by shift, SD to dst_off.
    Computes u[0] = a[0] <<< shift. -/
theorem divK_normA_last_spec (dst_off : BitVec 12)
    (sp val shift dst_old : Word) (base : Word) :
    let result := val <<< (shift.toNat % 64)
    let cr := divK_normA_last_code dst_off base
    cpsTriple base (base + 8) cr
      (
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ val) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro result cr
  have I0 := sll_spec_gen_rd_eq_rs1 .x7 .x6 val shift base (by nofun)
  have I1 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 4)
  runBlock I0 I1

end EvmAsm.Evm64
