/-
  EvmAsm.Evm64.DivMod.LimbSpec.MulSub

  CPS specs for one limb of the Knuth Algorithm D mul-sub inner step,
  which computes `u[j..j+4] -= qHat * v[0..3]` one limb at a time:
    * `divK_mulsub_partA_spec_within` — 6 instructions (LD, MUL, MULHU, ADD,
      SLTU, ADD): load v[i], compute `prodLo = qHat * v_i`,
      `prodHi = MULHU qHat v_i`, and form `fullSub = prodLo +
      carryIn` and `partialCarry = (fullSub < carryIn) + prodHi`.
    * `divK_mulsub_partB_spec_within` — 5 instructions (LD, SLTU, SUB, ADD, SD):
      load u[j+i], compute `uNew = u_i - fullSub`,
      `carryOut = partialCarry + (u_i < fullSub)`, store `uNew`.

  Fourteenth chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees both
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

/-- Mul-sub limb Part A: LD v[i], MUL, MULHU, ADD, SLTU, ADD.
    6 instructions. Produces fullSub (x7) and partialCarry (x10). -/
theorem divK_mulsub_partA_spec_within (sp qHat carryIn v5Old v7Old v_i : Word)
    (v_off : BitVec 12) (base : Word) :
    let prodLo := qHat * v_i
    let prodHi := rv64_mulhu qHat v_i
    let fullSub := prodLo + carryIn
    let borrowAdd := if BitVec.ult fullSub carryIn then (1 : Word) else 0
    let partialCarry := borrowAdd + prodHi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.MULHU .x5 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x7 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x10 .x7 .x10))
       (CodeReq.singleton (base + 20) (.ADD .x10 .x10 .x5))))))
    cpsTripleWithin 6 base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) ** (.x10 ↦ᵣ carryIn) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) ** (.x10 ↦ᵣ partialCarry) **
       (.x5 ↦ᵣ prodHi) ** (.x7 ↦ᵣ fullSub) **
       ((sp + signExtend12 v_off) ↦ₘ v_i)) := by
  intro prodLo prodHi fullSub borrowAdd partialCarry cr
  have I0 := ld_spec_gen_within .x5 .x12 sp v5Old v_i v_off base (by nofun)
  have I1 := mul_spec_gen_within .x7 .x11 .x5 v7Old qHat v_i (base + 4) (by nofun)
  have I2 := mulhu_spec_gen_rd_eq_rs2_within .x5 .x11 qHat v_i (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1_within .x7 .x10 prodLo carryIn (base + 12) (by nofun)
  have I4 := sltu_spec_gen_rd_eq_rs2_within .x10 .x7 fullSub carryIn (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x10 .x5 borrowAdd prodHi (base + 20) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5

/-- Mul-sub limb Part B: LD u[j+i], SLTU, SUB, ADD, SD.
    5 instructions. Produces carryOut (x10) and stores uNew. -/
theorem divK_mulsub_partB_spec_within (uBase partialCarry prodHi fullSub v2Old u_i : Word)
    (u_off : BitVec 12) (base : Word) :
    let borrowSub := if BitVec.ult u_i fullSub then (1 : Word) else 0
    let uNew := u_i - fullSub
    let carryOut := partialCarry + borrowSub
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x5 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x10 .x10 .x5))
       (CodeReq.singleton (base + 16) (.SD .x6 .x2 u_off)))))
    cpsTripleWithin 5 base (base + 20) cr
      ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ partialCarry) **
       (.x5 ↦ᵣ prodHi) ** (.x7 ↦ᵣ fullSub) ** (.x2 ↦ᵣ v2Old) **
       ((uBase + signExtend12 u_off) ↦ₘ u_i))
      ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ carryOut) **
       (.x5 ↦ᵣ borrowSub) ** (.x7 ↦ᵣ fullSub) ** (.x2 ↦ᵣ uNew) **
       ((uBase + signExtend12 u_off) ↦ₘ uNew)) := by
  intro borrowSub uNew carryOut cr
  have I0 := ld_spec_gen_within .x2 .x6 uBase v2Old u_i u_off base (by nofun)
  have I1 := sltu_spec_gen_within .x5 .x2 .x7 prodHi u_i fullSub (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1_within .x2 .x7 u_i fullSub (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1_within .x10 .x5 partialCarry borrowSub (base + 12) (by nofun)
  have I4 := sd_spec_gen_within .x6 .x2 uBase uNew u_i u_off (base + 16)
  runBlock I0 I1 I2 I3 I4

end EvmAsm.Evm64
