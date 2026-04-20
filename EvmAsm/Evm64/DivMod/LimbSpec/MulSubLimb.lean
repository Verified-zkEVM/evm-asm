/-
  EvmAsm.Evm64.DivMod.LimbSpec.MulSubLimb

  Composed per-limb specs for the `mul-sub` and `add-back` inner loops
  of the Knuth Algorithm D step:
    * `divK_mulsub_limb_spec` — 11-instruction straight-line composition
      of `partA` (6 instrs) + `partB` (5 instrs): `u -= qHat * v_i`
      with carry propagation.
    * `divK_addback_limb_spec` — 8-instruction straight-line composition
      of add-back `partA` (5 instrs) + `partB` (3 instrs): `u += v_i`
      with carry propagation, used when `qHat` was over-shot.

  Twenty-sixth chunk of the `LimbSpec.lean` split tracked by issue #312.
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

/-- Mul-sub full limb: partA (6 instrs) + partB (5 instrs) = 11 instructions.
    Input: qHat (x11), carryIn (x10), v[i] and u[j+i] in memory.
    Output: carryOut (x10), uNew stored. -/
theorem divK_mulsub_limb_spec
    (sp uBase qHat carryIn v5_old v7_old v2_old v_i u_i : Word)
    (v_off u_off : BitVec 12) (base : Word) :
    let prodLo := qHat * v_i
    let prodHi := rv64_mulhu qHat v_i
    let fullSub := prodLo + carryIn
    let borrowAdd := if BitVec.ult fullSub carryIn then (1 : Word) else 0
    let partialCarry := borrowAdd + prodHi
    let borrowSub := if BitVec.ult u_i fullSub then (1 : Word) else 0
    let uNew := u_i - fullSub
    let carryOut := partialCarry + borrowSub
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.MULHU .x5 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x7 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x10 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADD .x10 .x10 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SLTU .x5 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SUB .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 36) (.ADD .x10 .x10 .x5))
       (CodeReq.singleton (base + 40) (.SD .x6 .x2 u_off)))))))))))
    cpsTriple base (base + 44) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) ** (.x10 ↦ᵣ carryIn) **
       (.x6 ↦ᵣ uBase) ** (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((uBase + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) ** (.x10 ↦ᵣ carryOut) **
       (.x6 ↦ᵣ uBase) ** (.x5 ↦ᵣ borrowSub) ** (.x7 ↦ᵣ fullSub) **
       (.x2 ↦ᵣ uNew) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((uBase + signExtend12 u_off) ↦ₘ uNew)) := by
  intro prodLo prodHi fullSub borrowAdd partialCarry borrowSub uNew carryOut cr
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun)
  have I1 := mul_spec_gen .x7 .x11 .x5 v7_old qHat v_i (base + 4) (by nofun)
  have I2 := mulhu_spec_gen_rd_eq_rs2 .x5 .x11 qHat v_i (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x7 .x10 prodLo carryIn (base + 12) (by nofun)
  have I4 := sltu_spec_gen_rd_eq_rs2 .x10 .x7 fullSub carryIn (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1 .x10 .x5 borrowAdd prodHi (base + 20) (by nofun)
  have I6 := ld_spec_gen .x2 .x6 uBase v2_old u_i u_off (base + 24) (by nofun)
  have I7 := sltu_spec_gen .x5 .x2 .x7 prodHi u_i fullSub (base + 28) (by nofun)
  have I8 := sub_spec_gen_rd_eq_rs1 .x2 .x7 u_i fullSub (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1 .x10 .x5 partialCarry borrowSub (base + 36) (by nofun)
  have I10 := sd_spec_gen .x6 .x2 uBase uNew u_i u_off (base + 40)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10

/-- Add-back full limb: partA (5 instrs) + partB (3 instrs) = 8 instructions.
    Input: carryIn (x7), v[i] and u[j+i] in memory.
    Output: carryOut (x7), uNew stored. -/
theorem divK_addback_limb_spec
    (sp uBase carryIn v5_old v2_old v_i u_i : Word)
    (v_off u_off : BitVec 12) (base : Word) :
    let uPlusCarry := u_i + carryIn
    let carry1 := if BitVec.ult uPlusCarry carryIn then (1 : Word) else 0
    let uNew := uPlusCarry + v_i
    let carry2 := if BitVec.ult uNew v_i then (1 : Word) else 0
    let carryOut := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x7 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.ADD .x2 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SLTU .x5 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x7 .x7 .x5))
       (CodeReq.singleton (base + 28) (.SD .x6 .x2 u_off))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ carryIn) **
       (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((uBase + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ carryOut) **
       (.x5 ↦ᵣ carry2) ** (.x2 ↦ᵣ uNew) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((uBase + signExtend12 u_off) ↦ₘ uNew)) := by
  intro uPlusCarry carry1 uNew carry2 carryOut cr
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun)
  have I1 := ld_spec_gen .x2 .x6 uBase v2_old u_i u_off (base + 4) (by nofun)
  have I2 := add_spec_gen_rd_eq_rs1 .x2 .x7 u_i carryIn (base + 8) (by nofun)
  have I3 := sltu_spec_gen_rd_eq_rs2 .x7 .x2 uPlusCarry carryIn (base + 12) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x2 .x5 uPlusCarry v_i (base + 16) (by nofun)
  have I5 := sltu_spec_gen_rd_eq_rs2 .x5 .x2 uNew v_i (base + 20) (by nofun)
  have I6 := or_spec_gen_rd_eq_rs1 .x7 .x5 carry1 carry2 (base + 24) (by nofun)
  have I7 := sd_spec_gen .x6 .x2 uBase uNew u_i u_off (base + 28)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7

end EvmAsm.Evm64
