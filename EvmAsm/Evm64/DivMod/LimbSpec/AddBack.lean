/-
  EvmAsm.Evm64.DivMod.LimbSpec.AddBack

  CPS specs for one limb of the Knuth Algorithm D "add-back" correction,
  which un-does the mul-sub when `q_hat` over-shot by 1:
    * `divK_addback_partA_spec` — 5 instructions (LD, LD, ADD, SLTU, ADD):
      load v[i] and u[j+i], form `uPlusCarry = u_i + carryIn`, its
      SLTU `carry1`, and `uNew = uPlusCarry + v_i`.
    * `divK_addback_partB_spec` — 3 instructions (SLTU, OR, SD): form
      `carry2 = uNew < v_i`, OR with `carry1` for `carryOut`, store
      `uNew`.

  Fifteenth chunk of the `LimbSpec.lean` split tracked by issue #312.
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

/-- Add-back Part A: LD v[i], LD u[j+i], ADD carry, SLTU carry1, ADD v[i].
    5 instructions. Produces sum (x2) and carry1 (x7). -/
theorem divK_addback_partA_spec (sp u_base carryIn v5_old v2_old v_i u_i : Word)
    (v_off : BitVec 12) (u_off : BitVec 12) (base : Word) :
    let uPlusCarry := u_i + carryIn
    let carry1 := if BitVec.ult uPlusCarry carryIn then (1 : Word) else 0
    let uNew := uPlusCarry + v_i
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x7 .x2 .x7))
       (CodeReq.singleton (base + 16) (.ADD .x2 .x2 .x5)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carryIn) **
       (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry1) **
       (.x5 ↦ᵣ v_i) ** (.x2 ↦ᵣ uNew) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i)) := by
  intro uPlusCarry carry1 uNew cr
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun)
  have I1 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 4) (by nofun)
  have I2 := add_spec_gen_rd_eq_rs1 .x2 .x7 u_i carryIn (base + 8) (by nofun)
  have I3 := sltu_spec_gen_rd_eq_rs2 .x7 .x2 uPlusCarry carryIn (base + 12) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x2 .x5 uPlusCarry v_i (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

/-- Add-back Part B: SLTU carry2, OR carryOut, SD uNew.
    3 instructions. Produces carryOut (x7) and stores uNew. -/
theorem divK_addback_partB_spec (u_base carry1 v_i uNew u_i : Word)
    (u_off : BitVec 12) (base : Word) :
    let carry2 := if BitVec.ult uNew v_i then (1 : Word) else 0
    let carryOut := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLTU .x5 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 4) (.OR .x7 .x7 .x5))
       (CodeReq.singleton (base + 8) (.SD .x6 .x2 u_off)))
    cpsTriple base (base + 12) cr
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry1) **
       (.x5 ↦ᵣ v_i) ** (.x2 ↦ᵣ uNew) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carryOut) **
       (.x5 ↦ᵣ carry2) ** (.x2 ↦ᵣ uNew) **
       ((u_base + signExtend12 u_off) ↦ₘ uNew)) := by
  intro carry2 carryOut cr
  have I0 := sltu_spec_gen_rd_eq_rs2 .x5 .x2 uNew v_i base (by nofun)
  have I1 := or_spec_gen_rd_eq_rs1 .x7 .x5 carry1 carry2 (base + 4) (by nofun)
  have I2 := sd_spec_gen .x6 .x2 u_base uNew u_i u_off (base + 8)
  runBlock I0 I1 I2

end EvmAsm.Evm64
