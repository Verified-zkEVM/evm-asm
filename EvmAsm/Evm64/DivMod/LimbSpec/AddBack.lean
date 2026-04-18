/-
  EvmAsm.Evm64.DivMod.LimbSpec.AddBack

  CPS specs for one limb of the Knuth Algorithm D "add-back" correction,
  which un-does the mul-sub when `q_hat` over-shot by 1:
    * `divK_addback_partA_spec` — 5 instructions (LD, LD, ADD, SLTU, ADD):
      load v[i] and u[j+i], form `u_plus_carry = u_i + carry_in`, its
      SLTU `carry1`, and `u_new = u_plus_carry + v_i`.
    * `divK_addback_partB_spec` — 3 instructions (SLTU, OR, SD): form
      `carry2 = u_new < v_i`, OR with `carry1` for `carry_out`, store
      `u_new`.

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
theorem divK_addback_partA_spec (sp u_base carry_in v5_old v2_old v_i u_i : Word)
    (v_off : BitVec 12) (u_off : BitVec 12) (base : Word) :
    let u_plus_carry := u_i + carry_in
    let carry1 := if BitVec.ult u_plus_carry carry_in then (1 : Word) else 0
    let u_new := u_plus_carry + v_i
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x7 .x2 .x7))
       (CodeReq.singleton (base + 16) (.ADD .x2 .x2 .x5)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry1) **
       (.x5 ↦ᵣ v_i) ** (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i)) := by
  intro u_plus_carry carry1 u_new cr
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun)
  have I1 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 4) (by nofun)
  have I2 := add_spec_gen_rd_eq_rs1 .x2 .x7 u_i carry_in (base + 8) (by nofun)
  have I3 := sltu_spec_gen_rd_eq_rs2 .x7 .x2 u_plus_carry carry_in (base + 12) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x2 .x5 u_plus_carry v_i (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

/-- Add-back Part B: SLTU carry2, OR carry_out, SD u_new.
    3 instructions. Produces carry_out (x7) and stores u_new. -/
theorem divK_addback_partB_spec (u_base carry1 v_i u_new u_i : Word)
    (u_off : BitVec 12) (base : Word) :
    let carry2 := if BitVec.ult u_new v_i then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLTU .x5 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 4) (.OR .x7 .x7 .x5))
       (CodeReq.singleton (base + 8) (.SD .x6 .x2 u_off)))
    cpsTriple base (base + 12) cr
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry1) **
       (.x5 ↦ᵣ v_i) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ carry2) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro carry2 carry_out cr
  have I0 := sltu_spec_gen_rd_eq_rs2 .x5 .x2 u_new v_i base (by nofun)
  have I1 := or_spec_gen_rd_eq_rs1 .x7 .x5 carry1 carry2 (base + 4) (by nofun)
  have I2 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 8)
  runBlock I0 I1 I2

end EvmAsm.Evm64
