/-
  EvmAsm.Evm64.DivMod.LimbSpec.MulSubLimb

  Composed per-limb specs for the `mul-sub` and `add-back` inner loops
  of the Knuth Algorithm D step:
    * `divK_mulsub_limb_spec` — 11-instruction straight-line composition
      of `partA` (6 instrs) + `partB` (5 instrs): `u -= q_hat * v_i`
      with carry propagation.
    * `divK_addback_limb_spec` — 8-instruction straight-line composition
      of add-back `partA` (5 instrs) + `partB` (3 instrs): `u += v_i`
      with carry propagation, used when `q_hat` was over-shot.

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
    Input: q_hat (x11), carry_in (x10), v[i] and u[j+i] in memory.
    Output: carry_out (x10), u_new stored. -/
theorem divK_mulsub_limb_spec
    (sp u_base q_hat carry_in v5_old v7_old v2_old v_i u_i : Word)
    (v_off u_off : BitVec 12) (base : Word) :
    let prod_lo := q_hat * v_i
    let prod_hi := rv64_mulhu q_hat v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let partial_carry := borrow_add + prod_hi
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    let u_new := u_i - full_sub
    let carry_out := partial_carry + borrow_sub
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
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_in) **
       (.x6 ↦ᵣ u_base) ** (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_out) **
       (.x6 ↦ᵣ u_base) ** (.x5 ↦ᵣ borrow_sub) ** (.x7 ↦ᵣ full_sub) **
       (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro prod_lo prod_hi full_sub borrow_add partial_carry borrow_sub u_new carry_out cr
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun)
  have I1 := mul_spec_gen .x7 .x11 .x5 v7_old q_hat v_i (base + 4) (by nofun)
  have I2 := mulhu_spec_gen_rd_eq_rs2 .x5 .x11 q_hat v_i (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x7 .x10 prod_lo carry_in (base + 12) (by nofun)
  have I4 := sltu_spec_gen_rd_eq_rs2 .x10 .x7 full_sub carry_in (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1 .x10 .x5 borrow_add prod_hi (base + 20) (by nofun)
  have I6 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 24) (by nofun)
  have I7 := sltu_spec_gen .x5 .x2 .x7 prod_hi u_i full_sub (base + 28) (by nofun)
  have I8 := sub_spec_gen_rd_eq_rs1 .x2 .x7 u_i full_sub (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1 .x10 .x5 partial_carry borrow_sub (base + 36) (by nofun)
  have I10 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 40)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10

/-- Add-back full limb: partA (5 instrs) + partB (3 instrs) = 8 instructions.
    Input: carry_in (x7), v[i] and u[j+i] in memory.
    Output: carry_out (x7), u_new stored. -/
theorem divK_addback_limb_spec
    (sp u_base carry_in v5_old v2_old v_i u_i : Word)
    (v_off u_off : BitVec 12) (base : Word) :
    let u_plus_carry := u_i + carry_in
    let carry1 := if BitVec.ult u_plus_carry carry_in then (1 : Word) else 0
    let u_new := u_plus_carry + v_i
    let carry2 := if BitVec.ult u_new v_i then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
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
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ carry2) ** (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro u_plus_carry carry1 u_new carry2 carry_out cr
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun)
  have I1 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 4) (by nofun)
  have I2 := add_spec_gen_rd_eq_rs1 .x2 .x7 u_i carry_in (base + 8) (by nofun)
  have I3 := sltu_spec_gen_rd_eq_rs2 .x7 .x2 u_plus_carry carry_in (base + 12) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x2 .x5 u_plus_carry v_i (base + 16) (by nofun)
  have I5 := sltu_spec_gen_rd_eq_rs2 .x5 .x2 u_new v_i (base + 20) (by nofun)
  have I6 := or_spec_gen_rd_eq_rs1 .x7 .x5 carry1 carry2 (base + 24) (by nofun)
  have I7 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 28)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7

end EvmAsm.Evm64
