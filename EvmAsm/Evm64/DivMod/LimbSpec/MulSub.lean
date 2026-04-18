/-
  EvmAsm.Evm64.DivMod.LimbSpec.MulSub

  CPS specs for one limb of the Knuth Algorithm D mul-sub inner step,
  which computes `u[j..j+4] -= q_hat * v[0..3]` one limb at a time:
    * `divK_mulsub_partA_spec` — 6 instructions (LD, MUL, MULHU, ADD,
      SLTU, ADD): load v[i], compute `prod_lo = q_hat * v_i`,
      `prod_hi = MULHU q_hat v_i`, and form `full_sub = prod_lo +
      carry_in` and `partial_carry = (full_sub < carry_in) + prod_hi`.
    * `divK_mulsub_partB_spec` — 5 instructions (LD, SLTU, SUB, ADD, SD):
      load u[j+i], compute `u_new = u_i - full_sub`,
      `carry_out = partial_carry + (u_i < full_sub)`, store `u_new`.

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
    6 instructions. Produces full_sub (x7) and partial_carry (x10). -/
theorem divK_mulsub_partA_spec (sp q_hat carry_in v5_old v7_old v_i : Word)
    (v_off : BitVec 12) (base : Word) :
    let prod_lo := q_hat * v_i
    let prod_hi := rv64_mulhu q_hat v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let partial_carry := borrow_add + prod_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.MULHU .x5 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x7 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x10 .x7 .x10))
       (CodeReq.singleton (base + 20) (.ADD .x10 .x10 .x5))))))
    cpsTriple base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ partial_carry) **
       (.x5 ↦ᵣ prod_hi) ** (.x7 ↦ᵣ full_sub) **
       ((sp + signExtend12 v_off) ↦ₘ v_i)) := by
  intro prod_lo prod_hi full_sub borrow_add partial_carry cr
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun)
  have I1 := mul_spec_gen .x7 .x11 .x5 v7_old q_hat v_i (base + 4) (by nofun)
  have I2 := mulhu_spec_gen_rd_eq_rs2 .x5 .x11 q_hat v_i (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x7 .x10 prod_lo carry_in (base + 12) (by nofun)
  have I4 := sltu_spec_gen_rd_eq_rs2 .x10 .x7 full_sub carry_in (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1 .x10 .x5 borrow_add prod_hi (base + 20) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5

/-- Mul-sub limb Part B: LD u[j+i], SLTU, SUB, ADD, SD.
    5 instructions. Produces carry_out (x10) and stores u_new. -/
theorem divK_mulsub_partB_spec (u_base partial_carry prod_hi full_sub v2_old u_i : Word)
    (u_off : BitVec 12) (base : Word) :
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    let u_new := u_i - full_sub
    let carry_out := partial_carry + borrow_sub
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x5 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x10 .x10 .x5))
       (CodeReq.singleton (base + 16) (.SD .x6 .x2 u_off)))))
    cpsTriple base (base + 20) cr
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ partial_carry) **
       (.x5 ↦ᵣ prod_hi) ** (.x7 ↦ᵣ full_sub) ** (.x2 ↦ᵣ v2_old) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ borrow_sub) ** (.x7 ↦ᵣ full_sub) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro borrow_sub u_new carry_out cr
  have I0 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off base (by nofun)
  have I1 := sltu_spec_gen .x5 .x2 .x7 prod_hi u_i full_sub (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x2 .x7 u_i full_sub (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x10 .x5 partial_carry borrow_sub (base + 12) (by nofun)
  have I4 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 16)
  runBlock I0 I1 I2 I3 I4

end EvmAsm.Evm64
