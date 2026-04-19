/-
  EvmAsm.Evm64.DivMod.LimbSpec.SubCarryStoreQj

  CPS specs for two small, related blocks that run right after the
  mul-sub inner loop in the Knuth Algorithm D step:
    * `divK_sub_carry_spec` — 4 instructions (LD, SLTU, SUB, SD) that
      subtract the final carry from `u[j+4]` and record the resulting
      borrow.
    * `divK_store_qj_addr_spec` — 3 instructions (SLLI, ADDI, SUB) that
      compute `q_addr = sp + 4088 - 8*j` into x7.
    * `divK_store_qj_write_spec` — 1-instruction SD that actually
      writes `q_hat` at `q_addr`.

  Sixteenth chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees all
  three specs.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Subtract carry from u[j+4].
    4 instructions: LD, SLTU, SUB, SD. Produces borrow (x7). -/
theorem divK_sub_carry_spec (u_base carry_in v5_old v7_old u_top : Word)
    (u_off : BitVec 12) (base : Word) :
    let borrow := if BitVec.ult u_top carry_in then (1 : Word) else 0
    let u_new := u_top - carry_in
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x7 .x5 .x10))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x5 .x5 .x10))
       (CodeReq.singleton (base + 12) (.SD .x6 .x5 u_off))))
    cpsTriple base (base + 16) cr
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       ((u_base + signExtend12 u_off) ↦ₘ u_top))
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ u_new) ** (.x7 ↦ᵣ borrow) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro borrow u_new cr
  have I0 := ld_spec_gen .x5 .x6 u_base v5_old u_top u_off base (by nofun)
  have I1 := sltu_spec_gen .x7 .x5 .x10 v7_old u_top carry_in (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x5 .x10 u_top carry_in (base + 8) (by nofun)
  have I3 := sd_spec_gen .x6 .x5 u_base u_new u_top u_off (base + 12)
  runBlock I0 I1 I2 I3

/-- Store q[j]: compute &q[j] = sp+4088 - j*8, store q_hat.
    First 3 instructions compute q_addr. Then SD stores. Split into 3+1. -/
theorem divK_store_qj_addr_spec (sp j v5_old v7_old : Word)
    (base : Word) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let sp_m8 := sp + signExtend12 4088
    let q_addr := sp_m8 - j_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x7 .x12 4088))
       (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5)))
    cpsTriple base (base + 12) cr
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr)) := by
  intro j_x8 sp_m8 q_addr cr
  have I0 := slli_spec_gen .x5 .x1 v5_old j 3 base (by nofun)
  have I1 := addi_spec_gen .x7 .x12 v7_old sp 4088 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 sp_m8 j_x8 (base + 8) (by nofun)
  runBlock I0 I1 I2

/-- Store q[j]: SD q_hat at q_addr. 1 instruction. -/
theorem divK_store_qj_write_spec (q_addr q_hat q_old : Word) (base : Word) :
    let cr := CodeReq.singleton base (.SD .x7 .x11 0)
    cpsTriple base (base + 4) cr
      ((.x7 ↦ᵣ q_addr) ** (.x11 ↦ᵣ q_hat) ** (q_addr ↦ₘ q_old))
      ((.x7 ↦ᵣ q_addr) ** (.x11 ↦ᵣ q_hat) ** (q_addr ↦ₘ q_hat)) := by
  intro cr
  have hse : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr : q_addr + signExtend12 (0 : BitVec 12) = q_addr := by rw [hse]; bv_omega
  have I0 := sd_spec_gen .x7 .x11 q_addr q_hat q_old 0 base
  rw [haddr] at I0
  runBlock I0

end EvmAsm.Evm64
