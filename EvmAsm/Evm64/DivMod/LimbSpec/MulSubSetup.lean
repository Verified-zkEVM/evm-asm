/-
  EvmAsm.Evm64.DivMod.LimbSpec.MulSubSetup

  CPS specs for the small setup/save/init blocks around the mul-sub and
  add-back inner loops of the Knuth Algorithm D step:
    * `divK_mulsub_setup_spec` — 5 instructions (LD, SLLI, ADDI, SUB,
      ADDI) that restore `j` from scratch, compute `u_base = sp - 8*j`,
      and zero the carry.
    * `divK_save_j_spec` — single SD storing `j` back to scratch.
    * `divK_addback_init_spec` — single ADDI zeroing the add-back carry.

  Eighteenth chunk of the `LimbSpec.lean` split tracked by issue #312.
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

/-- Mul-sub setup: restore j from scratch, compute u_base, zero carry. -/
theorem divK_mulsub_setup_spec (sp qHat j v1_old v5_old v6_old v10_old : Word)
    (base : Word) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let sp_m40 := sp + signExtend12 4056
    let u_base := sp_m40 - j_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3976))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x6 .x12 4056))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x6 .x6 .x5))
       (CodeReq.singleton (base + 16) (.ADDI .x10 .x0 0)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x1 ↦ᵣ v1_old) ** (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x10 ↦ᵣ v10_old) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ j_x8) ** (.x6 ↦ᵣ u_base) **
       (.x10 ↦ᵣ signExtend12 0) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j)) := by
  intro j_x8 sp_m40 u_base cr
  have I0 := ld_spec_gen .x1 .x12 sp v1_old j 3976 base (by nofun)
  have I1 := slli_spec_gen .x5 .x1 v5_old j 3 (base + 4) (by nofun)
  have I2 := addi_spec_gen .x6 .x12 v6_old sp 4056 (base + 8) (by nofun)
  have I3 := sub_spec_gen_rd_eq_rs1 .x6 .x5 sp_m40 j_x8 (base + 12) (by nofun)
  have I4 := addi_x0_spec_gen .x10 v10_old 0 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

/-- Save j to scratch memory. -/
theorem divK_save_j_spec (sp j j_old : Word) (base : Word) :
    let cr := CodeReq.singleton base (.SD .x12 .x1 3976)
    cpsTriple base (base + 4) cr
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) ** (sp + signExtend12 3976 ↦ₘ j_old))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) ** (sp + signExtend12 3976 ↦ₘ j)) := by
  intro cr
  have I0 := sd_spec_gen .x12 .x1 sp j j_old 3976 base
  runBlock I0

/-- Initialize add-back carry to 0. -/
theorem divK_addback_init_spec (v7_old : Word) (base : Word) :
    let cr := CodeReq.singleton base (.ADDI .x7 .x0 0)
    cpsTriple base (base + 4) cr
      ((.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ 0))
      ((.x7 ↦ᵣ signExtend12 0) ** (.x0 ↦ᵣ 0)) := by
  intro cr
  have I0 := addi_x0_spec_gen .x7 v7_old 0 base (by nofun)
  runBlock I0

end EvmAsm.Evm64
