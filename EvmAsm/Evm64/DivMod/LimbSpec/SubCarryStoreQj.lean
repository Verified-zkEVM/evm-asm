/-
  EvmAsm.Evm64.DivMod.LimbSpec.SubCarryStoreQj

  CPS specs for two small, related blocks that run right after the
  mul-sub inner loop in the Knuth Algorithm D step:
    * `divK_sub_carry_spec` — 4 instructions (LD, SLTU, SUB, SD) that
      subtract the final carry from `u[j+4]` and record the resulting
      borrow.
    * `divK_store_qj_addr_spec` — 3 instructions (SLLI, ADDI, SUB) that
      compute `qAddr = sp + 4088 - 8*j` into x7.
    * `divK_store_qj_write_spec` — 1-instruction SD that actually
      writes `qHat` at `qAddr`.

  Sixteenth chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees all
  three specs.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.AddrNorm
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.DivMod.AddrNorm (se12_0)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Subtract carry from u[j+4].
    4 instructions: LD, SLTU, SUB, SD. Produces borrow (x7). -/
theorem divK_sub_carry_spec (uBase carryIn v5Old v7Old uTop : Word)
    (u_off : BitVec 12) (base : Word) :
    let borrow := if BitVec.ult uTop carryIn then (1 : Word) else 0
    let uNew := uTop - carryIn
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x7 .x5 .x10))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x5 .x5 .x10))
       (CodeReq.singleton (base + 12) (.SD .x6 .x5 u_off))))
    cpsTriple base (base + 16) cr
      ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ carryIn) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) **
       ((uBase + signExtend12 u_off) ↦ₘ uTop))
      ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ carryIn) **
       (.x5 ↦ᵣ uNew) ** (.x7 ↦ᵣ borrow) **
       ((uBase + signExtend12 u_off) ↦ₘ uNew)) := by
  intro borrow uNew cr
  have I0 := ld_spec_gen .x5 .x6 uBase v5Old uTop u_off base (by nofun)
  have I1 := sltu_spec_gen .x7 .x5 .x10 v7Old uTop carryIn (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x5 .x10 uTop carryIn (base + 8) (by nofun)
  have I3 := sd_spec_gen .x6 .x5 uBase uNew uTop u_off (base + 12)
  runBlock I0 I1 I2 I3

/-- Store q[j]: compute &q[j] = sp+4088 - j*8, store qHat.
    First 3 instructions compute qAddr. Then SD stores. Split into 3+1. -/
theorem divK_store_qj_addr_spec (sp j v5Old v7Old : Word)
    (base : Word) :
    let jX8 := j <<< (3 : BitVec 6).toNat
    let sp_m8 := sp + signExtend12 4088
    let qAddr := sp_m8 - jX8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x7 .x12 4088))
       (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5)))
    cpsTriple base (base + 12) cr
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ jX8) ** (.x7 ↦ᵣ qAddr)) := by
  intro jX8 sp_m8 qAddr cr
  have I0 := slli_spec_gen .x5 .x1 v5Old j 3 base (by nofun)
  have I1 := addi_spec_gen .x7 .x12 v7Old sp 4088 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 sp_m8 jX8 (base + 8) (by nofun)
  runBlock I0 I1 I2

/-- Store q[j]: SD qHat at qAddr. 1 instruction. -/
theorem divK_store_qj_write_spec (qAddr qHat qOld : Word) (base : Word) :
    let cr := CodeReq.singleton base (.SD .x7 .x11 0)
    cpsTriple base (base + 4) cr
      ((.x7 ↦ᵣ qAddr) ** (.x11 ↦ᵣ qHat) ** (qAddr ↦ₘ qOld))
      ((.x7 ↦ᵣ qAddr) ** (.x11 ↦ᵣ qHat) ** (qAddr ↦ₘ qHat)) := by
  intro cr
  have haddr : qAddr + signExtend12 (0 : BitVec 12) = qAddr := by rw [se12_0]; bv_omega
  have I0 := sd_spec_gen .x7 .x11 qAddr qHat qOld 0 base
  rw [haddr] at I0
  runBlock I0

end EvmAsm.Evm64
