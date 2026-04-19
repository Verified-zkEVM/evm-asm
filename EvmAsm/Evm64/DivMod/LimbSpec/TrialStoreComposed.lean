/-
  EvmAsm.Evm64.DivMod.LimbSpec.TrialStoreComposed

  Two straight-line composition specs for the Knuth loop body:
    * `divK_trial_load_spec` — 12-instruction composition (trial_load_u
      + trial_load_vtop) that fetches `u_hi`, `u_lo`, and `v_top` from
      memory in preparation for the trial-quotient estimation.
    * `divK_store_qj_spec` — 4-instruction composition (store_qj_addr
      + store_qj_write) that computes `qAddr = sp + 4088 - 8*j` and
      stores `q_hat` there.

  Twenty-eighth chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees both
  specs.
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

/-- Trial quotient load: fetch u_hi, u_lo, v_top from memory.
    Instrs [1]-[12] of loop body.
    Output: x7 = u_hi, x5 = u_lo, x10 = v_top, x6 = vtopBase. -/
theorem divK_trial_load_spec
    (sp j n v5_old v6_old v7_old v10_old u_hi u_lo v_top : Word)
    (base : Word) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x7 .x1 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x7 .x7 3))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADDI .x5 .x12 4056))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x5 0))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x6 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 32) (.ADDI .x6 .x6 4095))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x6 .x6 3))
      (CodeReq.union (CodeReq.singleton (base + 40) (.ADD .x6 .x12 .x6))
       (CodeReq.singleton (base + 44) (.LD .x10 .x6 32))))))))))))
    cpsTriple base (base + 48) cr
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ u_hi) ** ((uAddr + 8) ↦ₘ u_lo) **
       (vtopBase + signExtend12 32 ↦ₘ v_top))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ u_hi) ** ((uAddr + 8) ↦ₘ u_lo) **
       (vtopBase + signExtend12 32 ↦ₘ v_top)) := by
  intro uAddr vtopBase cr
  let jpn := j + n
  let jpn_x8 := jpn <<< (3 : BitVec 6).toNat
  let u0_base := sp + signExtend12 4056
  have haddr0 : uAddr + signExtend12 (0 : BitVec 12) = uAddr := by rw [se12_0]; bv_omega
  have I0 := ld_spec_gen .x5 .x12 sp v5_old n 3984 base (by nofun)
  have I1 := add_spec_gen .x7 .x1 .x5 j n v7_old (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x7 jpn 3 (base + 8) (by nofun)
  have I3 := addi_spec_gen .x5 .x12 n sp 4056 (base + 12) (by nofun)
  have I4 := sub_spec_gen_rd_eq_rs1 .x5 .x7 u0_base jpn_x8 (base + 16) (by nofun)
  have I5 := ld_spec_gen .x7 .x5 uAddr jpn_x8 u_hi 0 (base + 20) (by nofun)
  rw [haddr0] at I5
  have I6 := ld_spec_gen_same .x5 uAddr u_lo 8 (base + 24) (by nofun)
  let nm1 := n + signExtend12 4095
  let nm1_x8 := nm1 <<< (3 : BitVec 6).toNat
  have I7 := ld_spec_gen .x6 .x12 sp v6_old n 3984 (base + 28) (by nofun)
  have I8 := addi_spec_gen_same .x6 n 4095 (base + 32) (by nofun)
  have I9 := slli_spec_gen_same .x6 nm1 3 (base + 36) (by nofun)
  have I10 := add_spec_gen_rd_eq_rs2 .x6 .x12 sp nm1_x8 (base + 40) (by nofun)
  have I11 := ld_spec_gen .x10 .x6 vtopBase v10_old v_top 32 (base + 44) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11

/-- Store q[j]: compute address and store q_hat. 4 instructions.
    qAddr = sp + 4088 - j*8. -/
theorem divK_store_qj_spec (sp j q_hat v5_old v7_old q_old : Word)
    (base : Word) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x7 .x12 4088))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
       (CodeReq.singleton (base + 12) (.SD .x7 .x11 0))))
    cpsTriple base (base + 16) cr
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (qAddr ↦ₘ q_old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ qAddr) **
       (qAddr ↦ₘ q_hat)) := by
  intro j_x8 qAddr cr
  have I0 := slli_spec_gen .x5 .x1 v5_old j 3 base (by nofun)
  have I1 := addi_spec_gen .x7 .x12 v7_old sp 4088 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 (sp + signExtend12 4088) j_x8 (base + 8) (by nofun)
  have haddr : qAddr + signExtend12 (0 : BitVec 12) = qAddr := by rw [se12_0]; bv_omega
  have I3 := sd_spec_gen .x7 .x11 qAddr q_hat q_old 0 (base + 12)
  rw [haddr] at I3
  runBlock I0 I1 I2 I3

end EvmAsm.Evm64
