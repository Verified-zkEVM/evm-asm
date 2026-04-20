/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Phase1

  CPS specs for Phase 1 of the `div128` subroutine (the 128/64-bit trial
  division used by the Knuth Algorithm D loop to produce two 32-bit
  quotient halves):
    * `divK_div128_save_split_d_spec` — 6-instruction block (SD, SD,
      SRLI, SLLI, SRLI, SD) that saves the return address and `d` to
      scratch, and splits `d` into `dHi` / `dLo`.
    * `divK_div128_split_ulo_spec` — 4-instruction block (SRLI, SLLI,
      SRLI, SD) that splits `uLo` into `un1` / `un0` and saves `un0`.
    * `divK_div128_step1_init_spec` — 3-instruction block (DIVU, MUL,
      SUB) computing `q1 = uHi / dHi` and `rhat = uHi - q1 * dHi`.

  Twentieth chunk of the `LimbSpec.lean` split tracked by issue #312.
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

/-- div128 Phase 1a: save x2 (return addr) and x10 (d), compute dHi and dLo. -/
theorem divK_div128_save_split_d_spec (sp ret_addr d v1_old v6_old
    ret_mem d_mem dlo_mem : Word) (base : Word) :
    let dHi := d >>> (32 : BitVec 6).toNat
    let dLo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SD .x12 .x2 3968))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x10 3960))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SRLI .x6 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLLI .x1 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SRLI .x1 .x1 32))
       (CodeReq.singleton (base + 20) (.SD .x12 .x1 3952))))))
    cpsTriple base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ v6_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem))
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ dHi) ** (.x1 ↦ᵣ dLo) **
       (sp + signExtend12 3968 ↦ₘ ret_addr) **
       (sp + signExtend12 3960 ↦ₘ d) **
       (sp + signExtend12 3952 ↦ₘ dLo)) := by
  intro dHi dLo cr
  have I0 := sd_spec_gen .x12 .x2 sp ret_addr ret_mem 3968 base
  have I1 := sd_spec_gen .x12 .x10 sp d d_mem 3960 (base + 4)
  have I2 := srli_spec_gen .x6 .x10 v6_old d 32 (base + 8) (by nofun)
  have I3 := slli_spec_gen .x1 .x10 v1_old d 32 (base + 12) (by nofun)
  have I4 := srli_spec_gen_same .x1 (d <<< (32 : BitVec 6).toNat) 32 (base + 16) (by nofun)
  have I5 := sd_spec_gen .x12 .x1 sp dLo dlo_mem 3952 (base + 20)
  runBlock I0 I1 I2 I3 I4 I5

/-- div128 Phase 1b: split uLo into un1 (x11) and un0 (x5), save un0. -/
theorem divK_div128_split_ulo_spec (sp uLo v11_old un0_mem : Word) (base : Word) :
    let un1 := uLo >>> (32 : BitVec 6).toNat
    let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x11 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLLI .x5 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SRLI .x5 .x5 32))
       (CodeReq.singleton (base + 12) (.SD .x12 .x5 3944))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ uLo) ** (.x11 ↦ᵣ v11_old) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ un0) ** (.x11 ↦ᵣ un1) **
       (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro un1 un0 cr
  have I0 := srli_spec_gen .x11 .x5 v11_old uLo 32 base (by nofun)
  have I1 := slli_spec_gen_same .x5 uLo 32 (base + 4) (by nofun)
  have I2 := srli_spec_gen_same .x5 (uLo <<< (32 : BitVec 6).toNat) 32 (base + 8) (by nofun)
  have I3 := sd_spec_gen .x12 .x5 sp un0 un0_mem 3944 (base + 12)
  runBlock I0 I1 I2 I3

/-- div128 Step 1: q1 = DIVU(uHi, dHi), rhat = uHi - q1 * dHi. -/
theorem divK_div128_step1_init_spec (uHi dHi v5_old v10_old : Word) (base : Word) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x10 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x6))
       (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5)))
    cpsTriple base (base + 12) cr
      ((.x7 ↦ᵣ uHi) ** (.x6 ↦ᵣ dHi) **
       (.x10 ↦ᵣ v10_old) ** (.x5 ↦ᵣ v5_old))
      ((.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) **
       (.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q1 * dHi)) := by
  intro q1 rhat cr
  have I0 := divu_spec_gen .x10 .x7 .x6 v10_old uHi dHi base (by nofun)
  have I1 := mul_spec_gen .x5 .x10 .x6 v5_old q1 dHi (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 uHi (q1 * dHi) (base + 8) (by nofun)
  runBlock I0 I1 I2

end EvmAsm.Evm64
