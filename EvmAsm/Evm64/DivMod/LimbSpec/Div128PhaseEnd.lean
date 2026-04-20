/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128PhaseEnd

  Full compositions for the first and last straight-line phases of the
  `div128` trial-division subroutine:
    * `divK_div128_phase1_spec` — Instrs [0]-[9], 10 instructions:
      SD+SD+SRLI+SLLI+SRLI+SD (save_split_d) followed by
      SRLI+SLLI+SRLI+SD (split_ulo). Saves the return address and `d`,
      splits `d` into `dHi`/`dLo`, splits `uLo` into `un1`/`un0`.
    * `divK_div128_end_spec` — Instrs [45]-[48], 4 instructions:
      SLLI+OR (combine_q → `q = q1<<32 | q0`) followed by LD+JALR
      (restore return addr and jump back). Exits at `ret_addr`.

  Twenty-seventh chunk of the `LimbSpec.lean` split tracked by issue #312.
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

/-- div128 Phase 1: save return addr/d, split d and uLo. Instrs [0]-[9].
    Input: x12=sp, x2=ret_addr, x10=d, x5=uLo, x7=uHi.
    Output: x6=dHi, x11=un1, x5=un0 (saved), x7=uHi (unchanged). -/
theorem divK_div128_phase1_spec
    (sp ret_addr d uLo uHi v1_old v6_old v11_old
     ret_mem d_mem dlo_mem un0_mem : Word) (base : Word) :
    let dHi := d >>> (32 : BitVec 6).toNat
    let dLo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let un1 := uLo >>> (32 : BitVec 6).toNat
    let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SD .x12 .x2 3968))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x10 3960))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SRLI .x6 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLLI .x1 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SRLI .x1 .x1 32))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x1 3952))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SRLI .x11 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SLLI .x5 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SRLI .x5 .x5 32))
       (CodeReq.singleton (base + 36) (.SD .x12 .x5 3944))))))))))
    cpsTriple base (base + 40) cr
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ v6_old) ** (.x1 ↦ᵣ v1_old) ** (.x5 ↦ᵣ uLo) **
       (.x11 ↦ᵣ v11_old) ** (.x7 ↦ᵣ uHi) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ dHi) ** (.x1 ↦ᵣ dLo) ** (.x5 ↦ᵣ un0) **
       (.x11 ↦ᵣ un1) ** (.x7 ↦ᵣ uHi) **
       (sp + signExtend12 3968 ↦ₘ ret_addr) **
       (sp + signExtend12 3960 ↦ₘ d) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro dHi dLo un1 un0 cr
  have I0 := sd_spec_gen .x12 .x2 sp ret_addr ret_mem 3968 base
  have I1 := sd_spec_gen .x12 .x10 sp d d_mem 3960 (base + 4)
  have I2 := srli_spec_gen .x6 .x10 v6_old d 32 (base + 8) (by nofun)
  have I3 := slli_spec_gen .x1 .x10 v1_old d 32 (base + 12) (by nofun)
  have I4 := srli_spec_gen_same .x1 (d <<< (32 : BitVec 6).toNat) 32 (base + 16) (by nofun)
  have I5 := sd_spec_gen .x12 .x1 sp dLo dlo_mem 3952 (base + 20)
  have I6 := srli_spec_gen .x11 .x5 v11_old uLo 32 (base + 24) (by nofun)
  have I7 := slli_spec_gen_same .x5 uLo 32 (base + 28) (by nofun)
  have I8 := srli_spec_gen_same .x5 (uLo <<< (32 : BitVec 6).toNat) 32 (base + 32) (by nofun)
  have I9 := sd_spec_gen .x12 .x5 sp un0 un0_mem 3944 (base + 36)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9

/-- div128 end phase: combine q1,q0 into q, restore return addr, return.
    Instrs [45]-[48]. Exit to ret_addr. -/
theorem divK_div128_end_spec
    (sp q1 q0 v2_old v11_old ret_addr : Word) (base : Word)
    (halign : (ret_addr + signExtend12 0) &&& ~~~1 = ret_addr) :
    let q1_hi := q1 <<< (32 : BitVec 6).toNat
    let q := q1_hi ||| q0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x11 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.OR .x11 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x2 .x12 3968))
       (CodeReq.singleton (base + 12) (.JALR .x0 .x2 0))))
    cpsTriple base ret_addr cr
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ v11_old) **
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2_old) ** (sp + signExtend12 3968 ↦ₘ ret_addr))
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ q) **
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr)) := by
  intro q1_hi q cr
  have I0 := slli_spec_gen .x11 .x10 v11_old q1 32 base (by nofun)
  have I1 := or_spec_gen_rd_eq_rs1 .x11 .x5 q1_hi q0 (base + 4) (by nofun)
  have I2 := ld_spec_gen .x2 .x12 sp v2_old ret_addr 3968 (base + 8) (by nofun)
  have I3 := jalr_x0_spec_gen .x2 ret_addr 0 (base + 12)
  rw [halign] at I3
  runBlock I0 I1 I2 I3

end EvmAsm.Evm64
