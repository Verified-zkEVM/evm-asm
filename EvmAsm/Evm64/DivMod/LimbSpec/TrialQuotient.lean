/-
  EvmAsm.Evm64.DivMod.LimbSpec.TrialQuotient

  CPS specs for the blocks that set up the trial-quotient estimation in
  the Knuth Algorithm D loop:
    * `divK_correction_branch_spec` — single-BEQ `cpsBranch` that skips
      the add-back correction path when the borrow from mul-sub is zero.
    * `divK_trial_load_u_spec` — 7-instruction block loading the high
      two limbs of `u[j..]` into x7/x5 at `uAddr = sp + 4056 - (j+n)*8`.
    * `divK_trial_load_vtop_spec` — 5-instruction block loading
      `vTop = b[n-1]` and leaving its address in x6.
    * `divK_trial_max_spec` — 2-instruction MAX path (ADDI x11, JAL)
      that clamps qHat to MAX64 and jumps past the div128 call.

  Nineteenth chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees all
  four specs.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.AddrNorm
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se21_8)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Correction condition: branch if borrow (x7) is zero. -/
theorem divK_correction_branch_spec (borrow : Word) (skip_off : BitVec 13) (base : Word) :
    let cr := CodeReq.singleton base (.BEQ .x7 .x0 skip_off)
    cpsBranch base cr
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0))
      (base + signExtend13 skip_off)
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0))
      (base + 4)
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0)) := by
  intro cr
  have hbeq := beq_spec_gen .x7 .x0 skip_off borrow 0 base
  exact cpsBranch_weaken
    (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    hbeq

/-- Load uHi = u[j+n] and uLo = u[j+n-1] for trial quotient estimation.
    uAddr = sp + signExtend12 4056 - (j + n) <<< 3.
    uHi = mem[uAddr], uLo = mem[uAddr + 8]. -/
theorem divK_trial_load_u_spec (sp j n v5Old v7Old uHi uLo : Word)
    (base : Word) :
    let jpn := j + n
    let jpnX8 := jpn <<< (3 : BitVec 6).toNat
    let u0_base := sp + signExtend12 4056
    let uAddr := u0_base - jpnX8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x7 .x1 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x7 .x7 3))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADDI .x5 .x12 4056))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x5 0))
       (CodeReq.singleton (base + 24) (.LD .x5 .x5 8)))))))
    cpsTriple base (base + 28) cr
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo)) := by
  intro jpn jpnX8 u0_base uAddr cr
  have haddr0 : uAddr + signExtend12 (0 : BitVec 12) = uAddr := by rv64_addr
  have I0 := ld_spec_gen .x5 .x12 sp v5Old n 3984 base (by nofun)
  have I1 := add_spec_gen .x7 .x1 .x5 j n v7Old (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x7 jpn 3 (base + 8) (by nofun)
  have I3 := addi_spec_gen .x5 .x12 n sp 4056 (base + 12) (by nofun)
  have I4 := sub_spec_gen_rd_eq_rs1 .x5 .x7 u0_base jpnX8 (base + 16) (by nofun)
  have I5 := ld_spec_gen .x7 .x5 uAddr jpnX8 uHi 0 (base + 20) (by nofun)
  rw [haddr0] at I5
  have I6 := ld_spec_gen_same .x5 uAddr uLo 8 (base + 24) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5 I6

/-- Load vTop = b[n-1] for trial quotient estimation.
    vtop_addr = sp + (n + signExtend12 4095) <<< 3.
    vTop = mem[vtop_addr + 32]. -/
theorem divK_trial_load_vtop_spec (sp n v6Old v10Old vTop : Word)
    (base : Word) :
    let nm1 := n + signExtend12 4095
    let nm1X8 := nm1 <<< (3 : BitVec 6).toNat
    let vtopBase := sp + nm1X8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x6 .x6 4095))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x6 .x6 3))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x6 .x12 .x6))
       (CodeReq.singleton (base + 16) (.LD .x10 .x6 32)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x10 ↦ᵣ v10Old) **
       (sp + signExtend12 3984 ↦ₘ n) ** (vtopBase + signExtend12 32 ↦ₘ vTop))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ vtopBase) ** (.x10 ↦ᵣ vTop) **
       (sp + signExtend12 3984 ↦ₘ n) ** (vtopBase + signExtend12 32 ↦ₘ vTop)) := by
  intro nm1 nm1X8 vtopBase cr
  have I0 := ld_spec_gen .x6 .x12 sp v6Old n 3984 base (by nofun)
  have I1 := addi_spec_gen_same .x6 n 4095 (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x6 nm1 3 (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs2 .x6 .x12 sp nm1X8 (base + 12) (by nofun)
  have I4 := ld_spec_gen .x10 .x6 vtopBase v10Old vTop 32 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

/-- Trial quotient MAX path: set qHat = MAX64, jump over div128 call. -/
theorem divK_trial_max_spec (v11Old : Word) (base : Word) :
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADDI .x11 .x0 4095))
       (CodeReq.singleton (base + 4) (.JAL .x0 8))
    cpsTriple base (base + 12) cr
      ((.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ 0))
      ((.x11 ↦ᵣ signExtend12 4095) ** (.x0 ↦ᵣ 0)) := by
  intro cr
  have I0 := addi_x0_spec_gen .x11 v11Old 4095 base (by nofun)
  have I1 := jal_x0_spec_gen 8 (base + 4)
  rw [se21_8] at I1
  have ha : (base + 4 : Word) + 8 = base + 12 := by bv_addr
  rw [ha] at I1
  runBlock I0 I1

end EvmAsm.Evm64
