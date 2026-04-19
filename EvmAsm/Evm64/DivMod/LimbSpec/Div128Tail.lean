/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Tail

  CPS specs for the tail section of the `div128` trial-division
  subroutine — the SRLI clamp tests, step-2 init, product-check-2 body,
  single-ADDI correction, q1<<32|q0 combine, and LD+JALR return:
    * `divK_div128_clamp_test_q1_spec` / `divK_div128_clamp_test_q0_spec`
      — single SRLI writing `hi = q >>> 32` used by the BEQ in the
      clamp-merged wrappers.
    * `divK_div128_step2_init_spec` — 3-instr DIVU/MUL/SUB computing
      `q0 = un21 / d_hi` and `rhat2 = un21 - q0 * d_hi`.
    * `divK_div128_prodcheck2_body_spec` — 5-instr LD/MUL/SLLI/LD/OR
      producing `q0*d_lo` and `rhat2*2^32 + un0` for the BLTU.
    * `divK_div128_correct_q0_single_spec` — single ADDI that just
      decrements q0 after the product-check-2 BLTU.
    * `divK_div128_combine_q_spec` — 2-instr SLLI/OR producing
      `q = q1<<32 | q0`.
    * `divK_div128_restore_return_spec` — 2-instr LD/JALR restoring the
      saved return address and jumping back.

  Twenty-second chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees all
  seven specs.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- div128 q1 clamp test: x5 = q1 >>> 32 (nonzero iff q1 >= 2^32). -/
theorem divK_div128_clamp_test_q1_spec (q1 v5_old : Word) (base : Word) :
    let hi := q1 >>> (32 : BitVec 6).toNat
    let cr := CodeReq.singleton base (.SRLI .x5 .x10 32)
    cpsTriple base (base + 4) cr
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ v5_old))
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ hi)) := by
  intro hi cr
  have I0 := srli_spec_gen .x5 .x10 v5_old q1 32 base (by nofun)
  runBlock I0

/-- div128 q0 clamp test: x1 = q0 >>> 32. -/
theorem divK_div128_clamp_test_q0_spec (q0 v1_old : Word) (base : Word) :
    let hi := q0 >>> (32 : BitVec 6).toNat
    let cr := CodeReq.singleton base (.SRLI .x1 .x5 32)
    cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ q0) ** (.x1 ↦ᵣ v1_old))
      ((.x5 ↦ᵣ q0) ** (.x1 ↦ᵣ hi)) := by
  intro hi cr
  have I0 := srli_spec_gen .x1 .x5 v1_old q0 32 base (by nofun)
  runBlock I0

/-- div128 Step 2: q0 = DIVU(un21, d_hi), rhat2 = un21 - q0 * d_hi. -/
theorem divK_div128_step2_init_spec (un21 d_hi v1_old v5_old v11_old : Word) (base : Word) :
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
       (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1)))
    cpsTriple base (base + 12) cr
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (.x11 ↦ᵣ v11_old))
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ q0) ** (.x1 ↦ᵣ q0 * d_hi) ** (.x11 ↦ᵣ rhat2)) := by
  intro q0 rhat2 cr
  have I0 := divu_spec_gen .x5 .x7 .x6 v5_old un21 d_hi base (by nofun)
  have I1 := mul_spec_gen .x1 .x5 .x6 v1_old q0 d_hi (base + 4) (by nofun)
  have I2 := sub_spec_gen .x11 .x7 .x1 un21 (q0 * d_hi) v11_old (base + 8) (by nofun)
  runBlock I0 I1 I2

/-- div128 product check 2: compute q0*d_lo and rhat2*2^32+un0 for comparison. -/
theorem divK_div128_prodcheck2_body_spec (sp q0 rhat2 v1_old v7_old dlo un0 : Word)
    (base : Word) :
    let q0_dlo := q0 * dlo
    let rhat2_hi := rhat2 <<< (32 : BitVec 6).toNat
    let rhat2_un0 := rhat2_hi ||| un0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.LD .x11 .x12 3944))
       (CodeReq.singleton (base + 16) (.OR .x1 .x1 .x11)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
       (.x7 ↦ᵣ v7_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
       (.x7 ↦ᵣ q0_dlo) ** (.x1 ↦ᵣ rhat2_un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0_dlo rhat2_hi rhat2_un0 cr
  have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo 3952 base (by nofun)
  have I1 := mul_spec_gen .x7 .x5 .x1 v7_old q0 dlo (base + 4) (by nofun)
  have I2 := slli_spec_gen .x1 .x11 dlo rhat2 32 (base + 8) (by nofun)
  have I3 := ld_spec_gen .x11 .x12 sp rhat2 un0 3944 (base + 12) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1 .x1 .x11 rhat2_hi un0 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

/-- div128 product check 2 correction: q0--. -/
theorem divK_div128_correct_q0_single_spec (q0 : Word) (base : Word) :
    let q0' := q0 + signExtend12 4095
    let cr := CodeReq.singleton base (.ADDI .x5 .x5 4095)
    cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ q0))
      ((.x5 ↦ᵣ q0')) := by
  intro q0' cr
  have I0 := addi_spec_gen_same .x5 q0 4095 base (by nofun)
  runBlock I0

/-- div128 combine: x11 = q1<<32 | q0. -/
theorem divK_div128_combine_q_spec (q1 q0 v11_old : Word) (base : Word) :
    let q1_hi := q1 <<< (32 : BitVec 6).toNat
    let q := q1_hi ||| q0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x11 .x10 32))
       (CodeReq.singleton (base + 4) (.OR .x11 .x11 .x5))
    cpsTriple base (base + 8) cr
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ v11_old))
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ q)) := by
  intro q1_hi q cr
  have I0 := slli_spec_gen .x11 .x10 v11_old q1 32 base (by nofun)
  have I1 := or_spec_gen_rd_eq_rs1 .x11 .x5 q1_hi q0 (base + 4) (by nofun)
  runBlock I0 I1

/-- div128 restore and return: load return addr, JALR x0 x2 0. -/
theorem divK_div128_restore_return_spec (sp v2_old ret_addr : Word) (base : Word)
    (halign : (ret_addr + signExtend12 0) &&& ~~~1 = ret_addr) :
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x2 .x12 3968))
       (CodeReq.singleton (base + 4) (.JALR .x0 .x2 0))
    cpsTriple base ret_addr cr
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2_old) ** (sp + signExtend12 3968 ↦ₘ ret_addr))
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr)) := by
  intro cr
  have I0 := ld_spec_gen .x2 .x12 sp v2_old ret_addr 3968 base (by nofun)
  have I1 := jalr_x0_spec_gen .x2 ret_addr 0 (base + 4)
  rw [halign] at I1
  runBlock I0 I1

end EvmAsm.Evm64
