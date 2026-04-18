/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128UnProdCheck

  CPS specs for the middle of the `div128` trial-division subroutine —
  the un21 computation, the product-check body shared between step 1
  and step 2, and the two small "q-- and rhat += d_hi" correction
  blocks:
    * `divK_div128_compute_un21_spec` — 5-instruction LD/SLLI/OR/MUL/SUB
      computing `un21 = rhat*2^32 + un1 - q1*d_lo`.
    * `divK_div128_prodcheck_body_spec` — 4-instruction LD/MUL/SLLI/OR
      producing `q*d_lo` (x5) and `rhat*2^32 + un1` (x1) for BLTU.
    * `divK_div128_correct_q1_spec` — 2-instruction q1-- / rhat += d_hi
      correction on x10/x7.
    * `divK_div128_correct_q0_spec` — same shape but on x5/x11 for q0.

  Twenty-first chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees all
  four specs.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- div128 un21 = rhat*2^32 + un1 - q1*d_lo.
    Loads d_lo from scratch memory. -/
theorem divK_div128_compute_un21_spec (sp q1 rhat un1 v1_old v5_old dlo_mem : Word) (base : Word) :
    let rhat_hi := rhat <<< (32 : BitVec 6).toNat
    let rhat_un1 := rhat_hi ||| un1
    let q1_dlo := q1 * dlo_mem
    let un21 := rhat_un1 - q1_dlo
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLLI .x5 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x5 .x5 .x11))
      (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x1 .x10 .x1))
       (CodeReq.singleton (base + 16) (.SUB .x7 .x5 .x1)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) **
       (.x11 ↦ᵣ un1) ** (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ un21) **
       (.x11 ↦ᵣ un1) ** (.x5 ↦ᵣ rhat_un1) ** (.x1 ↦ᵣ q1_dlo) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem)) := by
  intro rhat_hi rhat_un1 q1_dlo un21 cr
  have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo_mem 3952 base (by nofun)
  have I1 := slli_spec_gen .x5 .x7 v5_old rhat 32 (base + 4) (by nofun)
  have I2 := or_spec_gen_rd_eq_rs1 .x5 .x11 rhat_hi un1 (base + 8) (by nofun)
  have I3 := mul_spec_gen_rd_eq_rs2 .x1 .x10 q1 dlo_mem (base + 12) (by nofun)
  have I4 := sub_spec_gen .x7 .x5 .x1 rhat_un1 q1_dlo rhat (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

/-- div128 product check body: compute q*d_lo and rhat*2^32+un1 for comparison. -/
theorem divK_div128_prodcheck_body_spec (sp q rhat un1 v1_old v5_old dlo : Word) (base : Word) :
    let q_dlo := q * dlo
    let rhat_hi := rhat <<< (32 : BitVec 6).toNat
    let rhat_un1 := rhat_hi ||| un1
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x7 32))
       (CodeReq.singleton (base + 12) (.OR .x1 .x1 .x11))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ q_dlo) ** (.x1 ↦ᵣ rhat_un1) ** (sp + signExtend12 3952 ↦ₘ dlo)) := by
  intro q_dlo rhat_hi rhat_un1 cr
  have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo 3952 base (by nofun)
  have I1 := mul_spec_gen .x5 .x10 .x1 v5_old q dlo (base + 4) (by nofun)
  have I2 := slli_spec_gen .x1 .x7 dlo rhat 32 (base + 8) (by nofun)
  have I3 := or_spec_gen_rd_eq_rs1 .x1 .x11 (rhat <<< (32 : BitVec 6).toNat) un1 (base + 12) (by nofun)
  runBlock I0 I1 I2 I3

/-- div128 correction: q-- and rhat += d_hi. Generic for q1 (x10) or q0 (x5). -/
theorem divK_div128_correct_q1_spec (q rhat d_hi : Word) (base : Word) :
    let q' := q + signExtend12 4095
    let rhat' := rhat + d_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 4) (.ADD .x7 .x7 .x6))
    cpsTriple base (base + 8) cr
      ((.x10 ↦ᵣ q) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))
      ((.x10 ↦ᵣ q') ** (.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ d_hi)) := by
  intro q' rhat' cr
  have I0 := addi_spec_gen_same .x10 q 4095 base (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1 .x7 .x6 rhat d_hi (base + 4) (by nofun)
  runBlock I0 I1

/-- div128 correction for q0: q0-- and rhat2 += d_hi. -/
theorem divK_div128_correct_q0_spec (q0 rhat2 d_hi : Word) (base : Word) :
    let q0' := q0 + signExtend12 4095
    let rhat2' := rhat2 + d_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADDI .x5 .x5 4095))
       (CodeReq.singleton (base + 4) (.ADD .x11 .x11 .x6))
    cpsTriple base (base + 8) cr
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi))
      ((.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2') ** (.x6 ↦ᵣ d_hi)) := by
  intro q0' rhat2' cr
  have I0 := addi_spec_gen_same .x5 q0 4095 base (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1 .x11 .x6 rhat2 d_hi (base + 4) (by nofun)
  runBlock I0 I1

end EvmAsm.Evm64
