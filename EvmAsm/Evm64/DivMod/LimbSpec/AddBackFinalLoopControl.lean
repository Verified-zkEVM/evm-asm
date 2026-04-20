/-
  EvmAsm.Evm64.DivMod.LimbSpec.AddBackFinalLoopControl

  CPS specs for the two small blocks at the end of each Knuth Algorithm D
  step:
    * `divK_addback_final_spec` — 4 instructions (LD, ADD, SD, ADDI)
      that add the final carry to `u[j+4]` after the add-back corrections
      and decrement `qHat`.
    * `divK_loop_control_spec` — 2-instruction `cpsBranch` (ADDI + BGE)
      that decrements `j` and branches back to the top of the loop while
      `j ≥ 0`.

  Seventeenth chunk of the `LimbSpec.lean` split tracked by issue #312.
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

/-- Add-back finalization after limb corrections. -/
theorem divK_addback_final_spec (uBase carry qHat v5Old uTop : Word)
    (u_off : BitVec 12) (base : Word) :
    let uNew := uTop + carry
    let qHat' := qHat + signExtend12 4095
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x5 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x6 .x5 u_off))
       (CodeReq.singleton (base + 12) (.ADDI .x11 .x11 4095))))
    cpsTriple base (base + 16) cr
      ((.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ carry) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ v5Old) ** (uBase + signExtend12 u_off ↦ₘ uTop))
      ((.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ carry) ** (.x11 ↦ᵣ qHat') **
       (.x5 ↦ᵣ uNew) ** (uBase + signExtend12 u_off ↦ₘ uNew)) := by
  intro uNew qHat' cr
  have I0 := ld_spec_gen .x5 .x6 uBase v5Old uTop u_off base (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1 .x5 .x7 uTop carry (base + 4) (by nofun)
  have I2 := sd_spec_gen .x6 .x5 uBase uNew uTop u_off (base + 8)
  have I3 := addi_spec_gen_same .x11 qHat 4095 (base + 12) (by nofun)
  runBlock I0 I1 I2 I3

/-- Loop control: decrement j and branch back if j >= 0. -/
theorem divK_loop_control_spec (j : Word) (loop_back_off : BitVec 13)
    (base : Word) :
    let j' := j + signExtend12 4095
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADDI .x1 .x1 4095))
       (CodeReq.singleton (base + 4) (.BGE .x1 .x0 loop_back_off))
    cpsBranch base cr
      ((.x1 ↦ᵣ j) ** (.x0 ↦ᵣ 0))
      (base + 4 + signExtend13 loop_back_off)
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      (base + 8)
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) := by
  intro j' cr
  have hbody : cpsTriple base (base + 4) cr
      ((.x1 ↦ᵣ j) ** (.x0 ↦ᵣ 0))
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) := by
    have I0 := addi_spec_gen_same .x1 j 4095 base (by nofun)
    runBlock I0
  have hbge_raw := bge_spec_gen .x1 .x0 loop_back_off j' 0 (base + 4)
  have ha1 : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha1] at hbge_raw
  have hbge : cpsBranch (base + 4) _
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      ((base + 4) + signExtend13 loop_back_off)
        ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      (base + 8)
        ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) :=
    cpsBranch_weaken
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      hbge_raw
  have hbge_ext : cpsBranch (base + 4) cr
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      ((base + 4) + signExtend13 loop_back_off) ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      (base + 8) ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) :=
    fun R hR s hcr hPR hpc =>
      hbge R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show CodeReq.union (CodeReq.singleton base (.ADDI .x1 .x1 4095))
          (CodeReq.singleton (base + 4) (.BGE .x1 .x0 loop_back_off)) (base + 4) = _
        simp only [CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  exact cpsTriple_seq_cpsBranch_same_cr _ _ _ _ _ _ _ _ _ hbody hbge_ext

end EvmAsm.Evm64
