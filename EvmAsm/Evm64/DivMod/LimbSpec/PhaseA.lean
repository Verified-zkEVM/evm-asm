/-
  EvmAsm.Evm64.DivMod.LimbSpec.PhaseA

  CPS specs for the Knuth Algorithm D "phase A" — OR-reducing the 4
  limbs of the divisor `b` and branching to the zero path if the
  reduction is zero:
    * `divK_phaseA_code` — `CodeReq.ofProg base (divK_phaseA 1020)`.
    * `divK_phaseA_body_spec` — 7-instruction straight-line body
      (LD, LD, OR, LD, OR, LD, OR) producing `x5 = b0 ||| b1 ||| b2 ||| b3`.
    * `divK_phaseA_spec` — full `cpsBranch` wrapping the body plus the
      BEQ at `base + 28` that branches to the zero path when the OR-reduce
      is zero.

  Seventh chunk of the `LimbSpec.lean` split tracked by issue #312. The
  consumer surface is unchanged: `LimbSpec.lean` re-exports this file so
  every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees both
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

abbrev divK_phaseA_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseA 1020)

/-- Phase A body: load and OR-reduce the 4 limbs of b.
    Produces x5 = b0 ||| b1 ||| b2 ||| b3.
    The BEQ instruction at base+28 and x0 are preserved for branch composition. -/
theorem divK_phaseA_body_spec (sp : Word) (base : Word)
    (b0 b1 b2 b3 v5 v10 : Word) :
    let cr := divK_phaseA_code base
    cpsTriple base (base + 28) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 b0 32 base (by nofun)
  have I1 := ld_spec_gen .x10 .x12 sp v10 b1 40 (base + 4) (by nofun)
  have I2 := or_spec_gen_rd_eq_rs1 .x5 .x10 b0 b1 (base + 8) (by nofun)
  have I3 := ld_spec_gen .x10 .x12 sp b1 b2 48 (base + 12) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x10 (b0 ||| b1) b2 (base + 16) (by nofun)
  have I5 := ld_spec_gen .x10 .x12 sp b2 b3 56 (base + 20) (by nofun)
  have I6 := or_spec_gen_rd_eq_rs1 .x5 .x10 (b0 ||| b1 ||| b2) b3 (base + 24) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5 I6

/-- Phase A: OR-reduce b then BEQ to zero path. -/
theorem divK_phaseA_spec (sp : Word) (base : Word)
    (b0 b1 b2 b3 v5 v10 : Word) :
    let bor := b0 ||| b1 ||| b2 ||| b3
    let cr := divK_phaseA_code base
    let post :=
      (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ bor) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
      ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)
    cpsBranch base cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      -- Taken: bor = 0
      ((base + 28) + signExtend13 1020) post
      -- Not taken: bor ≠ 0
      (base + 32) post := by
  intro bor cr post
  -- 1. Body: 7 straight-line instructions
  have hbody := divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10
  -- 2. BEQ: branch at base + 28, drop pure facts
  have hbeq_raw := beq_spec_gen .x5 .x0 1020 bor (0 : Word) (base + 28)
  have ha1 : (base + 28 : Word) + 4 = base + 32 := by bv_addr
  rw [ha1] at hbeq_raw
  have hbeq := cpsBranch_weaken
    (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    hbeq_raw
  -- 3. Frame BEQ with remaining registers and memory
  have hbeq_framed := cpsBranch_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- 4. Extend BEQ branch to full cr (singleton ⊆ full code)
  have hbeq_ext := cpsBranch_extend_code (cr' := cr) (fun a i h => by
    simp only [CodeReq.singleton] at h
    split at h <;> simp_all only [Option.some.injEq, beq_iff_eq, reduceCtorEq]
    -- a = base + 28, i = .BEQ .x5 .x0 1020
    subst_vars
    show divK_phaseA_code base (base + 28) = _
    exact CodeReq.ofProg_lookup base (divK_phaseA 1020) 7
      (by decide) (by decide)
    ) hbeq_framed
  -- 5. Compose body → BEQ with permutation (same CR) and clean up postconditions
  exact cpsBranch_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (cpsTriple_seq_cpsBranch_perm_same_cr
      (fun h hp => by xperm_hyp hp) hbody hbeq_ext)

end EvmAsm.Evm64
