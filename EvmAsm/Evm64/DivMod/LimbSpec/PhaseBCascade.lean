/-
  EvmAsm.Evm64.DivMod.LimbSpec.PhaseBCascade

  CPS spec for a single step of the Knuth Algorithm D phase-B cascade —
  the repeating `ADDI x5 = n_val; BNE rx x0 → end` pattern that computes
  `n` (the index of the highest non-zero limb of the divisor):
    * `divK_phaseB_cascade_step_code` — a 2-instruction `CodeReq.union`
      of the ADDI and the BNE.
    * `divK_phaseB_cascade_step_spec` — full `cpsBranch` spec: in either
      branch `x5 = n_val`; the taken branch jumps when `rx ≠ 0`.

  Eleventh chunk of the `LimbSpec.lean` split tracked by issue #312. The
  consumer surface is unchanged: `LimbSpec.lean` re-exports this file so
  every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the
  spec.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

abbrev divK_phaseB_cascade_step_code (n_val : BitVec 12) (rx : Reg) (bne_off : BitVec 13)
    (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x5 .x0 n_val))
   (CodeReq.singleton (base + 4) (.BNE rx .x0 bne_off))

/-- Single cascade step: load n_val into x5, then BNE on rx vs x0.
    Taken: rx ≠ 0 (limb is nonzero), branch to target with x5 = n_val.
    Not taken: rx = 0, fall through with x5 = n_val. -/
theorem divK_phaseB_cascade_step_spec (n_val : BitVec 12) (rx : Reg) (check v5 : Word)
    (bne_off : BitVec 13) (base : Word) :
    let n := (0 : Word) + signExtend12 n_val
    let cr := divK_phaseB_cascade_step_code n_val rx bne_off base
    let post :=
      (.x5 ↦ᵣ n) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check)
    cpsBranch base cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check))
      -- Taken: check ≠ 0
      ((base + 4) + signExtend13 bne_off) post
      -- Not taken: check = 0
      (base + 8) post := by
  intro n cr post
  -- 1. ADDI body
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check))
      ((.x5 ↦ᵣ n) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check)) := by
    have I0 := addi_spec_gen .x5 .x0 v5 (0 : Word) n_val base (by nofun)
    runBlock I0
  -- 2. BNE at base + 4, drop pure facts
  have hbne_raw := bne_spec_gen rx .x0 bne_off check (0 : Word) (base + 4)
  have ha1 : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha1] at hbne_raw
  have hbne : cpsBranch (base + 4) _
      ((rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 4) + signExtend13 bne_off)
        ((rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 8)
        ((rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      hbne_raw
  -- 3. Frame BNE with x5
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    (.x5 ↦ᵣ n)
    (by pcFree) hbne
  -- 4. Extend to full cr
  have hbne_ext := cpsBranch_extend_code (cr' := cr) (fun a i h => by
    simp only [CodeReq.singleton] at h
    split at h
    · next heq =>
      rw [beq_iff_eq] at heq; subst heq
      simp only [Option.some.injEq] at h; subst h
      show divK_phaseB_cascade_step_code n_val rx bne_off base (base + 4) = _
      simp only [divK_phaseB_cascade_step_code, CodeReq.union, CodeReq.singleton]
      have h0 : ¬(base + 4 = base) := by bv_omega
      simp only [beq_iff_eq, h0, ↓reduceIte]
    · simp at h) hbne_framed
  -- 5. Compose
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  exact cpsBranch_consequence _ _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

end EvmAsm.Evm64
