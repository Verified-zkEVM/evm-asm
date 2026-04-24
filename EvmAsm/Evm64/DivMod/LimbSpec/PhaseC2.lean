/-
  EvmAsm.Evm64.DivMod.LimbSpec.PhaseC2

  CPS specs for the Knuth Algorithm D "phase C2" — the 3-instruction
  setup that stores `shift` to scratch, zeros `x2`, then computes
  `x2 = -shift` (the "anti-shift") — followed by a BEQ that jumps past
  the normalize/denormalize dance when `shift = 0`:
    * `divK_phaseC2_code` — `CodeReq.ofProg base (divK_phaseC2 shift0_off)`.
    * `divK_phaseC2_body_spec` — SD + ADDI + SUB (3 instructions).
    * `divK_phaseC2_spec` — full `cpsBranch` wrapping body + BEQ.

  Ninth chunk of the `LimbSpec.lean` split tracked by issue #312. The
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

abbrev divK_phaseC2_code (shift0_off : BitVec 13) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseC2 shift0_off)

/-- Phase C2 body: SD shift to scratch, ADDI x2 = 0, SUB x2 = -shift.
    Preserves x6 and x0 for the subsequent BEQ.
    The postcondition uses `signExtend12 (0 : BitVec 12) - shift` (= 0 - shift)
    to match the syntactic form produced by addi_x0_spec_gen + sub_spec_gen. -/
theorem divK_phaseC2_body_spec (sp shift v2 shiftMem : Word)
    (shift0_off : BitVec 13) (base : Word) :
    let cr := divK_phaseC2_code shift0_off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  intro cr
  have I0 := sd_spec_gen .x12 .x6 sp shift shiftMem 3992 base
  have I1 := addi_x0_spec_gen .x2 v2 0 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x2 .x6
    (signExtend12 (0 : BitVec 12)) shift (base + 8) (by nofun)
  runBlock I0 I1 I2

/-- Phase C2: store shift, compute antiShift, BEQ if shift=0.
    Taken: shift = 0, skip normalization.
    Not taken: shift ≠ 0, proceed to normalize.
    antiShift = signExtend12 0 - shift (= 0 - shift = negation of shift amount). -/
theorem divK_phaseC2_spec (sp shift v2 shiftMem : Word)
    (shift0_off : BitVec 13) (base : Word) :
    let cr := divK_phaseC2_code shift0_off base
    let post :=
      (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) **
      (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + signExtend12 3992) ↦ₘ shift)
    cpsBranch base cr
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      -- Taken: shift = 0
      ((base + 12) + signExtend13 shift0_off) post
      -- Not taken: shift ≠ 0
      (base + 16) post := by
  intro cr post
  have hbody := divK_phaseC2_body_spec sp shift v2 shiftMem shift0_off base
  have hbeq_raw := beq_spec_gen .x6 .x0 shift0_off shift (0 : Word) (base + 12)
  have ha1 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  rw [ha1] at hbeq_raw
  have hbeq : cpsBranch (base + 12) _
      ((.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 12) + signExtend13 shift0_off)
        ((.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 16)
        ((.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_weaken
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
      hbeq_raw
  have hbeq_framed := cpsBranch_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hbeq_ext := cpsBranch_extend_code (cr' := cr) (fun a i h => by
    simp only [CodeReq.singleton] at h
    split at h
    · next heq =>
      rw [beq_iff_eq] at heq; subst heq
      simp only [Option.some.injEq] at h; subst h
      show divK_phaseC2_code shift0_off base (base + 12) = _
      have : (divK_phaseC2 shift0_off).length = 4 := by
        unfold divK_phaseC2 SD ADDI single seq; rfl
      exact CodeReq.ofProg_lookup base (divK_phaseC2 shift0_off) 3
        (by omega) (by omega)
    · simp at h) hbeq_framed
  exact cpsBranch_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (cpsTriple_seq_cpsBranch_perm_same_cr
      (fun h hp => by xperm_hyp hp) hbody hbeq_ext)

end EvmAsm.Evm64
