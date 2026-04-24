/-
  EvmAsm.Evm64.DivMod.LimbSpec.LoopSetup

  CPS specs for the Knuth Algorithm D main-loop setup:
    * `divK_loopSetup_code` — `CodeReq.ofProg base (divK_loopSetup bltOff)`.
    * `divK_loopSetup_body_spec` — 3-instruction body (LD n, ADDI x1 = 4,
      SUB x1 = 4 - n).
    * `divK_loopSetup_spec` — full `cpsBranch` wrapping body + BLT that
      skips the loop when `m = 4 - n` is negative.

  Twelfth chunk of the `LimbSpec.lean` split tracked by issue #312. The
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

abbrev divK_loopSetup_code (bltOff : BitVec 13) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_loopSetup bltOff)

/-- Loop setup body: load n, compute m = 4 - n. 3 straight-line instructions.
    Uses signExtend12 4 directly to match addi_x0_spec_gen + sub_spec_gen output. -/
theorem divK_loopSetup_body_spec (sp n v1 v5 : Word)
    (bltOff : BitVec 13) (base : Word) :
    let cr := divK_loopSetup_code bltOff base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
       (.x1 ↦ᵣ (signExtend12 (4 : BitVec 12) - n)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n)) := by
  intro cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 n 3984 base (by nofun)
  have I1 := addi_x0_spec_gen .x1 v1 4 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x1 .x5
    (signExtend12 (4 : BitVec 12)) n (base + 8) (by nofun)
  runBlock I0 I1 I2

/-- Loop setup: load n, compute m = 4-n, BLT if m < 0 (skip loop).
    Taken: m < 0 (n > 4, impossible in practice but handled).
    Not taken: m >= 0, proceed to loop. -/
theorem divK_loopSetup_spec (sp n v1 v5 : Word)
    (bltOff : BitVec 13) (base : Word) :
    let m := signExtend12 (4 : BitVec 12) - n
    let cr := divK_loopSetup_code bltOff base
    let post :=
      (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + signExtend12 3984) ↦ₘ n)
    cpsBranch base cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      -- Taken: m < 0 (signed)
      ((base + 12) + signExtend13 bltOff) post
      -- Not taken: m >= 0
      (base + 16) post := by
  intro m cr post
  have hbody := divK_loopSetup_body_spec sp n v1 v5 bltOff base
  have hblt_raw := blt_spec_gen .x1 .x0 bltOff m (0 : Word) (base + 12)
  have ha1 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  rw [ha1] at hblt_raw
  have hblt : cpsBranch (base + 12) _
      ((.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 12) + signExtend13 bltOff)
        ((.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 16)
        ((.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_weaken
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
      hblt_raw
  have hblt_framed := cpsBranch_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
     ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblt
  have hblt_ext := cpsBranch_extend_code (cr' := cr) (fun a i h => by
    simp only [CodeReq.singleton] at h
    split at h
    · next heq =>
      rw [beq_iff_eq] at heq; subst heq
      simp only [Option.some.injEq] at h; subst h
      show divK_loopSetup_code bltOff base (base + 12) = _
      have : (divK_loopSetup bltOff).length = 4 := by
        unfold divK_loopSetup LD ADDI single seq; rfl
      exact CodeReq.ofProg_lookup base (divK_loopSetup bltOff) 3
        (by omega) (by omega)
    · simp at h) hblt_framed
  exact cpsBranch_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (cpsTriple_seq_cpsBranch_perm_same_cr
      (fun h hp => by xperm_hyp hp) hbody hblt_ext)

end EvmAsm.Evm64
