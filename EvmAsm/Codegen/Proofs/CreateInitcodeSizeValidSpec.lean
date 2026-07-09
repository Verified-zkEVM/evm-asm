/-
  EvmAsm.Codegen.Proofs.CreateInitcodeSizeValidSpec

  First cpsTriple proof of a VERDICT ORCHESTRATION-GLUE block — the EIP-3860
  init-code size gate (`create_initcode_size_valid`,
  Codegen/Programs/CreateInitcodeSizeValid.lean). Where the opcode handlers are
  straight-line bodies lifted through the dispatcher tails, the verdict glue is
  branchy (two-exit gates, linear scans). This file proves the size gate's
  structured RV64 program as a `cpsTriple`:

    a0 := (if MAX_INITCODE_SIZE(131072) < len then 1 else 0); return

  via a reusable two-exit pattern: `cisv_arm` (the generic `LI x10 c ;; ret`
  arm) + `generic_bltu_spec_within` (branch) + `cpsBranchWithin_merge` (with the
  conditional post discharged per-arm from the branch's `⌜BitVec.ult⌝` fact via
  `sepConj_pure_left`). The same pattern generalises to every two-exit verdict
  gate. Connecting this to the deployed asm string (refactor the codegen block to
  emit via `emitProgram` from this structured program, byte-identically) is the
  deployment follow-up (bead evm-asm-x43os). Axiom-clean.
-/
import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.CreateInitcodeSizeValid
namespace EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

theorem cisv_arm (base v5 x1_init x10old c : Word) :
    cpsTripleWithin 2 base (x1_init &&& ~~~1)
      ((CodeReq.singleton base (.LI .x10 c)).union
        (CodeReq.singleton (base + 4) (.JALR .x0 .x1 0)))
      ((.x10 ↦ᵣ x10old) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ x1_init))
      ((.x10 ↦ᵣ c) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ x1_init)) := by
  have hdisj : (CodeReq.singleton base (.LI .x10 c)).Disjoint
      (CodeReq.singleton (base + 4) (.JALR .x0 .x1 0)) := by
    apply CodeReq.Disjoint.singleton; bv_omega
  have h1 : cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LI .x10 c))
      ((.x10 ↦ᵣ x10old) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ x1_init))
      ((.x10 ↦ᵣ c) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR ((.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ x1_init)) (by pcFree)
        (li_spec_within .x10 x10old c base (by nofun)))
  have h2 : cpsTripleWithin 1 (base + 4) (x1_init &&& ~~~1)
      (CodeReq.singleton (base + 4) (.JALR .x0 .x1 0))
      ((.x10 ↦ᵣ c) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ x1_init))
      ((.x10 ↦ᵣ c) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameL ((.x10 ↦ᵣ c) ** (.x5 ↦ᵣ v5)) (by pcFree)
        (EvmAsm.Evm64.ret_spec_within' (base + 4) x1_init))
  exact cpsTripleWithin_seq hdisj h1 h2

theorem cisv_spec (base v5old len x1_init : Word) :
    cpsTripleWithin 4 base (x1_init &&& ~~~1)
      ((CodeReq.singleton base (.LI .x5 (131072 : Word))).union
        ((CodeReq.singleton (base + 4) (.BLTU .x5 .x10 (12 : BitVec 13))).union
          (((CodeReq.singleton (base + 16) (.LI .x10 (1 : Word))).union
              (CodeReq.singleton (base + 16 + 4) (.JALR .x0 .x1 0))).union
           ((CodeReq.singleton (base + 8) (.LI .x10 (0 : Word))).union
              (CodeReq.singleton (base + 8 + 4) (.JALR .x0 .x1 0))))))
      ((.x5 ↦ᵣ v5old) ** (.x10 ↦ᵣ len) ** (.x1 ↦ᵣ x1_init))
      ((.x5 ↦ᵣ (131072 : Word)) **
       (.x10 ↦ᵣ (if BitVec.ult (131072 : Word) len then (1 : Word) else 0)) **
       (.x1 ↦ᵣ x1_init)) := by
  have armT : cpsTripleWithin 2 (base + 16) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 16) (.LI .x10 (1 : Word))).union
        (CodeReq.singleton (base + 16 + 4) (.JALR .x0 .x1 0)))
      (((.x5 ↦ᵣ (131072 : Word)) ** (.x10 ↦ᵣ len) ** ⌜BitVec.ult (131072 : Word) len⌝) ** (.x1 ↦ᵣ x1_init))
      ((.x5 ↦ᵣ (131072 : Word)) **
       (.x10 ↦ᵣ (if BitVec.ult (131072 : Word) len then (1 : Word) else 0)) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hult, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_pos hult]; sep_perm hrest)
      (cpsTripleWithin_frameL ⌜BitVec.ult (131072 : Word) len⌝ (by pcFree)
        (cisv_arm (base + 16) (131072 : Word) x1_init len (1 : Word)))
  have armF : cpsTripleWithin 2 (base + 8) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 8) (.LI .x10 (0 : Word))).union
        (CodeReq.singleton (base + 8 + 4) (.JALR .x0 .x1 0)))
      (((.x5 ↦ᵣ (131072 : Word)) ** (.x10 ↦ᵣ len) ** ⌜¬ BitVec.ult (131072 : Word) len⌝) ** (.x1 ↦ᵣ x1_init))
      ((.x5 ↦ᵣ (131072 : Word)) **
       (.x10 ↦ᵣ (if BitVec.ult (131072 : Word) len then (1 : Word) else 0)) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hult, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_neg hult]; sep_perm hrest)
      (cpsTripleWithin_frameL ⌜¬ BitVec.ult (131072 : Word) len⌝ (by pcFree)
        (cisv_arm (base + 8) (131072 : Word) x1_init len (0 : Word)))
  have hbr0 := cpsBranchWithin_frameR ((.x1 ↦ᵣ x1_init)) (by pcFree)
    (generic_bltu_spec_within .x5 .x10 (12 : BitVec 13) (131072 : Word) len (base + 4))
  have he_t : ((base + 4) + signExtend13 (12 : BitVec 13) : Word) = base + 16 := by
    have : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide
    rw [this]; bv_omega
  have he_f : ((base + 4) + 4 : Word) = base + 8 := by bv_omega
  rw [he_t, he_f] at hbr0
  have hda : (CodeReq.singleton (base + 4) (.BLTU .x5 .x10 (12 : BitVec 13))).Disjoint
      (((CodeReq.singleton (base + 16) (.LI .x10 (1 : Word))).union (CodeReq.singleton (base + 16 + 4) (.JALR .x0 .x1 0))).union
       ((CodeReq.singleton (base + 8) (.LI .x10 (0 : Word))).union (CodeReq.singleton (base + 8 + 4) (.JALR .x0 .x1 0)))) := by
    apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
      apply CodeReq.Disjoint.singleton <;> bv_omega
  have hdtf : ((CodeReq.singleton (base + 16) (.LI .x10 (1 : Word))).union (CodeReq.singleton (base + 16 + 4) (.JALR .x0 .x1 0))).Disjoint
      ((CodeReq.singleton (base + 8) (.LI .x10 (0 : Word))).union (CodeReq.singleton (base + 8 + 4) (.JALR .x0 .x1 0))) := by
    apply CodeReq.Disjoint.union_left <;> apply CodeReq.Disjoint.union_right <;>
      apply CodeReq.Disjoint.singleton <;> bv_omega
  have hmerge := cpsBranchWithin_merge hda hdtf hbr0 armT armF
  have hpro : cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LI .x5 (131072 : Word)))
      ((.x5 ↦ᵣ v5old) ** (.x10 ↦ᵣ len) ** (.x1 ↦ᵣ x1_init))
      (((.x5 ↦ᵣ (131072 : Word)) ** (.x10 ↦ᵣ len)) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR ((.x10 ↦ᵣ len) ** (.x1 ↦ᵣ x1_init)) (by pcFree)
        (li_spec_within .x5 v5old (131072 : Word) base (by nofun)))
  have hdpro : (CodeReq.singleton base (.LI .x5 (131072 : Word))).Disjoint
      ((CodeReq.singleton (base + 4) (.BLTU .x5 .x10 (12 : BitVec 13))).union
        (((CodeReq.singleton (base + 16) (.LI .x10 (1 : Word))).union (CodeReq.singleton (base + 16 + 4) (.JALR .x0 .x1 0))).union
         ((CodeReq.singleton (base + 8) (.LI .x10 (0 : Word))).union (CodeReq.singleton (base + 8 + 4) (.JALR .x0 .x1 0))))) := by
    apply CodeReq.Disjoint.union_right
    · apply CodeReq.Disjoint.singleton; bv_omega
    · apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
        apply CodeReq.Disjoint.singleton <;> bv_omega
  exact cpsTripleWithin_seq hdpro hpro hmerge

/-- Commutativity of `CodeReq.union` for disjoint code maps. No general
    `union_comm` holds (overlapping maps prefer their left argument), but for
    disjoint maps the order is irrelevant — exactly what the deployment-link
    alignment below needs to match `ofProg`'s sequential layout to `cisv_spec`'s
    branch-merge layout. -/
theorem CodeReq.union_comm_of_disjoint {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2) :
    cr1.union cr2 = cr2.union cr1 := by
  funext a
  simp only [CodeReq.union]
  rcases hd a with h1 | h2
  · rw [h1]; cases cr2 a <;> rfl
  · rw [h2]; cases cr1 a <;> rfl

/-- The DEPLOYED gate carries the cpsTriple. `cisv_spec` restated over
    `CodeReq.ofProg base EvmAsm.Codegen.cisvProgram` — the six-instruction
    STRUCTURED program the codegen actually emits (via `emitProgram`,
    byte-identical to the prior asm, probe-verified 0/0/0/1). This is the
    explicit proof↔deployment link: the emitted `create_initcode_size_valid`
    block satisfies `a0 := (if 131072 < len then 1 else 0); return`. The alignment
    reassociates `ofProg`'s sequential six-singleton layout into `cisv_spec`'s
    branch-merge layout (arms reordered) via `union_comm_of_disjoint`. -/
theorem cisv_deployed_spec (base v5old len x1_init : Word) :
    cpsTripleWithin 4 base (x1_init &&& ~~~1)
      (CodeReq.ofProg base EvmAsm.Codegen.cisvProgram)
      ((.x5 ↦ᵣ v5old) ** (.x10 ↦ᵣ len) ** (.x1 ↦ᵣ x1_init))
      ((.x5 ↦ᵣ (131072 : Word)) **
       (.x10 ↦ᵣ (if BitVec.ult (131072 : Word) len then (1 : Word) else 0)) **
       (.x1 ↦ᵣ x1_init)) := by
  have hAB : ((CodeReq.singleton (base + 8) (.LI .x10 (0 : Word))).union
        (CodeReq.singleton (base + 8 + 4) (.JALR .x0 .x1 0))).Disjoint
      ((CodeReq.singleton (base + 16) (.LI .x10 (1 : Word))).union
        (CodeReq.singleton (base + 16 + 4) (.JALR .x0 .x1 0))) := by
    apply CodeReq.Disjoint.union_left <;> apply CodeReq.Disjoint.union_right <;>
      apply CodeReq.Disjoint.singleton <;> bv_omega
  have hcode : CodeReq.ofProg base EvmAsm.Codegen.cisvProgram =
      ((CodeReq.singleton base (.LI .x5 (131072 : Word))).union
        ((CodeReq.singleton (base + 4) (.BLTU .x5 .x10 (12 : BitVec 13))).union
          (((CodeReq.singleton (base + 16) (.LI .x10 (1 : Word))).union
              (CodeReq.singleton (base + 16 + 4) (.JALR .x0 .x1 0))).union
           ((CodeReq.singleton (base + 8) (.LI .x10 (0 : Word))).union
              (CodeReq.singleton (base + 8 + 4) (.JALR .x0 .x1 0)))))) := by
    simp only [EvmAsm.Codegen.cisvProgram]
    rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
        CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
    rw [show ((base + 4) + 4 : Word) = base + 8 from by bv_omega,
        show ((base + 8) + 4 + 4 : Word) = base + 16 from by bv_omega]
    congr 1
    congr 1
    rw [← CodeReq.union_assoc]
    exact CodeReq.union_comm_of_disjoint hAB
  rw [hcode]; exact cisv_spec base v5old len x1_init

end EvmAsm.Rv64

