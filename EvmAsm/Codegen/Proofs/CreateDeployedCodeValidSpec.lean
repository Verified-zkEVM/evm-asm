/-
  EvmAsm.Codegen.Proofs.CreateDeployedCodeValidSpec

  cpsTriple proof of the EIP-7907/EIP-3541 deployed-code validity gate
  (`create_deployed_code_valid`, Codegen/Programs/CreateDeployedCodeValid.lean) —
  the second verdict-glue gate after `create_initcode_size_valid` (cisv), and the
  first THREE-way one. Built in slices (bead evm-asm-x43os.1):

    SLICE 1 (this file): the inner 0xEF byte-check branch + the shared arms, via
    the cisv two-exit pattern. SLICE 2 adds the LBU byte-load + the size/empty
    branches; SLICE 3 the full `create_deployed_code_valid_spec` + deployment.

  Register map: a0 = x10 (code ptr in / 0|1 result out), a1 = x11 (len),
  t0 = x5, t1 = x6 (loaded byte).
-/
import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Proofs.CreateInitcodeSizeValidSpec

namespace EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- The EIP-3541 `0xEF`-prefix byte-check branch of `create_deployed_code_valid`,
    at `base + 20`: `BEQ x6 x5` (x6 = loaded byte0, x5 = 239 = 0xEF) jumps to the
    invalid arm (`base + 32`, `LI x10 1; ret`) when equal, else falls to the valid
    arm (`base + 24`, `LI x10 0; ret`). Result `x10 := if byte0 = 239 then 1 else 0`.
    Mirrors `cisv_spec`'s branch merge (disjoint arms), with the extra `x6/x11/mem`
    carried in the frame. -/
theorem cdcv_byte_branch
    (base byte0 len ptrOld x1_init dwordAddr memVal : Word) :
    cpsTripleWithin 3 (base + 20) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
        (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
            (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
         ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
            (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0)))))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) ** (.x10 ↦ᵣ ptrOld) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) **
       (.x10 ↦ᵣ (if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init)) := by
  -- Taken arm (base+32, invalid): byte0 = 239.
  have armT : cpsTripleWithin 2 (base + 32) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
        (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0)))
      (((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) ** ⌜byte0 = (239 : Word)⌝) **
        ((.x10 ↦ᵣ ptrOld) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init)))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) **
       (.x10 ↦ᵣ (if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨heq, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_pos heq]; sep_perm hrest)
      (cpsTripleWithin_frameL ⌜byte0 = (239 : Word)⌝ (by pcFree)
        (cpsTripleWithin_frameR ((.x6 ↦ᵣ byte0) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal))
          (by pcFree)
          (cisv_arm (base + 32) (239 : Word) x1_init ptrOld (1 : Word))))
  -- Fall arm (base+24, valid): byte0 ≠ 239.
  have armF : cpsTripleWithin 2 (base + 24) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
        (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0)))
      (((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) ** ⌜byte0 ≠ (239 : Word)⌝) **
        ((.x10 ↦ᵣ ptrOld) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init)))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) **
       (.x10 ↦ᵣ (if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hne, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_neg hne]; sep_perm hrest)
      (cpsTripleWithin_frameL ⌜byte0 ≠ (239 : Word)⌝ (by pcFree)
        (cpsTripleWithin_frameR ((.x6 ↦ᵣ byte0) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal))
          (by pcFree)
          (cisv_arm (base + 24) (239 : Word) x1_init ptrOld (0 : Word))))
  -- Branch: BEQ x6 x5, framing the non-branch state (x10/x11/mem/x1).
  have hbr0 := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ ptrOld) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init))
    (by pcFree)
    (generic_beq_spec_within .x6 .x5 (12 : BitVec 13) byte0 (239 : Word) (base + 20))
  have he_t : ((base + 20) + signExtend13 (12 : BitVec 13) : Word) = base + 32 := by
    have : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide
    rw [this]; bv_omega
  have he_f : ((base + 20) + 4 : Word) = base + 24 := by bv_omega
  rw [he_t, he_f] at hbr0
  have hda : (CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).Disjoint
      (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
       ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0)))) := by
    apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
      apply CodeReq.Disjoint.singleton <;> bv_omega
  have hdtf : ((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).Disjoint
      ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0))) := by
    apply CodeReq.Disjoint.union_left <;> apply CodeReq.Disjoint.union_right <;>
      apply CodeReq.Disjoint.singleton <;> bv_omega
  exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hq => by sep_perm hq)
    (cpsBranchWithin_merge hda hdtf hbr0 armT armF)

end EvmAsm.Rv64
