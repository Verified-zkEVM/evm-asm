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

/-- The byte-load segment of `create_deployed_code_valid`, at `base + 12`:
    `LBU x6, 0(x10)` (load code `byte0`), `LI x5, 239`, then the 0xEF byte-check
    branch (`cdcv_byte_branch`). Establishes `x10 := if byte0 = 239 then 1 else 0`
    where `byte0 = (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64`. -/
theorem cdcv_seg3
    (base ptrVal oldByte oldT0 len x1_init dwordAddr wordVal : Word)
    (halign : alignToDword ptrVal = dwordAddr)
    (hvalid : isValidByteAccess ptrVal = true) :
    cpsTripleWithin 5 (base + 12) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).union
        ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
          ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
            (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
                (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
             ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
                (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0)))))))
      ((.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
      ((.x6 ↦ᵣ (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64) **
       (.x5 ↦ᵣ (239 : Word)) **
       (.x10 ↦ᵣ (if (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64 = (239 : Word)
                 then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) := by
  -- LBU x6, 0(x10) : x6 := byte0  (offset 0 ⇒ addr = ptrVal).
  have hz : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have h_lbu0 := generic_lbu_spec_within .x6 .x10 ptrVal oldByte (0 : BitVec 12)
    (base + 12) dwordAddr wordVal (by nofun)
    (by rw [hz]; simpa using halign) (by rw [hz]; simpa using hvalid)
  have haddr : ptrVal + signExtend12 (0 : BitVec 12) = ptrVal := by
    rw [hz]; exact BitVec.add_zero ptrVal
  rw [haddr] at h_lbu0
  have hx16 : (base + 12 + 4 : Word) = base + 16 := by bv_omega
  rw [hx16] at h_lbu0
  set byte0 := (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64 with hb0
  -- Flat intermediate state threaded through (matching cdcv_byte_branch's order).
  have h_lbu : cpsTripleWithin 1 (base + 12) (base + 16)
      (CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12)))
      ((.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hq => by sep_perm hq)
      (cpsTripleWithin_frameR ((.x5 ↦ᵣ oldT0) ** (.x11 ↦ᵣ len) ** (.x1 ↦ᵣ x1_init)) (by pcFree) h_lbu0)
  -- LI x5, 239.
  have h_li0 := li_spec_within .x5 oldT0 (239 : Word) (base + 16) (by nofun)
  have hx20 : (base + 16 + 4 : Word) = base + 20 := by bv_omega
  rw [hx20] at h_li0
  have h_li : cpsTripleWithin 1 (base + 16) (base + 20)
      (CodeReq.singleton (base + 16) (.LI .x5 (239 : Word)))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) ** (.x10 ↦ᵣ ptrVal) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hq => by sep_perm hq)
      (cpsTripleWithin_frameR ((.x6 ↦ᵣ byte0) ** (.x10 ↦ᵣ ptrVal) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
        (by pcFree) h_li0)
  have h_byte := cdcv_byte_branch base byte0 len ptrVal x1_init dwordAddr wordVal
  have hd_li_byte : (CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).Disjoint
      ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
        (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
         ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0))))) := by
    apply CodeReq.Disjoint.union_right
    · apply CodeReq.Disjoint.singleton; bv_omega
    · apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
        apply CodeReq.Disjoint.singleton <;> bv_omega
  have hd_lbu_rest : (CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).Disjoint
      ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
        ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
          (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
           ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0)))))) := by
    apply CodeReq.Disjoint.union_right
    · apply CodeReq.Disjoint.singleton; bv_omega
    · apply CodeReq.Disjoint.union_right
      · apply CodeReq.Disjoint.singleton; bv_omega
      · apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
          apply CodeReq.Disjoint.singleton <;> bv_omega
  exact cpsTripleWithin_seq hd_lbu_rest h_lbu (cpsTripleWithin_seq hd_li_byte h_li h_byte)

/-- The empty-length-check branch of `create_deployed_code_valid`, at `base + 8`:
    `BEQ x11 x0` (x11 = len) jumps to the valid arm (`base + 24`, `LI x10 0; ret`)
    when `len = 0`, else falls to the byte-load segment (`base + 12`, `cdcv_seg3`).
    The two paths are merged over ONE shared `CodeReq` (the seg3 code already
    contains the valid arm at `base + 24`, reached as the byte-check fall arm), via
    `cpsBranchWithin_merge_same_cr`. Result
    `x10 := if len = 0 then 0 else if byte0 = 239 then 1 else 0`, with the
    path-dependent scratch regs `x5`/`x6` abstracted to `regOwn`. -/
theorem cdcv_merge2
    (base ptrVal oldByte oldT0 len x1_init dwordAddr wordVal : Word)
    (halign : alignToDword ptrVal = dwordAddr)
    (hvalid : isValidByteAccess ptrVal = true) :
    cpsTripleWithin 6 (base + 8) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union
        ((CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).union
          ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
            ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
              (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
                  (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
               ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
                  (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0))))))))
      ((.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) **
       (.x10 ↦ᵣ ptrVal) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
      ((regOwn .x6) ** (regOwn .x5) **
       (.x10 ↦ᵣ (if len = 0 then (0 : Word)
                 else if (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64 = (239 : Word)
                      then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) := by
  have hseg := cdcv_seg3 base ptrVal oldByte oldT0 len x1_init dwordAddr wordVal halign hvalid
  set byte0 := (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64 with hb0
  set scode :=
    ((CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).union
      ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
        ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
          (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
              (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
           ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
              (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0))))))) with hsc
  -- {base+8} is disjoint from all of seg3's code.
  have hd8 : (CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).Disjoint scode := by
    rw [hsc]
    apply CodeReq.Disjoint.union_right
    · apply CodeReq.Disjoint.singleton; bv_omega
    · apply CodeReq.Disjoint.union_right
      · apply CodeReq.Disjoint.singleton; bv_omega
      · apply CodeReq.Disjoint.union_right
        · apply CodeReq.Disjoint.singleton; bv_omega
        · apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
            apply CodeReq.Disjoint.singleton <;> bv_omega
  -- seg3 lifted to the merged code (seg3's code is the left-biased tail).
  have hseg' := cpsTripleWithin_extend_code (CodeReq.mono_union_right hd8 (fun _ _ h => h)) hseg
  -- The valid arm's two addresses are inside seg3's code → inside the merged code.
  have hblk24 : ((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
      (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))) (base + 24) = none := by
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 32)))]
    exact CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 32 + 4))
  have hblk28 : ((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
      (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))) (base + 24 + 4) = none := by
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 32)))]
    exact CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 32 + 4))
  have hva24 : ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode)
      (base + 24) = some (.LI .x10 (0 : Word)) := by
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 8)))]
    rw [hsc]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 12)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 16)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 20)))]
    rw [CodeReq.union_none_left hblk24]
    exact CodeReq.union_hit (CodeReq.singleton_get _ _)
  have hva28 : ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode)
      (base + 24 + 4) = some (.JALR .x0 .x1 0) := by
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 8)))]
    rw [hsc]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 12)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 16)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 20)))]
    rw [CodeReq.union_none_left hblk28]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 24)))]
    exact CodeReq.singleton_get _ _
  have hvalid_mono := CodeReq.union_split_mono (CodeReq.singleton_mono hva24) (CodeReq.singleton_mono hva28)
  -- Taken arm (len = 0): the valid arm at base+24, x10 := 0.
  have h_t : cpsTripleWithin 5 (base + 24) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode)
      (((.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** ⌜len = (0 : Word)⌝) **
        ((.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) **
          (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)))
      ((regOwn .x6) ** (regOwn .x5) **
       (.x10 ↦ᵣ (if len = (0 : Word) then (0 : Word) else if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_extend_code hvalid_mono
      (cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken
          (fun _ hp => by sep_perm hp)
          (fun h hq => by
            obtain ⟨heq, hrest⟩ := (sepConj_pure_left h).mp hq
            rw [if_pos heq]
            have h1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x5 oldT0))) h hrest
            have h2 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 oldByte)) h h1
            sep_perm h2)
          (cpsTripleWithin_frameL ⌜len = (0 : Word)⌝ (by pcFree)
            (cpsTripleWithin_frameR ((.x6 ↦ᵣ oldByte) ** (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal))
              (by pcFree)
              (cisv_arm (base + 24) oldT0 x1_init ptrVal (0 : Word))))))
  -- Fall arm (len ≠ 0): seg3, x10 := if byte0 = 239 then 1 else 0.
  have h_f : cpsTripleWithin 5 (base + 12) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode)
      (((.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** ⌜len ≠ (0 : Word)⌝) **
        ((.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) **
          (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)))
      ((regOwn .x6) ** (regOwn .x5) **
       (.x10 ↦ᵣ (if len = (0 : Word) then (0 : Word) else if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hne, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_neg hne]
        have h1 := sepConj_mono_left (sepConj_mono_left (regIs_to_regOwn .x6 byte0)) h hrest
        have h2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x5 (239 : Word)))) h h1
        sep_perm h2)
      (cpsTripleWithin_frameL ⌜len ≠ (0 : Word)⌝ (by pcFree)
        (cpsTripleWithin_frameR (.x0 ↦ᵣ 0) (by pcFree) hseg'))
  -- Branch: BEQ x11 x0, framing the non-branch state.
  have hbr0 := cpsBranchWithin_frameR
    ((.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
    (by pcFree)
    (generic_beq_spec_within .x11 .x0 (16 : BitVec 13) len (0 : Word) (base + 8))
  have he_t : ((base + 8) + signExtend13 (16 : BitVec 13) : Word) = base + 24 := by
    have : signExtend13 (16 : BitVec 13) = (16 : Word) := by decide
    rw [this]; bv_omega
  have he_f : ((base + 8) + 4 : Word) = base + 12 := by bv_omega
  rw [he_t, he_f] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (@CodeReq.union_mono_left (CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))) scode) hbr0
  exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hq => by sep_perm hq)
    (cpsBranchWithin_merge_same_cr hbr h_t h_f)

end EvmAsm.Rv64
