/-
  EvmAsm.EL.RLP.ProgramSpec

  Executable specs for RLP decoder programs.
-/

import EvmAsm.EL.RLP.Program
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

namespace EvmAsm.EL.RLP

abbrev rlp_prefix_classify_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (rlp_prefix_classify .x5 .x10 .x6)

/--
  Single-byte path of the executable RLP prefix classifier.

  If the input prefix in `x5` is below `0x80`, the first BLTU jumps to the
  single-byte block, writes the `.singleByte` tag to `x10`, and then reaches
  the common exit at `base + 72`.
-/
theorem rlp_prefix_classify_singleByte_spec_within
    (pfx outOld tmpOld : Word) (base : Word)
    (h_single : BitVec.ult pfx (0x80 : Word)) :
    cpsTripleWithin 4 base (base + 72) (rlp_prefix_classify_code base)
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx) ** (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ PrefixClass.toWord .singleByte) ** (.x5 ↦ᵣ pfx) **
        (.x6 ↦ᵣ (0x80 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have I0 := li_spec_gen_within .x6 tmpOld (0x80 : Word) base (by nofun)
  have Hbr_raw := bltu_spec_gen_within .x5 .x6 rlpPrefixClassifyBranchOff
    pfx (0x80 : Word) (base + 4)
  have ha_t : (base + 4) + signExtend13 rlpPrefixClassifyBranchOff = base + 40 := by
    unfold rlpPrefixClassifyBranchOff
    rv64_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at Hbr_raw
  have Hbr_framed := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) Hbr_raw
  have Hbr_ext : cpsBranchWithin 1 (base + 4) (rlp_prefix_classify_code base)
      (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0x80 : Word))) **
        ((.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word))))
      (base + 40)
        (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0x80 : Word)) ** ⌜BitVec.ult pfx (0x80 : Word)⌝) **
          ((.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word))))
      (base + 8)
        (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0x80 : Word)) ** ⌜¬BitVec.ult pfx (0x80 : Word)⌝) **
          ((.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))) :=
    cpsBranchWithin_extend_code (cr' := rlp_prefix_classify_code base) (fun a i h => by
      simp only [CodeReq.singleton] at h
      split at h
      · next heq =>
        rw [beq_iff_eq] at heq
        rw [heq]
        simp only [Option.some.injEq] at h
        subst h
        show rlp_prefix_classify_code base (base + 4) = some (.BLTU .x5 .x6 rlpPrefixClassifyBranchOff)
        exact CodeReq.ofProg_lookup base (rlp_prefix_classify .x5 .x10 .x6) 1
          (by rw [rlp_prefix_classify_length]; norm_num)
          (by rw [rlp_prefix_classify_length]; norm_num)
      · simp at h) Hbr_framed
  have Hprefix : cpsBranchWithin 2 base (rlp_prefix_classify_code base)
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx) ** (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 40)
        (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0x80 : Word)) ** ⌜BitVec.ult pfx (0x80 : Word)⌝) **
          ((.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word))))
      (base + 8)
        (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0x80 : Word)) ** ⌜¬BitVec.ult pfx (0x80 : Word)⌝) **
          ((.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))) := by
    have I0_ext := cpsTripleWithin_extend_code (cr' := rlp_prefix_classify_code base) (fun a i h => by
      simp only [CodeReq.singleton] at h
      split at h
      · next heq =>
        rw [beq_iff_eq] at heq
        rw [heq]
        simp only [Option.some.injEq] at h
        subst h
        show rlp_prefix_classify_code base base = some (.LI .x6 (0x80 : Word))
        change CodeReq.ofProg base (.LI .x6 (0x80 : Word) :: _) base = some (.LI .x6 (0x80 : Word))
        rw [CodeReq.ofProg_cons]
        simp [CodeReq.union, CodeReq.singleton]
      · simp at h) I0
    have I0_framed := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcFree) I0_ext
    exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun h hp => by xperm_hyp hp) I0_framed Hbr_ext
  have Htaken := cpsBranchWithin_takenPath Hprefix (fun hp hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
    exact ((sepConj_pure_right _).1 h_pure).2 h_single)
  have I2 := li_spec_gen_within .x10 outOld (PrefixClass.toWord .singleByte) (base + 40) (by nofun)
  have I3 := jal_x0_spec_gen_within rlpPrefixClassifySingleByteExitOff (base + 44)
  have ha_exit : (base + 44) + signExtend21 rlpPrefixClassifySingleByteExitOff = base + 72 := by
    unfold rlpPrefixClassifySingleByteExitOff
    rv64_addr
  rw [ha_exit] at I3
  have Hsuffix : cpsTripleWithin 2 (base + 40) (base + 72) (rlp_prefix_classify_code base)
      (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0x80 : Word)) ** ⌜BitVec.ult pfx (0x80 : Word)⌝) **
        ((.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word))))
      ((.x10 ↦ᵣ PrefixClass.toWord .singleByte) ** (.x5 ↦ᵣ pfx) **
        (.x6 ↦ᵣ (0x80 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
    have I2_ext := cpsTripleWithin_extend_code (cr' := rlp_prefix_classify_code base) (fun a i h => by
      simp only [CodeReq.singleton] at h
      split at h
      · next heq =>
        rw [beq_iff_eq] at heq
        rw [heq]
        simp only [Option.some.injEq] at h
        subst h
        show rlp_prefix_classify_code base (base + 40) =
          some (.LI .x10 (PrefixClass.toWord .singleByte))
        exact CodeReq.ofProg_lookup base (rlp_prefix_classify .x5 .x10 .x6) 10
          (by rw [rlp_prefix_classify_length]; norm_num)
          (by rw [rlp_prefix_classify_length]; norm_num)
      · simp at h) I2
    have I3_ext := cpsTripleWithin_extend_code (cr' := rlp_prefix_classify_code base) (fun a i h => by
      simp only [CodeReq.singleton] at h
      split at h
      · next heq =>
        rw [beq_iff_eq] at heq
        rw [heq]
        simp only [Option.some.injEq] at h
        subst h
        show rlp_prefix_classify_code base (base + 44) =
          some (.JAL .x0 rlpPrefixClassifySingleByteExitOff)
        exact CodeReq.ofProg_lookup base (rlp_prefix_classify .x5 .x10 .x6) 11
          (by rw [rlp_prefix_classify_length]; norm_num)
          (by rw [rlp_prefix_classify_length]; norm_num)
      · simp at h) I3
    have I3_framed_raw := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ PrefixClass.toWord .singleByte) ** (.x5 ↦ᵣ pfx) **
        (.x6 ↦ᵣ (0x80 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcFree) I3_ext
    have I3_framed : cpsTripleWithin 1 (base + 44) (base + 72) (rlp_prefix_classify_code base)
        ((.x10 ↦ᵣ PrefixClass.toWord .singleByte) ** (.x5 ↦ᵣ pfx) **
          (.x6 ↦ᵣ (0x80 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
        ((.x10 ↦ᵣ PrefixClass.toWord .singleByte) ** (.x5 ↦ᵣ pfx) **
          (.x6 ↦ᵣ (0x80 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
      cpsTripleWithin_weaken
        (fun h hp => by simpa [sepConj_emp_left', sepConj_emp_right'] using hp)
        (fun h hp => by simpa [sepConj_emp_left', sepConj_emp_right'] using hp)
        I3_framed_raw
    have Hli : cpsTripleWithin 1 (base + 40) (base + 44) (rlp_prefix_classify_code base)
        (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0x80 : Word)) ** ⌜BitVec.ult pfx (0x80 : Word)⌝) **
          ((.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word))))
        ((.x10 ↦ᵣ PrefixClass.toWord .singleByte) ** (.x5 ↦ᵣ pfx) **
          (.x6 ↦ᵣ (0x80 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
      by
        have I2_framed := cpsTripleWithin_frameR
          ((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0x80 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
          (by pcFree) I2_ext
        have ha : (base + 40 : Word) + 4 = base + 44 := by bv_addr
        rw [ha] at I2_framed
        exact cpsTripleWithin_weaken
          (fun h hp => by
            have hp_no_pure :
                (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0x80 : Word))) **
                  ((.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))) h :=
              sepConj_mono_left
                (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
            xperm_hyp hp_no_pure)
          (fun h hp => hp)
          I2_framed
    exact cpsTripleWithin_seq_same_cr Hli I3_framed
  exact cpsTripleWithin_seq_same_cr Htaken Hsuffix

end EvmAsm.EL.RLP
