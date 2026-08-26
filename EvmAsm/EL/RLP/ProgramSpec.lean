/-
  EvmAsm.EL.RLP.ProgramSpec

  Executable specs for RLP decoder programs.
-/

module

public import EvmAsm.EL.RLP.Program
public import EvmAsm.Rv64.AddrNorm
public import EvmAsm.Rv64.ControlFlow
public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.Tactics.RunBlock
public import EvmAsm.Rv64.Tactics.XSimp

@[expose] public section

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

/--
  Pure-classifier bridge for the single-byte executable path.

  This version takes the EL/RLP predicate `classifyPrefix pfx = .singleByte`
  and feeds the zero-extended byte to the executable classifier spec.
-/
theorem rlp_prefix_classify_singleByte_of_classifyPrefix_spec_within
    (pfx : Byte) (outOld tmpOld : Word) (base : Word)
    (h_class : classifyPrefix pfx = .singleByte) :
    cpsTripleWithin 4 base (base + 72) (rlp_prefix_classify_code base)
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ PrefixClass.toWord .singleByte) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x6 ↦ᵣ (0x80 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  apply rlp_prefix_classify_singleByte_spec_within
  have h_lt := (classifyPrefix_singleByte_iff pfx).mp h_class
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.ult]
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

abbrev rlp_prefix_short_payload_len_code (base baseTag : Word) : CodeReq :=
  CodeReq.ofProg base (rlp_prefix_short_payload_len .x5 .x10 .x6 baseTag)

/--
  Executable short-payload length helper.

  The helper loads the class base tag (`0x80` for short byte strings or `0xC0`
  for short lists) and subtracts it from the prefix byte already in `x5`.
-/
theorem rlp_prefix_short_payload_len_spec_within
    (pfx outOld tmpOld baseTag : Word) (base : Word) :
    cpsTripleWithin 2 base (base + 8) (rlp_prefix_short_payload_len_code base baseTag)
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx) ** (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ pfx - baseTag) ** (.x5 ↦ᵣ pfx) **
        (.x6 ↦ᵣ baseTag) ** (.x0 ↦ᵣ (0 : Word))) := by
  have I0 := li_spec_gen_within .x6 tmpOld baseTag base (by nofun)
  have I0_ext := cpsTripleWithin_extend_code
    (cr' := rlp_prefix_short_payload_len_code base baseTag) (fun a i h => by
      simp only [CodeReq.singleton] at h
      split at h
      · next heq =>
        rw [beq_iff_eq] at heq
        rw [heq]
        simp only [Option.some.injEq] at h
        subst h
        show rlp_prefix_short_payload_len_code base baseTag base = some (.LI .x6 baseTag)
        change CodeReq.ofProg base (.LI .x6 baseTag :: _) base = some (.LI .x6 baseTag)
        rw [CodeReq.ofProg_cons]
        simp [CodeReq.union, CodeReq.singleton]
      · simp at h) I0
  have I0_framed := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) I0_ext
  have I1 := sub_spec_gen_within .x10 .x5 .x6 pfx baseTag outOld (base + 4) (by nofun)
  have I1_ext := cpsTripleWithin_extend_code
    (cr' := rlp_prefix_short_payload_len_code base baseTag) (fun a i h => by
      simp only [CodeReq.singleton] at h
      split at h
      · next heq =>
        rw [beq_iff_eq] at heq
        rw [heq]
        simp only [Option.some.injEq] at h
        subst h
        show rlp_prefix_short_payload_len_code base baseTag (base + 4) =
          some (.SUB .x10 .x5 .x6)
        exact CodeReq.ofProg_lookup base
          (rlp_prefix_short_payload_len .x5 .x10 .x6 baseTag) 1
          (by rw [rlp_prefix_short_payload_len_length]; norm_num)
          (by rw [rlp_prefix_short_payload_len_length]; norm_num)
      · simp at h) I1
  have I1_framed := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)))
    (by pcFree) I1_ext
  have ha_mid : (base : Word) + 4 = base + 4 := rfl
  have ha_exit : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_mid] at I0_framed
  rw [ha_exit] at I1_framed
  have Hseq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) I0_framed I1_framed
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    Hseq

theorem rlp_prefix_short_bytes_payload_len_spec_within
    (pfx : Byte) (outOld tmpOld : Word) (base : Word) :
    cpsTripleWithin 2 base (base + 8) (rlp_prefix_short_payload_len_code base (0x80 : Word))
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ pfx.zeroExtend 64 - (0x80 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x6 ↦ᵣ (0x80 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
  rlp_prefix_short_payload_len_spec_within (pfx.zeroExtend 64) outOld tmpOld (0x80 : Word) base

theorem rlp_prefix_short_list_payload_len_spec_within
    (pfx : Byte) (outOld tmpOld : Word) (base : Word) :
    cpsTripleWithin 2 base (base + 8) (rlp_prefix_short_payload_len_code base (0xC0 : Word))
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ pfx.zeroExtend 64 - (0xC0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x6 ↦ᵣ (0xC0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
  rlp_prefix_short_payload_len_spec_within (pfx.zeroExtend 64) outOld tmpOld (0xC0 : Word) base

theorem rlpPrefixShortBytesPayloadLen_toWord_of_class
    (pfx : Byte) (h_class : classifyPrefix pfx = .shortBytes) :
    (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx) : Word) =
      pfx.zeroExtend 64 - (0x80 : Word) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.zeroExtend_eq_setWidth]
    simp [rlpPrefixShortBytesPayloadLen_def, BitVec.toNat_setWidth]
    have h_range := (classifyPrefix_shortBytes_iff pfx).mp h_class
    omega
  · rw [BitVec.le_def]
    rw [BitVec.zeroExtend_eq_setWidth]
    simp [BitVec.toNat_setWidth]
    have h_range := (classifyPrefix_shortBytes_iff pfx).mp h_class
    omega

theorem rlpPrefixShortListPayloadLen_toWord_of_class
    (pfx : Byte) (h_class : classifyPrefix pfx = .shortList) :
    (BitVec.ofNat 64 (rlpPrefixShortListPayloadLen pfx) : Word) =
      pfx.zeroExtend 64 - (0xC0 : Word) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.zeroExtend_eq_setWidth]
    simp [rlpPrefixShortListPayloadLen_def, BitVec.toNat_setWidth]
    have h_range := (classifyPrefix_shortList_iff pfx).mp h_class
    omega
  · rw [BitVec.le_def]
    rw [BitVec.zeroExtend_eq_setWidth]
    simp [BitVec.toNat_setWidth]
    have h_range := (classifyPrefix_shortList_iff pfx).mp h_class
    omega

theorem rlp_prefix_short_bytes_payload_len_of_class_spec_within
    (pfx : Byte) (outOld tmpOld : Word) (base : Word)
    (h_class : classifyPrefix pfx = .shortBytes) :
    cpsTripleWithin 2 base (base + 8) (rlp_prefix_short_payload_len_code base (0x80 : Word))
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx) : Word)) **
        (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x6 ↦ᵣ (0x80 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  rw [rlpPrefixShortBytesPayloadLen_toWord_of_class pfx h_class]
  exact rlp_prefix_short_bytes_payload_len_spec_within pfx outOld tmpOld base

theorem rlp_prefix_short_list_payload_len_of_class_spec_within
    (pfx : Byte) (outOld tmpOld : Word) (base : Word)
    (h_class : classifyPrefix pfx = .shortList) :
    cpsTripleWithin 2 base (base + 8) (rlp_prefix_short_payload_len_code base (0xC0 : Word))
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortListPayloadLen pfx) : Word)) **
        (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x6 ↦ᵣ (0xC0 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  rw [rlpPrefixShortListPayloadLen_toWord_of_class pfx h_class]
  exact rlp_prefix_short_list_payload_len_spec_within pfx outOld tmpOld base

theorem rlpPrefixLongBytesLenOfLen_toWord_of_class
    (pfx : Byte) (h_class : classifyPrefix pfx = .longBytes) :
    (BitVec.ofNat 64 (rlpPrefixLongBytesLenOfLen pfx) : Word) =
      pfx.zeroExtend 64 - (0xB7 : Word) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.zeroExtend_eq_setWidth]
    simp [rlpPrefixLongBytesLenOfLen_def, BitVec.toNat_setWidth]
    have h_range := (classifyPrefix_longBytes_iff pfx).mp h_class
    omega
  · rw [BitVec.le_def]
    rw [BitVec.zeroExtend_eq_setWidth]
    simp [BitVec.toNat_setWidth]
    have h_range := (classifyPrefix_longBytes_iff pfx).mp h_class
    omega

theorem rlpPrefixLongListLenOfLen_toWord_of_class
    (pfx : Byte) (h_class : classifyPrefix pfx = .longList) :
    (BitVec.ofNat 64 (rlpPrefixLongListLenOfLen pfx) : Word) =
      pfx.zeroExtend 64 - (0xF7 : Word) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.zeroExtend_eq_setWidth]
    simp [rlpPrefixLongListLenOfLen_def, BitVec.toNat_setWidth]
    have h_range := (classifyPrefix_longList_iff pfx).mp h_class
    have h_bound := pfx.isLt
    omega
  · rw [BitVec.le_def]
    rw [BitVec.zeroExtend_eq_setWidth]
    simp [BitVec.toNat_setWidth]
    have h_range := (classifyPrefix_longList_iff pfx).mp h_class
    omega

theorem rlp_prefix_long_bytes_len_of_len_of_class_spec_within
    (pfx : Byte) (outOld tmpOld : Word) (base : Word)
    (h_class : classifyPrefix pfx = .longBytes) :
    cpsTripleWithin 2 base (base + 8) (rlp_prefix_short_payload_len_code base (0xB7 : Word))
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixLongBytesLenOfLen pfx) : Word)) **
        (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x6 ↦ᵣ (0xB7 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  rw [rlpPrefixLongBytesLenOfLen_toWord_of_class pfx h_class]
  exact rlp_prefix_short_payload_len_spec_within
    (pfx.zeroExtend 64) outOld tmpOld (0xB7 : Word) base

theorem rlp_prefix_long_list_len_of_len_of_class_spec_within
    (pfx : Byte) (outOld tmpOld : Word) (base : Word)
    (h_class : classifyPrefix pfx = .longList) :
    cpsTripleWithin 2 base (base + 8) (rlp_prefix_short_payload_len_code base (0xF7 : Word))
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixLongListLenOfLen pfx) : Word)) **
        (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x6 ↦ᵣ (0xF7 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  rw [rlpPrefixLongListLenOfLen_toWord_of_class pfx h_class]
  exact rlp_prefix_short_payload_len_spec_within
    (pfx.zeroExtend 64) outOld tmpOld (0xF7 : Word) base

abbrev rlp_prefix_long_header_bytes_code (base baseTag : Word) : CodeReq :=
  CodeReq.ofProg base (rlp_prefix_long_header_bytes .x5 .x10 .x6 baseTag)

/--
  Executable long-prefix header-byte helper.

  The helper computes `(pfx - baseTag) + 1`, i.e. the long length-of-length
  plus the prefix byte itself.
-/
theorem rlp_prefix_long_header_bytes_spec_within
    (pfx outOld tmpOld baseTag : Word) (base : Word) :
    cpsTripleWithin 3 base (base + 12) (rlp_prefix_long_header_bytes_code base baseTag)
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx) ** (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (pfx - baseTag) + signExtend12 (1 : BitVec 12)) ** (.x5 ↦ᵣ pfx) **
        (.x6 ↦ᵣ baseTag) ** (.x0 ↦ᵣ (0 : Word))) := by
  have I0 := li_spec_gen_within .x6 tmpOld baseTag base (by nofun)
  have I0_ext := cpsTripleWithin_extend_code
    (cr' := rlp_prefix_long_header_bytes_code base baseTag) (fun a i h => by
      simp only [CodeReq.singleton] at h
      split at h
      · next heq =>
        rw [beq_iff_eq] at heq
        rw [heq]
        simp only [Option.some.injEq] at h
        subst h
        show rlp_prefix_long_header_bytes_code base baseTag base = some (.LI .x6 baseTag)
        change CodeReq.ofProg base (.LI .x6 baseTag :: _) base = some (.LI .x6 baseTag)
        rw [CodeReq.ofProg_cons]
        simp [CodeReq.union, CodeReq.singleton]
      · simp at h) I0
  have I0_framed := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) I0_ext
  have I1 := sub_spec_gen_within .x10 .x5 .x6 pfx baseTag outOld (base + 4) (by nofun)
  have I1_ext := cpsTripleWithin_extend_code
    (cr' := rlp_prefix_long_header_bytes_code base baseTag) (fun a i h => by
      simp only [CodeReq.singleton] at h
      split at h
      · next heq =>
        rw [beq_iff_eq] at heq
        rw [heq]
        simp only [Option.some.injEq] at h
        subst h
        show rlp_prefix_long_header_bytes_code base baseTag (base + 4) =
          some (.SUB .x10 .x5 .x6)
        exact CodeReq.ofProg_lookup base
          (rlp_prefix_long_header_bytes .x5 .x10 .x6 baseTag) 1
          (by rw [rlp_prefix_long_header_bytes_length]; norm_num)
          (by rw [rlp_prefix_long_header_bytes_length]; norm_num)
      · simp at h) I1
  have I1_framed := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)))
    (by pcFree) I1_ext
  have I2 := addi_spec_gen_same_within .x10 (pfx - baseTag) (1 : BitVec 12) (base + 8) (by nofun)
  have I2_ext := cpsTripleWithin_extend_code
    (cr' := rlp_prefix_long_header_bytes_code base baseTag) (fun a i h => by
      simp only [CodeReq.singleton] at h
      split at h
      · next heq =>
        rw [beq_iff_eq] at heq
        rw [heq]
        simp only [Option.some.injEq] at h
        subst h
        show rlp_prefix_long_header_bytes_code base baseTag (base + 8) =
          some (.ADDI .x10 .x10 (1 : BitVec 12))
        exact CodeReq.ofProg_lookup base
          (rlp_prefix_long_header_bytes .x5 .x10 .x6 baseTag) 2
          (by rw [rlp_prefix_long_header_bytes_length]; norm_num)
          (by rw [rlp_prefix_long_header_bytes_length]; norm_num)
      · simp at h) I2
  have I2_framed := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ baseTag) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) I2_ext
  have ha1 : (base : Word) + 4 = base + 4 := rfl
  have ha2 : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  have ha3 : (base + 8 : Word) + 4 = base + 12 := by bv_addr
  rw [ha1] at I0_framed
  rw [ha2] at I1_framed
  rw [ha3] at I2_framed
  have H01 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) I0_framed I1_framed
  have H012 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) H01 I2_framed
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    H012

theorem rlpPrefixLongBytesHeaderBytes_toWord_of_class
    (pfx : Byte) (h_class : classifyPrefix pfx = .longBytes) :
    (BitVec.ofNat 64 (rlpPrefixLongBytesHeaderBytes pfx) : Word) =
      (pfx.zeroExtend 64 - (0xB7 : Word)) + signExtend12 (1 : BitVec 12) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by rfl]
  rw [← rlpPrefixLongBytesLenOfLen_toWord_of_class pfx h_class]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  simp [rlpPrefixLongBytesHeaderBytes]
  have h_len := rlpPrefixLongBytesLenOfLen_le_8_of_class h_class
  have h_pos := rlpPrefixLongBytesLenOfLen_pos_of_class h_class
  omega

theorem rlpPrefixLongListHeaderBytes_toWord_of_class
    (pfx : Byte) (h_class : classifyPrefix pfx = .longList) :
    (BitVec.ofNat 64 (rlpPrefixLongListHeaderBytes pfx) : Word) =
      (pfx.zeroExtend 64 - (0xF7 : Word)) + signExtend12 (1 : BitVec 12) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by rfl]
  rw [← rlpPrefixLongListLenOfLen_toWord_of_class pfx h_class]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  simp [rlpPrefixLongListHeaderBytes]
  have h_len := rlpPrefixLongListLenOfLen_le_8_of_class h_class
  have h_pos := rlpPrefixLongListLenOfLen_pos_of_class h_class
  omega

theorem rlp_prefix_long_bytes_header_bytes_of_class_spec_within
    (pfx : Byte) (outOld tmpOld : Word) (base : Word)
    (h_class : classifyPrefix pfx = .longBytes) :
    cpsTripleWithin 3 base (base + 12) (rlp_prefix_long_header_bytes_code base (0xB7 : Word))
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixLongBytesHeaderBytes pfx) : Word)) **
        (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x6 ↦ᵣ (0xB7 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  rw [rlpPrefixLongBytesHeaderBytes_toWord_of_class pfx h_class]
  exact rlp_prefix_long_header_bytes_spec_within
    (pfx.zeroExtend 64) outOld tmpOld (0xB7 : Word) base

theorem rlp_prefix_long_list_header_bytes_of_class_spec_within
    (pfx : Byte) (outOld tmpOld : Word) (base : Word)
    (h_class : classifyPrefix pfx = .longList) :
    cpsTripleWithin 3 base (base + 12) (rlp_prefix_long_header_bytes_code base (0xF7 : Word))
      ((.x6 ↦ᵣ tmpOld) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ outOld) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixLongListHeaderBytes pfx) : Word)) **
        (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x6 ↦ᵣ (0xF7 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  rw [rlpPrefixLongListHeaderBytes_toWord_of_class pfx h_class]
  exact rlp_prefix_long_header_bytes_spec_within
    (pfx.zeroExtend 64) outOld tmpOld (0xF7 : Word) base

end EvmAsm.EL.RLP
