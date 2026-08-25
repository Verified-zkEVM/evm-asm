/-
  Shared caller contract for the probe-only numeric header extractors.

  The ten routines in this file are the same eight-instruction wrapper around
  K34, differing only in the field index.  They are not linked guest symbols;
  the concrete address 0x80000000 is the documented probe conversion base.
-/

import EvmAsm.Codegen.Programs.HeaderExtractNumberSpec
import EvmAsm.Codegen.Programs.RlpFieldToU64StrictFlatSAsm
import EvmAsm.Codegen.Programs.HeaderDecode

namespace EvmAsm.Codegen.HeaderU64ExtractSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpFieldToU64StrictSAsm
open EvmAsm.Codegen.HeaderExtractNumberSpec

abbrev H : Word := (0x80000000 : Word)
abbrev Hnat : Nat := 0x80000000

def wrapperProg (index : Word) : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .MV .x13 .x12,
    .LI .x12 index,
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict (Hnat + 16)),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def wrapperCode (index : Word) : CodeReq := CodeReq.ofProg H (wrapperProg index)

def fullCode (index : Word) : CodeReq :=
  (wrapperCode index).union EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code

theorem wrapperCode_mono (index : Word) :
    ∀ a i, wrapperCode index a = some i → fullCode index a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

theorem wrapper_length (index : Word) : (wrapperProg index).length = 8 := by
  simp [wrapperProg]

theorem wrapper_disjoint (index : Word) :
    (wrapperCode index).Disjoint EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code := by
  unfold wrapperCode EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code
  refine CodeReq.Disjoint.union_right ?_
    (CodeReq.Disjoint.union_right ?_ ?_)
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.wrapperCode
      EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B H
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wrapper_length]; decide
    · rw [EvmAsm.Codegen.RlpFieldToU64StrictSAsm.program_length]; decide
    · rw [wrapper_length,
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.program_length]; decide
  · unfold EvmAsm.Codegen.RlpListNthItemSAsm.code
      EvmAsm.Codegen.RlpListNthItemSAsm.B H
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wrapper_length]; decide
    · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
    · rw [wrapper_length,
        EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.contentCode
      rlp_content_to_u64_strict_code EvmAsm.Codegen.RlpFieldToU64StrictSAsm.C64B H
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wrapper_length]; decide
    · rw [rlp_content_to_u64_strict_prog_length]; decide
    · rw [wrapper_length, rlp_content_to_u64_strict_prog_length]; decide

theorem wrapper_mono (index : Word) :
    ∀ a i, EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code a = some i →
      fullCode index a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right (wrapper_disjoint index) (fun _ _ h => h) a i hi

def uSuccess
    (sp0 spH newSp raIn listBase : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 x5 scalarStatus wrapperStatus outputValue,
    ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ sp0) **
      ((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer **
       successPayload newSp listBase offset len v12 x5 scalarStatus
         wrapperStatus outputValue saved bytes listLen index)) h

def uFailure
    (sp0 spH newSp raIn listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ v11 v12,
    ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ sp0) **
      ((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer **
       failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes
         listLen index)) h

def uPost
    (sp0 spH newSp raIn listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => uSuccess sp0 spH newSp raIn listBase outer saved bytes listLen index h ∨
    uFailure sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes listLen index h

set_option maxRecDepth 8000 in
theorem prologue
    (index : Nat)
    (sp0 raIn oldRaSlot spH newSp listBase listLenW outputPtr old13 old14
      oldOut oldOffset oldLen s0In s1In s2 s3 s4 s5 : Word)
    (outer : Saved) (bytes : List (BitVec 8))
    (houter : outer = { ra := H + 20, s0 := s0In, s1 := s1In })
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12)) :
    cpsTripleWithin 4 H (H + 16) (fullCode (BitVec.ofNat 64 index))
      (hdrPre sp0 raIn oldRaSlot spH newSp listBase listLenW outputPtr old13
        old14 oldOut oldOffset oldLen s0In s1In s2 s3 s4 s5 bytes)
      ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) **
       flatPre spH newSp listBase listLenW (BitVec.ofNat 64 index) outputPtr
         oldOut oldOffset oldLen old14 outer s2 s3 s4 s5 bytes) := by
  have h0 := addi_spec_gen_same_within .x2 sp0 (-16 : BitVec 12) H (by decide)
  rw [← hspH] at h0
  have h0' := cpsTripleWithin_extend_code (cr' := wrapperCode (BitVec.ofNat 64 index))
    (CodeReq.ofProg_mem_at H (H + 0) (wrapperProg (BitVec.ofNat 64 index)) 0
      (.ADDI .x2 .x2 (-16 : BitVec 12)) (by decide) (by simp [wrapperProg])
      rfl (by simp [wrapperProg])) h0
  have h1 := sd_spec_gen_within .x2 .x1 spH raIn oldRaSlot (0 : BitVec 12) (H + 4)
  rw [show spH + signExtend12 (0 : BitVec 12) = spH from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h1
  have h1' := cpsTripleWithin_extend_code (cr' := wrapperCode (BitVec.ofNat 64 index))
    (CodeReq.ofProg_mem_at H (H + 4) (wrapperProg (BitVec.ofNat 64 index)) 1
      (.SD .x2 .x1 (0 : BitVec 12)) (by bv_omega) (by simp [wrapperProg])
      rfl (by simp [wrapperProg])) h1
  have h2 := mv_spec_gen_within .x13 .x12 outputPtr old13 (H + 8) (by decide)
  have h2' := cpsTripleWithin_extend_code (cr' := wrapperCode (BitVec.ofNat 64 index))
    (CodeReq.ofProg_mem_at H (H + 8) (wrapperProg (BitVec.ofNat 64 index)) 2
      (.MV .x13 .x12) (by bv_omega) (by simp [wrapperProg]) rfl
      (by simp [wrapperProg])) h2
  have h3 := li_spec_gen_within .x12 outputPtr (BitVec.ofNat 64 index) (H + 12)
    (by decide)
  have h3' := cpsTripleWithin_extend_code (cr' := wrapperCode (BitVec.ofNat 64 index))
    (CodeReq.ofProg_mem_at H (H + 12) (wrapperProg (BitVec.ofNat 64 index)) 3
      (.LI .x12 (BitVec.ofNat 64 index)) (by bv_omega) (by simp [wrapperProg]) rfl
      (by simp [wrapperProg])) h3
  have h0F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ oldRaSlot) ** (.x12 ↦ᵣ outputPtr) **
      (.x13 ↦ᵣ old13)) (by pcf) h0'
  have h1F := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ outputPtr) ** (.x13 ↦ᵣ old13)) (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn)) (by pcf) h2'
  have h3F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) **
      (.x13 ↦ᵣ outputPtr)) (by pcf) h3'
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2F
  have h0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 h3F
  have hlocal : cpsTripleWithin 4 H (H + 16)
      (wrapperCode (BitVec.ofNat 64 index))
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (spH ↦ₘ oldRaSlot) **
        (.x12 ↦ᵣ outputPtr) ** (.x13 ↦ᵣ old13))
      ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 index)) ** (.x13 ↦ᵣ outputPtr)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0123
  have hframed := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ s0In) ** (.x9 ↦ᵣ s1In) ** frameSlotsOwn frame newSp **
      stackFree newSp 8 ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
      (.x14 ↦ᵣ old14) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
      (outputPtr ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) **
      (lengthCell ↦ₘ oldLen)) (by pcf) hlocal
  have hall := cpsTripleWithin_extend_code (cr' := fullCode (BitVec.ofNat 64 index))
    (wrapperCode_mono (BitVec.ofNat 64 index)) hframed
  subst houter
  refine cpsTripleWithin_weaken (fun h hp => by unfold hdrPre at hp; xperm_hyp hp)
    (fun h hq => by unfold flatPre wholeRest; xperm_hyp hq) hall

set_option maxRecDepth 8000 in
theorem epiCore (index : Nat) (sp0 spH raIn : Word) (G : Assertion) (hG : G.pcFree)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 3 (H + 20) raIn (fullCode (BitVec.ofNat 64 index))
      ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ spH) ** G)
      ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ sp0) ** G) := by
  have h5 := ld_spec_gen_within .x1 .x2 spH (H + 20) raIn (0 : BitVec 12) (H + 20)
    (by decide)
  rw [show spH + signExtend12 (0 : BitVec 12) = spH from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h5
  have h5' := cpsTripleWithin_extend_code (wrapperCode_mono (BitVec.ofNat 64 index))
    (cpsTripleWithin_extend_code (cr' := wrapperCode (BitVec.ofNat 64 index))
      (CodeReq.ofProg_mem_at H (H + 20) (wrapperProg (BitVec.ofNat 64 index)) 5
        (.LD .x1 .x2 (0 : BitVec 12)) (by bv_omega) (by simp [wrapperProg]) rfl
        (by simp [wrapperProg])) h5)
  have h6 := addi_spec_gen_same_within .x2 spH (16 : BitVec 12) (H + 24) (by decide)
  rw [show spH + signExtend12 (16 : BitVec 12) = sp0 from by
    rw [hspH]; exact sext_frameRestore sp0 (-16 : BitVec 12) (16 : BitVec 12) (by decide)] at h6
  have h6' := cpsTripleWithin_extend_code (wrapperCode_mono (BitVec.ofNat 64 index))
    (cpsTripleWithin_extend_code (cr' := wrapperCode (BitVec.ofNat 64 index))
      (CodeReq.ofProg_mem_at H (H + 24) (wrapperProg (BitVec.ofNat 64 index)) 6
        (.ADDI .x2 .x2 (16 : BitVec 12)) (by bv_omega) (by simp [wrapperProg]) rfl
        (by simp [wrapperProg])) h6)
  have h7 := EvmAsm.Evm64.ret_spec_within' (H + 28) raIn
  rw [hret] at h7
  have h7' := cpsTripleWithin_extend_code (wrapperCode_mono (BitVec.ofNat 64 index))
    (cpsTripleWithin_extend_code (cr' := wrapperCode (BitVec.ofNat 64 index))
      (CodeReq.ofProg_mem_at H (H + 28) (wrapperProg (BitVec.ofNat 64 index)) 7
        (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega) (by simp [wrapperProg]) rfl
        (by simp [wrapperProg])) h7)
  have h6F := cpsTripleWithin_frameR ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn)) (by pcf) h6'
  have h7F := cpsTripleWithin_frameR ((.x2 ↦ᵣ sp0) ** (spH ↦ₘ raIn)) (by pcf) h7'
  have h56 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h5' h6F
  have h567 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h56 h7F
  have hcore : cpsTripleWithin 3 (H + 20) raIn (fullCode (BitVec.ofNat 64 index))
      ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn))
      ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (spH ↦ₘ raIn)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h567
  have hframed := cpsTripleWithin_frameR G hG hcore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hframed

set_option maxRecDepth 8000 in
theorem epilogue (index : Nat)
    (sp0 spH newSp raIn listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 3 (H + 20) raIn (fullCode (BitVec.ofNat 64 index))
      ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) **
       flatPost spH newSp listBase oldOffset oldLen outer saved bytes listLen index)
      (uPost sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes listLen index) := by
  have hS : cpsTripleWithin 3 (H + 20) raIn (fullCode (BitVec.ofNat 64 index))
      (fun h => ∃ offset len v12 x5 ss ws ov,
        ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) **
          (((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
            savedFrame newSp outer) **
           successPayload newSp listBase offset len v12 x5 ss ws ov saved bytes listLen index)) h)
      (uPost sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes listLen index) := by
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun offset => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun len => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v12 => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun x5 => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun ss => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun ws => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun ov => ?_)
    have hc := epiCore index sp0 spH raIn
      ((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer **
        successPayload newSp listBase offset len v12 x5 ss ws ov saved bytes listLen index)
      (by unfold savedFrame successPayload; pcf) hspH hret
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => ?_) hc
    exact Or.inl ⟨offset, len, v12, x5, ss, ws, ov, by xperm_hyp hq⟩
  have hF : cpsTripleWithin 3 (H + 20) raIn (fullCode (BitVec.ofNat 64 index))
      (fun h => ∃ v11 v12,
        ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) **
          (((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
            savedFrame newSp outer) **
           failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes listLen index)) h)
      (uPost sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes listLen index) := by
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v11 => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v12 => ?_)
    have hc := epiCore index sp0 spH raIn
      ((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer **
        failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes listLen index)
      (by unfold savedFrame failurePayload; pcf) hspH hret
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => ?_) hc
    exact Or.inr ⟨v11, v12, by xperm_hyp hq⟩
  have hor := cpsTripleWithin_pre_or hS hF
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) hor
  unfold flatPost at hp
  have hinner := sepConj_mono_right
    (fun h' (hh : ((spH ↦ₘ raIn) **
        (fun h'' => flatSuccessReturned spH newSp listBase outer saved bytes listLen index h'' ∨
          flatFailureReturned spH newSp listBase oldOffset oldLen outer saved bytes listLen index h'')) h') =>
      sepConj_or_split h' hh) h hp
  rcases sepConj_or_split h hinner with hs | hf
  · unfold flatSuccessReturned at hs
    obtain ⟨h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hsp,
      ⟨offset, len, v12, x5, ss, ws, ov, hinner⟩⟩ := hs
    exact Or.inl ⟨offset, len, v12, x5, ss, ws, ov,
      h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hsp, hinner⟩
  · unfold flatFailureReturned at hf
    obtain ⟨h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hsp,
      ⟨v11, v12, hinner⟩⟩ := hf
    exact Or.inr ⟨v11, v12, h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hsp, hinner⟩

set_option maxRecDepth 8000 in
theorem header_u64_spec_within (index : Nat)
    (sp0 raIn oldRaSlot spH newSp listBase listLenW outputPtr old13 old14
      oldOut oldOffset oldLen s0In s1In s2 s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hnewSp : newSp = spH + signExtend12 (-32 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hbytes : listLen ≤ bytes.length)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    let outer : Saved := { ra := H + 20, s0 := s0In, s1 := s1In }
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    let n34 := (7 + 4 + callSteps) + ((1 + tailSteps) + 5)
    cpsTripleWithin (4 + (1 + n34) + 3) H raIn (fullCode (BitVec.ofNat 64 index))
      (hdrPre sp0 raIn oldRaSlot spH newSp listBase listLenW outputPtr old13
        old14 oldOut oldOffset oldLen s0In s1In s2 s3 s4 s5 bytes)
      (uPost sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes listLen index) := by
  intro outer saved callSteps tailSteps n34
  have hpro := prologue index sp0 raIn oldRaSlot spH newSp listBase listLenW outputPtr
    old13 old14 oldOut oldOffset oldLen s0In s1In s2 s3 s4 s5 outer bytes rfl hspH
  have hflat := rlpFieldToU64_flat_spec_within spH newSp listBase listLenW
    (BitVec.ofNat 64 index) outputPtr oldOut oldOffset oldLen old14 outer s2 s3 s4 s5 bytes
    listLen index hnewSp hlistLenW rfl hindex hsalign hbytes hnowrap hover hvalid hnz
    (by show (H + 20) &&& ~~~(1 : Word) = H + 20; decide)
  have hflatC := cpsTripleWithin_extend_code (wrapper_mono (BitVec.ofNat 64 index)) hflat
  have hflatF := cpsTripleWithin_frameR (spH ↦ₘ raIn) (by pcf) hflatC
  have hcallee : cpsTripleWithin n34 B (H + 20) (fullCode (BitVec.ofNat 64 index))
      ((.x1 ↦ᵣ (H + 20)) **
        (flatPre spH newSp listBase listLenW (BitVec.ofNat 64 index) outputPtr oldOut
          oldOffset oldLen old14 outer s2 s3 s4 s5 bytes ** (spH ↦ₘ raIn)))
      ((.x1 ↦ᵣ (H + 20)) **
        (flatPost spH newSp listBase oldOffset oldLen outer saved bytes listLen index **
          (spH ↦ₘ raIn))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hflatF
  have hcall := callWithin_spec (H + 16) B raIn
    (jalOff GuestAddrs.rlp_field_to_u64_strict (Hnat + 16)) n34 (by
      change (H + 16) + signExtend21 (jalOff GuestAddrs.rlp_field_to_u64_strict (Hnat + 16)) =
        BitVec.ofNat 64 GuestAddrs.rlp_field_to_u64_strict
      exact jalOff_correct_add GuestAddrs.rlp_field_to_u64_strict Hnat 16
        (by decide) (by decide) (by decide) (by decide))
    (fun a i hi => wrapperCode_mono (BitVec.ofNat 64 index) a i
      (CodeReq.ofProg_mem_at H (H + 16) (wrapperProg (BitVec.ofNat 64 index)) 4
        (.JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict (Hnat + 16)))
        (by bv_omega) (by rw [wrapper_length]; decide) rfl (by rw [wrapper_length]; decide) a i hi))
    (by unfold flatPre wholeRest; pcf) hcallee
  rw [show (H + 16 + 4 : Word) = H + 20 from by bv_omega] at hcall
  have hcall' : cpsTripleWithin (1 + n34) (H + 16) (H + 20)
      (fullCode (BitVec.ofNat 64 index))
      ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) **
        flatPre spH newSp listBase listLenW (BitVec.ofNat 64 index) outputPtr oldOut
          oldOffset oldLen old14 outer s2 s3 s4 s5 bytes)
      ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) **
        flatPost spH newSp listBase oldOffset oldLen outer saved bytes listLen index) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcall
  have hepi := epilogue index sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes
    listLen hspH hret
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hpro hcall'
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) h01 hepi

/-! The concrete probe-only wrappers all share the theorem above; these aliases
    bind each emitted symbol to its field index for the routine registry. -/

abbrev header_extract_basefee_spec_within := @header_u64_spec_within 15
abbrev header_extract_base_fee_u64_spec_within := @header_u64_spec_within 15
abbrev header_extract_base_fee_u64_bh_spec_within := @header_u64_spec_within 15
abbrev header_extract_blob_gas_used_spec_within := @header_u64_spec_within 17
abbrev header_extract_difficulty_spec_within := @header_u64_spec_within 7
abbrev header_extract_excess_blob_gas_spec_within := @header_u64_spec_within 18
abbrev header_extract_gas_limit_spec_within := @header_u64_spec_within 9
abbrev header_extract_gas_used_spec_within := @header_u64_spec_within 10
abbrev header_extract_timestamp_spec_within := @header_u64_spec_within 11

/-! ## Production header decoder segment

The probe wrappers above are deliberately retained as a model-level proof of
the strict field contract, but they are not linked guest entries.  The linked
Amsterdam decoder calls `rlp_content_to_u64_strict` directly from
`headerExtendedDecode_prog`.  The small segment theorem below is the bridge
for those call sites: it covers the two register shuffles emitted immediately
before each direct call (`sub x10,x10,x12; mv x11,x12`) and then composes the
verified scalar callee.  It is parameterised by the caller `CodeReq`, so a
whole-decoder proof can frame the remaining walk state without pretending that
the six sites are standalone routines.

The six direct sites are at offsets +324, +364, +404, +444, +604 and +644.
They decode fields 8, 9, 10, 11, 17 and 18 respectively.  Field 15 is decoded
by the distinct u256 routine at +548; difficulty (field 7) is handled by the
post-merge validator rather than a strict-u64 call.  Thus the three field-15
aliases and the field-7 alias above are not silently claimed by this segment
theorem.
-/

abbrev headerExtendedDecodeBase : Word :=
  (GuestAddrs.header_extended_decode : Word)
abbrev headerExtendedDecodeContentBase : Word :=
  (GuestAddrs.rlp_content_to_u64_strict : Word)

def headerExtendedDecodeCode : CodeReq :=
  CodeReq.ofProg headerExtendedDecodeBase headerExtendedDecode_prog

def headerExtendedDecodeU64Code : CodeReq :=
  headerExtendedDecodeCode.union
    (rlp_content_to_u64_strict_code headerExtendedDecodeContentBase)

private theorem headerExtendedDecodeU64Code_mem
    (a : Word) (i : Instr) (h : headerExtendedDecodeCode a = some i) :
    headerExtendedDecodeU64Code a = some i := by
  unfold headerExtendedDecodeU64Code
  exact CodeReq.union_mono_left a i h

private theorem headerExtendedDecodeU64Code_callee_mem
    (a : Word) (i : Instr)
    (h : rlp_content_to_u64_strict_code headerExtendedDecodeContentBase a = some i) :
    headerExtendedDecodeU64Code a = some i := by
  unfold headerExtendedDecodeU64Code
  exact CodeReq.mono_union_right (by
    unfold headerExtendedDecodeCode rlp_content_to_u64_strict_code
      headerExtendedDecodeBase headerExtendedDecodeContentBase
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [headerExtendedDecode_prog_length]
      decide
    · rw [rlp_content_to_u64_strict_prog_length]
      decide
    · rw [headerExtendedDecode_prog_length,
        rlp_content_to_u64_strict_prog_length]
      decide) (fun _ _ h' => h') a i h

/- set_option maxRecDepth 8000 in
theorem header_extended_decode_u64_segment_spec_within
    (A calleeEntry srcBase srcEnd len raIn old11 t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (cr : CodeReq)
    (hsub : srcEnd - len = srcBase)
    (hlen64 : len.toNat < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcBytes.length ≥ len.toNat)
    (hsover : srcBase.toNat + len.toNat ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len.toNat →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (hcalleeEntry : calleeEntry = headerExtendedDecodeContentBase)
    (hsub_mem : ∀ a i,
      CodeReq.singleton A (.SUB .x10 .x10 .x12) a = some i → cr a = some i)
    (hmv_mem : ∀ a i,
      CodeReq.singleton (A + 4) (.MV .x11 .x12) a = some i → cr a = some i)
    (hjal_mem : ∀ a i,
      CodeReq.singleton (A + 8)
        (.JAL .x1 (jalOff calleeEntry (A + 12))) a = some i → cr a = some i)
    (hcallee_mem : ∀ a i,
      rlp_content_to_u64_strict_code calleeEntry a = some i → cr a = some i) :
    cpsTripleWithin (3 + (7 * len.toNat + 11)) A (A + 12) cr
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcEnd) ** (.x11 ↦ᵣ old11) **
       (.x12 ↦ᵣ len) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) **
       (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      (((.x1 ↦ᵣ (A + 12)) ** (.x12 ↦ᵣ len)) **
       ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        (fun h =>
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) **
             ⌜8 < len.toNat⌝) h) ∨
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
             ⌜len.toNat = 0⌝) h) ∨
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
             ⌜0 < len.toNat ∧ len.toNat ≤ 8 ∧
               getByteAt srcBytes 0 = 0⌝) h) ∨
          (((.x10 ↦ᵣ BitVec.ofNat 64
               (Nat.fromBytesBE (srcBytes.take len.toNat))) **
             (.x11 ↦ᵣ (0 : Word)) **
             ⌜0 < len.toNat ∧ len.toNat ≤ 8 ∧
               getByteAt srcBytes 0 ≠ 0⌝) h)))) := by
  have hsub_spec := sub_spec_gen_rd_eq_rs1_within .x10 .x12 srcEnd len A
    (by decide)
  rw [hsub] at hsub_spec
  have hsub_code := cpsTripleWithin_extend_code hsub_mem hsub_spec
  have hsub_frame := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ len) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion srcBase srcBytes) (by pcf) hsub_code
  have hmv_spec := mv_spec_gen_within .x11 .x12 len old11 (A + 4)
    (by decide)
  have hmv_code := cpsTripleWithin_extend_code hmv_mem hmv_spec
  have hmv_frame := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcBase) ** (.x12 ↦ᵣ len) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion srcBase srcBytes) (by pcf) hmv_code
  have hcallee0 := rlp_content_to_u64_strict_spec_within
    calleeEntry srcBase (A + 12) t0Old x6Old t2Old t3Old srcBytes 0 len.toNat
      (by simpa using hlen64) hsalign (by omega) hsover (by
        simpa using hsvalid)
  have hcallee1 := cpsTripleWithin_extend_code hcallee_mem hcallee0
  have hcallee : cpsTripleWithin (7 * len.toNat + 11) calleeEntry (A + 12) cr
      (((.x1 ↦ᵣ (A + 12)) ** (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ len) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes))
      (((.x1 ↦ᵣ (A + 12)) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)) **
       (fun h =>
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) **
             ⌜8 < len.toNat⌝) h) ∨
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
             ⌜len.toNat = 0⌝) h) ∨
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
             ⌜0 < len.toNat ∧ len.toNat ≤ 8 ∧
               getByteAt srcBytes 0 = 0⌝) h) ∨
          (((.x10 ↦ᵣ BitVec.ofNat 64
               (Nat.fromBytesBE (srcBytes.take len.toNat))) **
             (.x11 ↦ᵣ (0 : Word)) **
             ⌜0 < len.toNat ∧ len.toNat ≤ 8 ∧
               getByteAt srcBytes 0 ≠ 0⌝) h))) := by
    simpa [hcalleeEntry] using hcallee1
  have hcall := callWithin_spec A calleeEntry raIn
    (jalOff calleeEntry (A + 12)) (7 * len.toNat + 11)
    (by rw [hcalleeEntry]; exact jalOff_correct_add
      GuestAddrs.rlp_content_to_u64_strict (A + 12)
      (by decide) (by decide) (by decide) (by decide))
    hjal_mem (by pcf) hcallee
  have hcall' := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ len)) (by pcf) hcall
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsub_frame hmv_frame
  have h012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h01 hcall'
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h012 -/

set_option maxRecDepth 8000 in
theorem header_extended_decode_u64_segment_spec_within
    (A calleeEntry srcBase srcEnd len raIn old11 : Word)
    (jal : BitVec 21) (n : Nat) (R Q : Assertion) (cr : CodeReq)
    (hsub : srcEnd - len = srcBase)
    (hjal : A + 8 + signExtend21 jal = calleeEntry)
    (hsub_mem : ∀ a i,
      CodeReq.singleton A (.SUB .x10 .x10 .x12) a = some i → cr a = some i)
    (hmv_mem : ∀ a i,
      CodeReq.singleton (A + 4) (.MV .x11 .x12) a = some i → cr a = some i)
    (hjal_mem : ∀ a i,
      CodeReq.singleton (A + 8) (.JAL .x1 jal) a = some i → cr a = some i)
    (hR : R.pcFree)
    (hcallee : cpsTripleWithin n calleeEntry (A + 12) cr
      (((.x1 ↦ᵣ (A + 12)) ** (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ len) ** R))
      (((.x1 ↦ᵣ (A + 12)) ** Q))) :
    cpsTripleWithin (3 + n) A (A + 12) cr
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcEnd) ** (.x11 ↦ᵣ old11) **
        (.x12 ↦ᵣ len) ** R)
      (((.x1 ↦ᵣ (A + 12)) ** (.x12 ↦ᵣ len) ** Q)) := by
  have hsub_spec := sub_spec_gen_rd_eq_rs1_within .x10 .x12 srcEnd len A
    (by decide)
  rw [hsub] at hsub_spec
  have hsub_code := cpsTripleWithin_extend_code hsub_mem hsub_spec
  have hsub_frame := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ old11) ** R)
    (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) hR)) hsub_code
  have hmv_spec := mv_spec_gen_within .x11 .x12 len old11 (A + 4)
    (by decide)
  have hmv_code := cpsTripleWithin_extend_code hmv_mem hmv_spec
  have hmv_frame := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcBase) ** R)
    (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) hR)) hmv_code
  have hadd4 : A + 4 + 4 = A + 8 := by
    rw [BitVec.add_assoc]
    simp
  have hadd8 : A + 8 + 4 = A + 12 := by
    rw [BitVec.add_assoc]
    simp
  have hcallee' : cpsTripleWithin n calleeEntry (A + 8 + 4) cr
      (((.x1 ↦ᵣ (A + 8 + 4)) ** (.x10 ↦ᵣ srcBase) **
        (.x11 ↦ᵣ len) ** R))
      (((.x1 ↦ᵣ (A + 8 + 4)) ** Q)) := by
    rw [BitVec.add_assoc]
    simpa using hcallee
  have hcall := callWithin_spec (A + 8) calleeEntry raIn jal n hjal hjal_mem
    (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) hR)) hcallee'
  have hcall' := cpsTripleWithin_frameR (.x12 ↦ᵣ len) (by pcf) hcall
  /- have hmv_frame' : cpsTripleWithin 1 (A + 4) (A + 8) cr
      (((.x12 ↦ᵣ len) ** (.x11 ↦ᵣ old11)) **
        (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcBase) ** R)
      (((.x12 ↦ᵣ len) ** (.x11 ↦ᵣ len)) **
        (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcBase) ** R) := by
    rw [BitVec.add_assoc]
    simpa using hmv_frame
  have hcall'' : cpsTripleWithin (1 + n) (A + 8) (A + 12) cr
      (((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ len) ** R) **
        (.x12 ↦ᵣ len))
      (((.x1 ↦ᵣ (A + 12)) ** Q) ** (.x12 ↦ᵣ len)) := by
    rw [BitVec.add_assoc]
    simpa using hcall'
  -/
  rw [hadd4] at hmv_frame
  rw [hadd8] at hcall'
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsub_frame hmv_frame
  have h012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h01 hcall'
  have hweak := cpsTripleWithin_weaken
    (P := (((.x10 ↦ᵣ srcEnd) ** (.x12 ↦ᵣ len)) **
      (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ old11) ** R))
    (P' := ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcEnd) ** (.x11 ↦ᵣ old11) **
      (.x12 ↦ᵣ len) ** R))
    (Q := ((.x1 ↦ᵣ (A + 12)) ** Q) ** (.x12 ↦ᵣ len))
    (Q' := ((.x1 ↦ᵣ (A + 12)) ** (.x12 ↦ᵣ len) ** Q))
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h012
  exact cpsTripleWithin_mono_nSteps (by omega) hweak

/- The six concrete call offsets in `headerExtendedDecode_prog`; these guards
   make the re-anchor check executable and keep every segment tied to the
   linked Program rather than to a copied instruction list. -/
example : (show List Instr from headerExtendedDecode_prog)[81]? =
    some (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 324))) := by decide
example : (show List Instr from headerExtendedDecode_prog)[91]? =
    some (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 364))) := by decide
example : (show List Instr from headerExtendedDecode_prog)[101]? =
    some (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 404))) := by decide
example : (show List Instr from headerExtendedDecode_prog)[111]? =
    some (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 444))) := by decide
example : (show List Instr from headerExtendedDecode_prog)[151]? =
    some (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 604))) := by decide
example : (show List Instr from headerExtendedDecode_prog)[161]? =
    some (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 644))) := by decide

/-! ## Anchored, callee-composed contracts for the six direct u64 call sites

    `header_extended_decode_u64_segment_spec_within` above is deliberately
    parameterised: `A` is a free `Word`, `cr` is a free `CodeReq` constrained
    only by three singleton memberships, and the callee's contract arrives as
    the hypothesis `hcallee`.  That is the right shape for a *reusable* segment
    lemma and the wrong shape for *evidence*: nothing in it says the three
    instructions are the ones the linked image holds at
    `GuestAddrs.header_extended_decode`, and nothing in it discharges the call.

    The six theorems below close both gaps.  For each direct
    `rlp_content_to_u64_strict` site they instantiate

    * `A := headerExtendedDecodeBase + 4*k` for the site's real instruction
      index `k` (79, 89, 99, 109, 149, 159 — the `SUB`),
    * `cr := headerExtendedDecodeU64Code`, the union of the linked decoder
      image with the linked callee image, so `hsub_mem`/`hmv_mem`/`hjal_mem`
      become facts about `headerExtendedDecode_prog` discharged through
      `CodeReq.ofProg_mem_at` (with the instruction identities `rfl`-checked
      against the Program, not copied),
    * `hcallee := rlp_content_to_u64_strict_spec_within` at
      `headerExtendedDecodeContentBase`, i.e. **composed, not assumed**.

    What is still owned elsewhere: these are the 3-instruction call segments,
    not the 174-instruction routine.  The whole-decoder triple (#12799 row 6)
    additionally owns the walk, the two 32-byte copy loops, the status
    branches and the frame; it will consume these six as its u64 call-site
    obligations. -/

/-- Registers the callee may clobber, plus the read-only content buffer:
    `t0 t1 t2 t3` (`x5 x6 x7 x28`), `x0`, and `bytesRegion srcBase srcBytes`.
    Every entry was read off the disassembled `rlp_content_to_u64_strict`
    listing at `GuestAddrs.rlp_content_to_u64_strict`, not off the source. -/
abbrev u64SiteFrame (srcBase t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) : Assertion :=
  (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes

/-- Precondition of one direct call site: `a0` still holds the walker's
    `next` cursor (`srcEnd`), `a2` the item length, `a1` whatever the walker
    left there, `ra` the caller's return address, plus `u64SiteFrame`. -/
abbrev u64SitePre (srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (len : Nat) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcEnd) ** (.x11 ↦ᵣ old11) **
    (.x12 ↦ᵣ BitVec.ofNat 64 len) **
    u64SiteFrame srcBase t0Old x6Old t2Old t3Old srcBytes

/-- The callee's own four-way outcome, carried through the site unchanged:
    `a1 = 2` (too long) / `a1 = 0, a0 = 0` (empty, canonical zero) /
    `a1 = 3` (leading zero) / `a1 = 0, a0 = fromBytesBE content`. -/
abbrev u64SiteOutcome (srcBase : Word) (srcBytes : List (BitVec 8))
    (len : Nat) : Assertion :=
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
    (fun h =>
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
         ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes 0 = 0⌝) h) ∨
      (((.x10 ↦ᵣ BitVec.ofNat 64
           (EvmAsm.EL.RLP.Nat.fromBytesBE (srcBytes.take len))) **
         (.x11 ↦ᵣ (0 : Word)) **
         ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes 0 ≠ 0⌝) h))

/-- Postcondition of one direct call site: `ra` points at the return address
    the `JAL` installed, `a2` is preserved, and the callee's outcome holds. -/
abbrev u64SitePost (A srcBase : Word) (srcBytes : List (BitVec 8))
    (len : Nat) : Assertion :=
  (.x1 ↦ᵣ (A + 12)) ** (.x12 ↦ᵣ BitVec.ofNat 64 len) **
    u64SiteOutcome srcBase srcBytes len

/-- `k < 174` as a bound on `headerExtendedDecode_prog.length`, routed through
    the named length theorem.  `by decide` on the goal directly re-elaborates
    the 174-element `Instr` list and exhausts the recursion budget. -/
private theorem headerExtendedDecode_index_lt (k : Nat) (h : k < 174) :
    k < headerExtendedDecode_prog.length := by
  rw [headerExtendedDecode_prog_length]; exact h

/-- Instruction `k` of the **linked** decoder Program is in the union
    `CodeReq` the six site theorems run under.  `hins` is discharged by `rfl`
    against `headerExtendedDecode_prog` at each site, so no instruction is
    ever transcribed by hand. -/
private theorem headerExtendedDecode_mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = headerExtendedDecodeBase + BitVec.ofNat 64 (4 * k))
    (hk : k < headerExtendedDecode_prog.length)
    (hins : headerExtendedDecode_prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i →
      headerExtendedDecodeU64Code a = some i :=
  fun a i h => headerExtendedDecodeU64Code_mem a i
    (CodeReq.ofProg_mem_at headerExtendedDecodeBase A headerExtendedDecode_prog
      k ins hA hk hins
      (by rw [headerExtendedDecode_prog_length]; decide) a i h)

/--
**The composition step.**  One direct `rlp_content_to_u64_strict` call site of
the linked decoder, over the linked `CodeReq`, with the callee's whole-routine
four-arm contract *discharged* rather than assumed.

This is `header_extended_decode_u64_segment_spec_within` with
`cr := headerExtendedDecodeU64Code`, `calleeEntry := headerExtendedDecodeContentBase`
and `hcallee` supplied from `EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_spec_within`.
The six site theorems below differ from it only in `A`, and in `A` being
concrete.

`hra` (`(A+12) &&& ~~~1 = A+12`) is the callee's `ra`-alignment side condition;
it is `decide`-checked at each concrete site, where `A + 12` is a real
instruction address and therefore 4-aligned.
-/
theorem header_extended_decode_u64_site_composed_within
    (A srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (len : Nat) (jal : BitVec 21)
    (hsub : srcEnd - BitVec.ofNat 64 len = srcBase)
    (hjal : A + 8 + signExtend21 jal = headerExtendedDecodeContentBase)
    (hra : (A + 12) &&& ~~~1 = A + 12)
    (hsub_mem : ∀ a i, CodeReq.singleton A (.SUB .x10 .x10 .x12) a = some i →
      headerExtendedDecodeU64Code a = some i)
    (hmv_mem : ∀ a i, CodeReq.singleton (A + 4) (.MV .x11 .x12) a = some i →
      headerExtendedDecodeU64Code a = some i)
    (hjal_mem : ∀ a i, CodeReq.singleton (A + 8) (.JAL .x1 jal) a = some i →
      headerExtendedDecodeU64Code a = some i)
    (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : len ≤ srcBytes.length)
    (hsover : srcBase.toNat + len ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (3 + (7 * len + 11)) A (A + 12) headerExtendedDecodeU64Code
      (u64SitePre srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old srcBytes len)
      (u64SitePost A srcBase srcBytes len) := by
  have hc0 := rlp_content_to_u64_strict_spec_within
    headerExtendedDecodeContentBase srcBase (A + 12) t0Old x6Old t2Old t3Old
    srcBytes 0 len hlen64 hsalign (by omega) (by omega)
    (by simpa using hsvalid)
  rw [hra] at hc0
  simp only [List.drop_zero, BitVec.add_zero] at hc0
  have hc1 := cpsTripleWithin_extend_code
    headerExtendedDecodeU64Code_callee_mem hc0
  have hcallee : cpsTripleWithin (7 * len + 11) headerExtendedDecodeContentBase
      (A + 12) headerExtendedDecodeU64Code
      ((.x1 ↦ᵣ (A + 12)) ** (.x10 ↦ᵣ srcBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        u64SiteFrame srcBase t0Old x6Old t2Old t3Old srcBytes)
      ((.x1 ↦ᵣ (A + 12)) ** u64SiteOutcome srcBase srcBytes len) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hc1
  exact header_extended_decode_u64_segment_spec_within A
    headerExtendedDecodeContentBase srcBase srcEnd (BitVec.ofNat 64 len) raIn
    old11 jal (7 * len + 11)
    (u64SiteFrame srcBase t0Old x6Old t2Old t3Old srcBytes)
    (u64SiteOutcome srcBase srcBytes len) headerExtendedDecodeU64Code
    hsub hjal hsub_mem hmv_mem hjal_mem (by pcf) hcallee

/-! ### The six sites

    Each `A` is the `SUB` of the site, i.e. the `JAL` offset minus 8; the
    `JAL`'s own offset is the one the live `example` guards above pin. -/

/-- Direct u64 site at `+324` (`SUB` at index 79, `JAL` at index 81), whose
    result the decoder stores at `out + 64` (`SD x18, x10, 64` at index 83).
    Header field **8** (`number`) by the outward-call census below — NOT field
    9, which the registry rows say; see that note. -/
theorem header_extended_decode_u64_site_324_spec_within
    (srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (len : Nat)
    (hsub : srcEnd - BitVec.ofNat 64 len = srcBase)
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : len ≤ srcBytes.length) (hsover : srcBase.toNat + len ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (3 + (7 * len + 11))
      (headerExtendedDecodeBase + BitVec.ofNat 64 316)
      (headerExtendedDecodeBase + BitVec.ofNat 64 316 + 12)
      headerExtendedDecodeU64Code
      (u64SitePre srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old srcBytes len)
      (u64SitePost (headerExtendedDecodeBase + BitVec.ofNat 64 316) srcBase
        srcBytes len) :=
  header_extended_decode_u64_site_composed_within _ srcBase srcEnd raIn old11
    t0Old x6Old t2Old t3Old srcBytes len
    (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 324))
    hsub (by decide) (by decide)
    (headerExtendedDecode_mem_at 79 _ _ (by decide) (headerExtendedDecode_index_lt 79 (by decide)) rfl)
    (headerExtendedDecode_mem_at 80 _ _ (by decide) (headerExtendedDecode_index_lt 80 (by decide)) rfl)
    (headerExtendedDecode_mem_at 81 _ _ (by decide) (headerExtendedDecode_index_lt 81 (by decide)) rfl)
    hlen64 hsalign hslen hsover hsvalid


/-- Direct u64 site at `+364` (`SUB` at index 89, `JAL` at index 91), whose
    result the decoder stores at `out + 80` (`SD x18, x10, 80` at index 93).
    Header field **9** (`gas_limit`) by the outward-call census below. -/
theorem header_extended_decode_u64_site_364_spec_within
    (srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (len : Nat)
    (hsub : srcEnd - BitVec.ofNat 64 len = srcBase)
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : len ≤ srcBytes.length) (hsover : srcBase.toNat + len ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (3 + (7 * len + 11))
      (headerExtendedDecodeBase + BitVec.ofNat 64 356)
      (headerExtendedDecodeBase + BitVec.ofNat 64 356 + 12)
      headerExtendedDecodeU64Code
      (u64SitePre srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old srcBytes len)
      (u64SitePost (headerExtendedDecodeBase + BitVec.ofNat 64 356) srcBase
        srcBytes len) :=
  header_extended_decode_u64_site_composed_within _ srcBase srcEnd raIn old11
    t0Old x6Old t2Old t3Old srcBytes len
    (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 364))
    hsub (by decide) (by decide)
    (headerExtendedDecode_mem_at 89 _ _ (by decide)
      (headerExtendedDecode_index_lt 89 (by decide)) rfl)
    (headerExtendedDecode_mem_at 90 _ _ (by decide)
      (headerExtendedDecode_index_lt 90 (by decide)) rfl)
    (headerExtendedDecode_mem_at 91 _ _ (by decide)
      (headerExtendedDecode_index_lt 91 (by decide)) rfl)
    hlen64 hsalign hslen hsover hsvalid

/-- Direct u64 site at `+404` (`SUB` at index 99, `JAL` at index 101), whose
    result the decoder stores at `out + 88` (`SD x18, x10, 88` at index 103).
    Header field **10** (`gas_used`) by the outward-call census below. -/
theorem header_extended_decode_u64_site_404_spec_within
    (srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (len : Nat)
    (hsub : srcEnd - BitVec.ofNat 64 len = srcBase)
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : len ≤ srcBytes.length) (hsover : srcBase.toNat + len ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (3 + (7 * len + 11))
      (headerExtendedDecodeBase + BitVec.ofNat 64 396)
      (headerExtendedDecodeBase + BitVec.ofNat 64 396 + 12)
      headerExtendedDecodeU64Code
      (u64SitePre srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old srcBytes len)
      (u64SitePost (headerExtendedDecodeBase + BitVec.ofNat 64 396) srcBase
        srcBytes len) :=
  header_extended_decode_u64_site_composed_within _ srcBase srcEnd raIn old11
    t0Old x6Old t2Old t3Old srcBytes len
    (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 404))
    hsub (by decide) (by decide)
    (headerExtendedDecode_mem_at 99 _ _ (by decide)
      (headerExtendedDecode_index_lt 99 (by decide)) rfl)
    (headerExtendedDecode_mem_at 100 _ _ (by decide)
      (headerExtendedDecode_index_lt 100 (by decide)) rfl)
    (headerExtendedDecode_mem_at 101 _ _ (by decide)
      (headerExtendedDecode_index_lt 101 (by decide)) rfl)
    hlen64 hsalign hslen hsover hsvalid

/-- Direct u64 site at `+444` (`SUB` at index 109, `JAL` at index 111), whose
    result the decoder stores at `out + 72` (`SD x18, x10, 72` at index 113).
    Header field **11** (`timestamp`) by the outward-call census below.
    ⚠️ This site has NO registry row; see the census note. -/
theorem header_extended_decode_u64_site_444_spec_within
    (srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (len : Nat)
    (hsub : srcEnd - BitVec.ofNat 64 len = srcBase)
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : len ≤ srcBytes.length) (hsover : srcBase.toNat + len ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (3 + (7 * len + 11))
      (headerExtendedDecodeBase + BitVec.ofNat 64 436)
      (headerExtendedDecodeBase + BitVec.ofNat 64 436 + 12)
      headerExtendedDecodeU64Code
      (u64SitePre srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old srcBytes len)
      (u64SitePost (headerExtendedDecodeBase + BitVec.ofNat 64 436) srcBase
        srcBytes len) :=
  header_extended_decode_u64_site_composed_within _ srcBase srcEnd raIn old11
    t0Old x6Old t2Old t3Old srcBytes len
    (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 444))
    hsub (by decide) (by decide)
    (headerExtendedDecode_mem_at 109 _ _ (by decide)
      (headerExtendedDecode_index_lt 109 (by decide)) rfl)
    (headerExtendedDecode_mem_at 110 _ _ (by decide)
      (headerExtendedDecode_index_lt 110 (by decide)) rfl)
    (headerExtendedDecode_mem_at 111 _ _ (by decide)
      (headerExtendedDecode_index_lt 111 (by decide)) rfl)
    hlen64 hsalign hslen hsover hsvalid

/-- Direct u64 site at `+604` (`SUB` at index 149, `JAL` at index 151), whose
    result the decoder stores at `out + 128` (`SD x18, x10, 128` at index 153).
    Header field **17** (`blob_gas_used`) by the outward-call census below. -/
theorem header_extended_decode_u64_site_604_spec_within
    (srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (len : Nat)
    (hsub : srcEnd - BitVec.ofNat 64 len = srcBase)
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : len ≤ srcBytes.length) (hsover : srcBase.toNat + len ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (3 + (7 * len + 11))
      (headerExtendedDecodeBase + BitVec.ofNat 64 596)
      (headerExtendedDecodeBase + BitVec.ofNat 64 596 + 12)
      headerExtendedDecodeU64Code
      (u64SitePre srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old srcBytes len)
      (u64SitePost (headerExtendedDecodeBase + BitVec.ofNat 64 596) srcBase
        srcBytes len) :=
  header_extended_decode_u64_site_composed_within _ srcBase srcEnd raIn old11
    t0Old x6Old t2Old t3Old srcBytes len
    (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 604))
    hsub (by decide) (by decide)
    (headerExtendedDecode_mem_at 149 _ _ (by decide)
      (headerExtendedDecode_index_lt 149 (by decide)) rfl)
    (headerExtendedDecode_mem_at 150 _ _ (by decide)
      (headerExtendedDecode_index_lt 150 (by decide)) rfl)
    (headerExtendedDecode_mem_at 151 _ _ (by decide)
      (headerExtendedDecode_index_lt 151 (by decide)) rfl)
    hlen64 hsalign hslen hsover hsvalid

/-- Direct u64 site at `+644` (`SUB` at index 159, `JAL` at index 161), whose
    result the decoder stores at `out + 136` (`SD x18, x10, 136` at index 163).
    Header field **18** (`excess_blob_gas`) by the outward-call census below. -/
theorem header_extended_decode_u64_site_644_spec_within
    (srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (len : Nat)
    (hsub : srcEnd - BitVec.ofNat 64 len = srcBase)
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : len ≤ srcBytes.length) (hsover : srcBase.toNat + len ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (3 + (7 * len + 11))
      (headerExtendedDecodeBase + BitVec.ofNat 64 636)
      (headerExtendedDecodeBase + BitVec.ofNat 64 636 + 12)
      headerExtendedDecodeU64Code
      (u64SitePre srcBase srcEnd raIn old11 t0Old x6Old t2Old t3Old srcBytes len)
      (u64SitePost (headerExtendedDecodeBase + BitVec.ofNat 64 636) srcBase
        srcBytes len) :=
  header_extended_decode_u64_site_composed_within _ srcBase srcEnd raIn old11
    t0Old x6Old t2Old t3Old srcBytes len
    (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 644))
    hsub (by decide) (by decide)
    (headerExtendedDecode_mem_at 159 _ _ (by decide)
      (headerExtendedDecode_index_lt 159 (by decide)) rfl)
    (headerExtendedDecode_mem_at 160 _ _ (by decide)
      (headerExtendedDecode_index_lt 160 (by decide)) rfl)
    (headerExtendedDecode_mem_at 161 _ _ (by decide)
      (headerExtendedDecode_index_lt 161 (by decide)) rfl)
    hlen64 hsalign hslen hsover hsvalid


/-! ### Where each site's result lands, and which header field it is

    The store that consumes each call is pinned below, so the six sites are
    distinguished by something the Program actually says rather than by a
    comment.  `x18` holds the caller's output struct pointer (`MV x18, x12`
    at index 7); the 32-byte copy loops fill `out + 0` and `out + 32`, and the
    u256 site at `+548` fills `out + 96`. -/

example : (show List Instr from headerExtendedDecode_prog)[83]? =
    some (.SD .x18 .x10 (64 : BitVec 12)) := by decide
example : (show List Instr from headerExtendedDecode_prog)[93]? =
    some (.SD .x18 .x10 (80 : BitVec 12)) := by decide
example : (show List Instr from headerExtendedDecode_prog)[103]? =
    some (.SD .x18 .x10 (88 : BitVec 12)) := by decide
example : (show List Instr from headerExtendedDecode_prog)[113]? =
    some (.SD .x18 .x10 (72 : BitVec 12)) := by decide
example : (show List Instr from headerExtendedDecode_prog)[153]? =
    some (.SD .x18 .x10 (128 : BitVec 12)) := by decide
example : (show List Instr from headerExtendedDecode_prog)[163]? =
    some (.SD .x18 .x10 (136 : BitVec 12)) := by decide

/-- **The outward-call census.**  Every `JAL x1` in `headerExtendedDecode_prog`,
    by index — 27 of them, and nothing else (the `JAL x0` at index 165 is the
    intra-routine jump over the failure arm, not a call).

    This is the fact that fixes which header field each u64 site decodes,
    because the decoder reaches field `i` by `rlp_walk_init` followed by
    `i + 1` calls to `rlp_walk_next`.  Reading the census: `8` is the
    `rlp_walk_init`; `137` is the single `rlp_content_to_u256_be_strict`;
    `81, 91, 101, 111, 151, 161` are the six `rlp_content_to_u64_strict`
    sites (already pinned individually above); the remaining 19 are
    `rlp_walk_next`.

    Counting `rlp_walk_next` calls before each strict site therefore gives:

    | site | walk_next calls before it | field |
    |---|---:|---:|
    | `+324` (idx 81)  | 9  | **8**  `number` |
    | `+364` (idx 91)  | 10 | **9**  `gas_limit` |
    | `+404` (idx 101) | 11 | **10** `gas_used` |
    | `+444` (idx 111) | 12 | **11** `timestamp` |
    | `+548` (idx 137, u256) | 16 | **15** `base_fee_per_gas` |
    | `+604` (idx 151) | 18 | **17** `blob_gas_used` |
    | `+644` (idx 161) | 19 | **18** `excess_blob_gas` |

    The two independently-agreed anchors calibrate the count: `+548` is the
    only u256-typed field and both this file's docstring and the registry call
    it field 15, and both call `+604`/`+644` fields 17/18.  Under the mapping
    "walk_next call `n` yields field `n-1`" all three land exactly, which then
    forces `+324` to be field **8** (`number`).

    ⚠️ `EvmAsm/Progress/Routines.lean` currently labels `+324`/`+364`/`+404`
    as fields 9/10/11.  That disagrees with this census and with this file's
    own docstring above; see the note on those rows.  The offsets in the rows
    are correct; the field names attached to the first three are shifted by
    one site, and `number` (field 8) has no row at all. -/
example :
    ((List.range 174).filter (fun k =>
        match (show List Instr from headerExtendedDecode_prog)[k]? with
        | some (.JAL .x1 _) => true
        | _ => false))
      = [8, 14, 30, 35, 40, 56, 61, 66, 71, 76, 81, 86, 91, 96, 101, 106, 111,
         116, 121, 126, 131, 137, 141, 146, 151, 156, 161] := by decide

/-! ### Non-vacuity for the six anchored site contracts

    A contract nobody can instantiate proves nothing, so each of the six gets
    the same two obligations: a **satisfiable instance** discharging every
    input-dependent hypothesis and landing in the post's *accept* disjunct,
    and a **negative control** exhibiting an instantiation of the very same
    conjuncts that is provably **false**.  Both are registered in
    `EvmAsm/Progress/Routines.lean` so the axiom gate audits them.

    The six sites share one hypothesis bundle (they differ only in `A`, which
    is concrete and appears in no hypothesis), so one instance and one control
    cover all six. -/

/-- Satisfiable instance for every `header_extended_decode_u64_site_*`:
    a two-byte content span `[0x12, 0x34]` at the dword-aligned RAM address
    `0xa0001000`, with the walker's `next` cursor `srcEnd = srcBase + 2`.
    Discharges `hsub`, `hlen64`, `hsalign`, `hslen`, `hsover`, `hsvalid`, and
    the trailing three conjuncts are exactly the guard of the post's **accept**
    disjunct (`0 < len ∧ len ≤ 8 ∧ content[0] ≠ 0`), so that arm is inhabited
    rather than merely stated. -/
theorem header_extended_decode_u64_site_instance :
    ∃ (srcBase srcEnd : Word) (srcBytes : List (BitVec 8)) (len : Nat),
      srcEnd - BitVec.ofNat 64 len = srcBase ∧
      len < 2 ^ 64 ∧ srcBase.toNat % 8 = 0 ∧ len ≤ srcBytes.length ∧
      srcBase.toNat + len ≤ 2 ^ 64 ∧
      (∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) ∧
      0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes 0 ≠ 0 := by
  refine ⟨(0xa0001000 : Word), (0xa0001002 : Word),
    [(0x12 : BitVec 8), (0x34 : BitVec 8)], 2,
    by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-- Negative control for the same bundle, on two independent conjuncts.

    (a) `hsub` is a real link between the walker's outputs, not bookkeeping:
    with `srcEnd = srcBase` (a zero-length span reported for a two-byte field)
    `srcEnd - 2 ≠ srcBase`, so the bundle excludes it.

    (b) `hsalign` and `hsvalid` are independent: the callee's own entry
    (`headerExtendedDecodeContentBase`) is dword-aligned, so `hsalign` holds
    there, and yet no byte of it is a legal data access — `.text` is outside
    every readable window.  So neither conjunct is implied by the other and
    neither is trivially true. -/
theorem header_extended_decode_u64_site_negative_control :
    (¬ ((0xa0001000 : Word) - BitVec.ofNat 64 2 = (0xa0001000 : Word))) ∧
    (headerExtendedDecodeContentBase.toNat % 8 = 0) ∧
    (¬ (∀ k, k < 2 →
        isValidByteAccess (headerExtendedDecodeContentBase +
          BitVec.ofNat 64 k) = true)) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have h0 := h 0 (by decide)
  revert h0
  decide

/-! ## Anti-vacuity cover (#12476)

    The old `hslack` (`listLen + 9 ≤ bytes.length`) was unsatisfiable on every
    short-form exact-fit list (`|bytes| = 1 + listLen`). The repaired premise
    *set* of `header_u64_spec_within` is jointly inhabited on that shape. -/

/-- Short-form exact-fit cover: `listLen = 1`, `|bytes| = 2`, `listBase = MEM_START`.
    Instantiates the theorem's real geometry binders (not a paraphrase). -/
example :
    let listLen := 1
    let bytes : List (BitVec 8) := List.replicate 2 (0 : BitVec 8)
    let listBase : Word := BitVec.ofNat 64 MEM_START
    (listBase.toNat % 8 = 0) ∧
    (listLen ≤ bytes.length) ∧
    (listBase.toNat + listLen + 9 < 2 ^ 64) ∧
    (listBase.toNat + bytes.length < 2 ^ 64) ∧
    (0 < bytes.length) ∧
    (∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) := by
  refine ⟨?hsalign, ?hbytes, ?hnowrap, ?hover, ?hnz, ?hvalid⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro k hk
    have hk2 : k < 2 := by simpa using hk
    have hsum :
        (BitVec.ofNat 64 MEM_START + BitVec.ofNat 64 k).toNat = 32 + k := by
      simp only [MEM_START]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 32 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 32 + k < 2 ^ 64)]
    simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    refine Or.inl (Or.inl ?_)
    constructor
    · rw [hsum]; change 32 ≤ 32 + k; omega
    · rw [hsum]; change 32 + k ≤ 0x78000000; omega

end EvmAsm.Codegen.HeaderU64ExtractSpec
