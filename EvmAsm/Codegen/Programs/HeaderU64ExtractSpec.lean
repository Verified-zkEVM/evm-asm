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

def wrapperCode_mono (index : Word) :
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
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
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
    listLen index hnewSp hlistLenW rfl hindex hsalign hslack hover hvalid
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

/- abbrev headerExtendedDecodeBase : Word :=
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
    · rw [show headerExtendedDecode_prog.length = 174 by decide]
      decide
    · rw [rlp_content_to_u64_strict_prog_length]
      decide
    · rw [show headerExtendedDecode_prog.length = 174 by decide,
        rlp_content_to_u64_strict_prog_length]
      decide) (fun _ _ h' => h') a i h -/

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

/-! A first linked-site specialization for the production decoder.  Keeping the
    call-site arithmetic here, next to the six re-anchor guards above, makes the
    segment usable by the eventual whole-decoder proof without treating an
    arbitrary three-instruction wrapper as evidence about the guest. -/
abbrev decoderBase : Word := (GuestAddrs.header_extended_decode : Word)
abbrev u64Base : Word := (GuestAddrs.rlp_content_to_u64_strict : Word)

set_option maxRecDepth 8000 in
theorem header_extended_decode_field17_segment_spec_within
    (srcBase srcEnd len raIn old11 : Word)
    (n : Nat) (R Q : Assertion) (cr : CodeReq)
    (hsub : srcEnd - len = srcBase)
    (hcallee : cpsTripleWithin n u64Base (decoderBase + 608) cr
      (((.x1 ↦ᵣ (decoderBase + 608)) ** (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ len) ** R))
      (((.x1 ↦ᵣ (decoderBase + 608)) ** Q)))
    (hR : R.pcFree)
    (hsub_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 596) (.SUB .x10 .x10 .x12) a = some i →
        cr a = some i)
    (hmv_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 600) (.MV .x11 .x12) a = some i →
        cr a = some i)
    (hjal_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 604)
        (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
          (GuestAddrs.header_extended_decode + 604))) a = some i →
        cr a = some i) :
    cpsTripleWithin (3 + n) (decoderBase + 596) (decoderBase + 608) cr
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcEnd) ** (.x11 ↦ᵣ old11) **
       (.x12 ↦ᵣ len) ** R)
      (((.x1 ↦ᵣ (decoderBase + 608)) ** (.x12 ↦ᵣ len) ** Q)) := by
  have h := header_extended_decode_u64_segment_spec_within
    (A := decoderBase + 596) (calleeEntry := u64Base)
    (srcBase := srcBase) (srcEnd := srcEnd) (len := len) (raIn := raIn)
    (old11 := old11)
    (jal := jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 604))
    (n := n) (R := R) (Q := Q) (cr := cr) hsub
    (by decide) hsub_mem hmv_mem hjal_mem hR hcallee
  simpa [decoderBase, u64Base, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_field8_segment_spec_within
    (srcBase srcEnd len raIn old11 : Word)
    (n : Nat) (R Q : Assertion) (cr : CodeReq)
    (hsub : srcEnd - len = srcBase)
    (hcallee : cpsTripleWithin n u64Base (decoderBase + 328) cr
      (((.x1 ↦ᵣ (decoderBase + 328)) ** (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ len) ** R))
      (((.x1 ↦ᵣ (decoderBase + 328)) ** Q)))
    (hR : R.pcFree)
    (hsub_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 316) (.SUB .x10 .x10 .x12) a = some i →
        cr a = some i)
    (hmv_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 320) (.MV .x11 .x12) a = some i →
        cr a = some i)
    (hjal_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 324)
        (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
          (GuestAddrs.header_extended_decode + 324))) a = some i →
        cr a = some i) :
    cpsTripleWithin (3 + n) (decoderBase + 316) (decoderBase + 328) cr
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcEnd) ** (.x11 ↦ᵣ old11) **
       (.x12 ↦ᵣ len) ** R)
      (((.x1 ↦ᵣ (decoderBase + 328)) ** (.x12 ↦ᵣ len) ** Q)) := by
  have h := header_extended_decode_u64_segment_spec_within
    (A := decoderBase + 316) (calleeEntry := u64Base)
    (srcBase := srcBase) (srcEnd := srcEnd) (len := len) (raIn := raIn)
    (old11 := old11)
    (jal := jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 324))
    (n := n) (R := R) (Q := Q) (cr := cr) hsub
    (by decide) hsub_mem hmv_mem hjal_mem hR hcallee
  simpa [decoderBase, u64Base, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_field9_segment_spec_within
    (srcBase srcEnd len raIn old11 : Word)
    (n : Nat) (R Q : Assertion) (cr : CodeReq)
    (hsub : srcEnd - len = srcBase)
    (hcallee : cpsTripleWithin n u64Base (decoderBase + 368) cr
      (((.x1 ↦ᵣ (decoderBase + 368)) ** (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ len) ** R))
      (((.x1 ↦ᵣ (decoderBase + 368)) ** Q)))
    (hR : R.pcFree)
    (hsub_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 356) (.SUB .x10 .x10 .x12) a = some i →
        cr a = some i)
    (hmv_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 360) (.MV .x11 .x12) a = some i →
        cr a = some i)
    (hjal_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 364)
        (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
          (GuestAddrs.header_extended_decode + 364))) a = some i →
        cr a = some i) :
    cpsTripleWithin (3 + n) (decoderBase + 356) (decoderBase + 368) cr
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcEnd) ** (.x11 ↦ᵣ old11) **
       (.x12 ↦ᵣ len) ** R)
      (((.x1 ↦ᵣ (decoderBase + 368)) ** (.x12 ↦ᵣ len) ** Q)) := by
  have h := header_extended_decode_u64_segment_spec_within
    (A := decoderBase + 356) (calleeEntry := u64Base)
    (srcBase := srcBase) (srcEnd := srcEnd) (len := len) (raIn := raIn)
    (old11 := old11)
    (jal := jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 364))
    (n := n) (R := R) (Q := Q) (cr := cr) hsub
    (by decide) hsub_mem hmv_mem hjal_mem hR hcallee
  simpa [decoderBase, u64Base, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_field10_segment_spec_within
    (srcBase srcEnd len raIn old11 : Word)
    (n : Nat) (R Q : Assertion) (cr : CodeReq)
    (hsub : srcEnd - len = srcBase)
    (hcallee : cpsTripleWithin n u64Base (decoderBase + 408) cr
      (((.x1 ↦ᵣ (decoderBase + 408)) ** (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ len) ** R))
      (((.x1 ↦ᵣ (decoderBase + 408)) ** Q)))
    (hR : R.pcFree)
    (hsub_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 396) (.SUB .x10 .x10 .x12) a = some i →
        cr a = some i)
    (hmv_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 400) (.MV .x11 .x12) a = some i →
        cr a = some i)
    (hjal_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 404)
        (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
          (GuestAddrs.header_extended_decode + 404))) a = some i →
        cr a = some i) :
    cpsTripleWithin (3 + n) (decoderBase + 396) (decoderBase + 408) cr
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcEnd) ** (.x11 ↦ᵣ old11) **
       (.x12 ↦ᵣ len) ** R)
      (((.x1 ↦ᵣ (decoderBase + 408)) ** (.x12 ↦ᵣ len) ** Q)) := by
  have h := header_extended_decode_u64_segment_spec_within
    (A := decoderBase + 396) (calleeEntry := u64Base)
    (srcBase := srcBase) (srcEnd := srcEnd) (len := len) (raIn := raIn)
    (old11 := old11)
    (jal := jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 404))
    (n := n) (R := R) (Q := Q) (cr := cr) hsub
    (by decide) hsub_mem hmv_mem hjal_mem hR hcallee
  simpa [decoderBase, u64Base, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_field11_segment_spec_within
    (srcBase srcEnd len raIn old11 : Word)
    (n : Nat) (R Q : Assertion) (cr : CodeReq)
    (hsub : srcEnd - len = srcBase)
    (hcallee : cpsTripleWithin n u64Base (decoderBase + 448) cr
      (((.x1 ↦ᵣ (decoderBase + 448)) ** (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ len) ** R))
      (((.x1 ↦ᵣ (decoderBase + 448)) ** Q)))
    (hR : R.pcFree)
    (hsub_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 436) (.SUB .x10 .x10 .x12) a = some i →
        cr a = some i)
    (hmv_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 440) (.MV .x11 .x12) a = some i →
        cr a = some i)
    (hjal_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 444)
        (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
          (GuestAddrs.header_extended_decode + 444))) a = some i →
        cr a = some i) :
    cpsTripleWithin (3 + n) (decoderBase + 436) (decoderBase + 448) cr
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcEnd) ** (.x11 ↦ᵣ old11) **
       (.x12 ↦ᵣ len) ** R)
      (((.x1 ↦ᵣ (decoderBase + 448)) ** (.x12 ↦ᵣ len) ** Q)) := by
  have h := header_extended_decode_u64_segment_spec_within
    (A := decoderBase + 436) (calleeEntry := u64Base)
    (srcBase := srcBase) (srcEnd := srcEnd) (len := len) (raIn := raIn)
    (old11 := old11)
    (jal := jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 444))
    (n := n) (R := R) (Q := Q) (cr := cr) hsub
    (by decide) hsub_mem hmv_mem hjal_mem hR hcallee
  simpa [decoderBase, u64Base, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_field18_segment_spec_within
    (srcBase srcEnd len raIn old11 : Word)
    (n : Nat) (R Q : Assertion) (cr : CodeReq)
    (hsub : srcEnd - len = srcBase)
    (hcallee : cpsTripleWithin n u64Base (decoderBase + 648) cr
      (((.x1 ↦ᵣ (decoderBase + 648)) ** (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ len) ** R))
      (((.x1 ↦ᵣ (decoderBase + 648)) ** Q)))
    (hR : R.pcFree)
    (hsub_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 636) (.SUB .x10 .x10 .x12) a = some i →
        cr a = some i)
    (hmv_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 640) (.MV .x11 .x12) a = some i →
        cr a = some i)
    (hjal_mem : ∀ a i,
      CodeReq.singleton (decoderBase + 644)
        (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
          (GuestAddrs.header_extended_decode + 644))) a = some i →
        cr a = some i) :
    cpsTripleWithin (3 + n) (decoderBase + 636) (decoderBase + 648) cr
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ srcEnd) ** (.x11 ↦ᵣ old11) **
       (.x12 ↦ᵣ len) ** R)
      (((.x1 ↦ᵣ (decoderBase + 648)) ** (.x12 ↦ᵣ len) ** Q)) := by
  have h := header_extended_decode_u64_segment_spec_within
    (A := decoderBase + 636) (calleeEntry := u64Base)
    (srcBase := srcBase) (srcEnd := srcEnd) (len := len) (raIn := raIn)
    (old11 := old11)
    (jal := jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.header_extended_decode + 644))
    (n := n) (R := R) (Q := Q) (cr := cr) hsub
    (by decide) hsub_mem hmv_mem hjal_mem hR hcallee
  simpa [decoderBase, u64Base, BitVec.add_assoc] using h

end EvmAsm.Codegen.HeaderU64ExtractSpec
