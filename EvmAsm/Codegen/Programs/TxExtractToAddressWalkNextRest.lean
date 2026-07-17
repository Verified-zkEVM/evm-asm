/-
  Extract body: type234 walk_next skips 2..5 (prep + call + BNE not-taken).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNextArgs
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpWalkCallSAsm

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact bytesRegion_pcFree _ _)

abbrev WalkNext2JalPc : Word := E + 224
abbrev LinkWalkNext2 : Word := E + 228
abbrev AfterWalkNext2Bne : Word := E + 232

set_option maxRecDepth 8000 in
/-- `mv s5,a0; mv a0,s5; mv a1,s6` AfterWalkNext1Bne → WalkNext2JalPc. -/
theorem extractWalkNext2Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext1Bne WalkNext2JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have s0 : cpsTripleWithin 1 AfterWalkNext1Bne (E + 216) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterWalkNext1Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterWalkNext1Bne extractProg 53
          (.MV .x21 .x10) (by simp only [AfterWalkNext1Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterWalkNext1Bne + 4 : Word) = E + 216 from by
      simp only [AfterWalkNext1Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s1 : cpsTripleWithin 1 (E + 216) (E + 220) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 216) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 216) extractProg 54
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 216 : Word) + 4) = E + 220 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s2 : cpsTripleWithin 1 (E + 220) WalkNext2JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 220) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 220) extractProg 55
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 220 : Word) + 4) = WalkNext2JalPc from by
      simp only [WalkNext2JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def walkNext2JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 224)

theorem walkNext2JalOff_resolves :
    WalkNext2JalPc + signExtend21 walkNext2JalOff = WN := by
  simp only [WalkNext2JalPc, WN, walkNext2JalOff, E]; decide

def extractWalkNext2Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext2) **
    bytesRegion txBase txBytes) **
   (fun h =>
     rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff h ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h)))

set_option maxRecDepth 8000 in
theorem extractWalkNext2Call
    (txBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) (old1 : Word)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext2JalPc LinkWalkNext2 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext2Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkWalkNext2 &&& ~~~(1 : Word)) = LinkWalkNext2 := by
    simp only [LinkWalkNext2, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkWalkNext2 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext2 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext2) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext2Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractWalkNext2Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext2 extractLinkedCode
      ((.x1 ↦ᵣ LinkWalkNext2) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkWalkNext2) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion txBase txBytes) **
         (fun h =>
           rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff h ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [extractWalkNext2Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext2JalPc WN old1 walkNext2JalOff 87
    walkNext2JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E WalkNext2JalPc extractProg 56
        (.JAL .x1 walkNext2JalOff) (by simp only [WalkNext2JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (WalkNext2JalPc + 4 : Word) = LinkWalkNext2 from by
    simp only [WalkNext2JalPc, LinkWalkNext2]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractWalkNext2Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractWalkNext2BneOk :
    cpsTripleWithin 1 LinkWalkNext2 AfterWalkNext2Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (324 : BitVec 13)
    (0 : Word) (0 : Word) LinkWalkNext2
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkWalkNext2 extractProg 57
        (.BNE .x11 .x0 (324 : BitVec 13)) (by simp only [LinkWalkNext2]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkWalkNext2 + 4 : Word) = AfterWalkNext2Bne from by
    simp only [LinkWalkNext2, AfterWalkNext2Bne]; bv_omega] at hnt
  exact hnt

abbrev WalkNext3JalPc : Word := E + 244
abbrev LinkWalkNext3 : Word := E + 248
abbrev AfterWalkNext3Bne : Word := E + 252

set_option maxRecDepth 8000 in
/-- `mv s5,a0; mv a0,s5; mv a1,s6` AfterWalkNext2Bne → WalkNext3JalPc. -/
theorem extractWalkNext3Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext2Bne WalkNext3JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have s0 : cpsTripleWithin 1 AfterWalkNext2Bne (E + 236) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterWalkNext2Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterWalkNext2Bne extractProg 58
          (.MV .x21 .x10) (by simp only [AfterWalkNext2Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterWalkNext2Bne + 4 : Word) = E + 236 from by
      simp only [AfterWalkNext2Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s1 : cpsTripleWithin 1 (E + 236) (E + 240) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 236) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 236) extractProg 59
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 236 : Word) + 4) = E + 240 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s2 : cpsTripleWithin 1 (E + 240) WalkNext3JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 240) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 240) extractProg 60
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 240 : Word) + 4) = WalkNext3JalPc from by
      simp only [WalkNext3JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def walkNext3JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 244)

theorem walkNext3JalOff_resolves :
    WalkNext3JalPc + signExtend21 walkNext3JalOff = WN := by
  simp only [WalkNext3JalPc, WN, walkNext3JalOff, E]; decide

def extractWalkNext3Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext3) **
    bytesRegion txBase txBytes) **
   (fun h =>
     rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff h ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h)))

set_option maxRecDepth 8000 in
theorem extractWalkNext3Call
    (txBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) (old1 : Word)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext3JalPc LinkWalkNext3 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext3Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkWalkNext3 &&& ~~~(1 : Word)) = LinkWalkNext3 := by
    simp only [LinkWalkNext3, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkWalkNext3 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext3 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext3) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext3Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractWalkNext3Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext3 extractLinkedCode
      ((.x1 ↦ᵣ LinkWalkNext3) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkWalkNext3) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion txBase txBytes) **
         (fun h =>
           rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff h ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [extractWalkNext3Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext3JalPc WN old1 walkNext3JalOff 87
    walkNext3JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E WalkNext3JalPc extractProg 61
        (.JAL .x1 walkNext3JalOff) (by simp only [WalkNext3JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (WalkNext3JalPc + 4 : Word) = LinkWalkNext3 from by
    simp only [WalkNext3JalPc, LinkWalkNext3]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractWalkNext3Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractWalkNext3BneOk :
    cpsTripleWithin 1 LinkWalkNext3 AfterWalkNext3Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (304 : BitVec 13)
    (0 : Word) (0 : Word) LinkWalkNext3
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkWalkNext3 extractProg 62
        (.BNE .x11 .x0 (304 : BitVec 13)) (by simp only [LinkWalkNext3]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkWalkNext3 + 4 : Word) = AfterWalkNext3Bne from by
    simp only [LinkWalkNext3, AfterWalkNext3Bne]; bv_omega] at hnt
  exact hnt

abbrev WalkNext4JalPc : Word := E + 264
abbrev LinkWalkNext4 : Word := E + 268
abbrev AfterWalkNext4Bne : Word := E + 272

set_option maxRecDepth 8000 in
/-- `mv s5,a0; mv a0,s5; mv a1,s6` AfterWalkNext3Bne → WalkNext4JalPc. -/
theorem extractWalkNext4Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext3Bne WalkNext4JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have s0 : cpsTripleWithin 1 AfterWalkNext3Bne (E + 256) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterWalkNext3Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterWalkNext3Bne extractProg 63
          (.MV .x21 .x10) (by simp only [AfterWalkNext3Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterWalkNext3Bne + 4 : Word) = E + 256 from by
      simp only [AfterWalkNext3Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s1 : cpsTripleWithin 1 (E + 256) (E + 260) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 256) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 256) extractProg 64
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 256 : Word) + 4) = E + 260 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s2 : cpsTripleWithin 1 (E + 260) WalkNext4JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 260) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 260) extractProg 65
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 260 : Word) + 4) = WalkNext4JalPc from by
      simp only [WalkNext4JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def walkNext4JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 264)

theorem walkNext4JalOff_resolves :
    WalkNext4JalPc + signExtend21 walkNext4JalOff = WN := by
  simp only [WalkNext4JalPc, WN, walkNext4JalOff, E]; decide

def extractWalkNext4Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext4) **
    bytesRegion txBase txBytes) **
   (fun h =>
     rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff h ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h)))

set_option maxRecDepth 8000 in
theorem extractWalkNext4Call
    (txBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) (old1 : Word)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext4JalPc LinkWalkNext4 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext4Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkWalkNext4 &&& ~~~(1 : Word)) = LinkWalkNext4 := by
    simp only [LinkWalkNext4, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkWalkNext4 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext4 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext4) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext4Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractWalkNext4Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext4 extractLinkedCode
      ((.x1 ↦ᵣ LinkWalkNext4) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkWalkNext4) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion txBase txBytes) **
         (fun h =>
           rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff h ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [extractWalkNext4Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext4JalPc WN old1 walkNext4JalOff 87
    walkNext4JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E WalkNext4JalPc extractProg 66
        (.JAL .x1 walkNext4JalOff) (by simp only [WalkNext4JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (WalkNext4JalPc + 4 : Word) = LinkWalkNext4 from by
    simp only [WalkNext4JalPc, LinkWalkNext4]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractWalkNext4Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractWalkNext4BneOk :
    cpsTripleWithin 1 LinkWalkNext4 AfterWalkNext4Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (284 : BitVec 13)
    (0 : Word) (0 : Word) LinkWalkNext4
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkWalkNext4 extractProg 67
        (.BNE .x11 .x0 (284 : BitVec 13)) (by simp only [LinkWalkNext4]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkWalkNext4 + 4 : Word) = AfterWalkNext4Bne from by
    simp only [LinkWalkNext4, AfterWalkNext4Bne]; bv_omega] at hnt
  exact hnt

abbrev WalkNext5JalPc : Word := E + 284
abbrev LinkWalkNext5 : Word := E + 288
abbrev AfterWalkNext5Bne : Word := E + 292

set_option maxRecDepth 8000 in
/-- `mv s5,a0; mv a0,s5; mv a1,s6` AfterWalkNext4Bne → WalkNext5JalPc. -/
theorem extractWalkNext5Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext4Bne WalkNext5JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have s0 : cpsTripleWithin 1 AfterWalkNext4Bne (E + 276) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterWalkNext4Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterWalkNext4Bne extractProg 68
          (.MV .x21 .x10) (by simp only [AfterWalkNext4Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterWalkNext4Bne + 4 : Word) = E + 276 from by
      simp only [AfterWalkNext4Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s1 : cpsTripleWithin 1 (E + 276) (E + 280) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 276) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 276) extractProg 69
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 276 : Word) + 4) = E + 280 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s2 : cpsTripleWithin 1 (E + 280) WalkNext5JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 280) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 280) extractProg 70
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 280 : Word) + 4) = WalkNext5JalPc from by
      simp only [WalkNext5JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def walkNext5JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 284)

theorem walkNext5JalOff_resolves :
    WalkNext5JalPc + signExtend21 walkNext5JalOff = WN := by
  simp only [WalkNext5JalPc, WN, walkNext5JalOff, E]; decide

def extractWalkNext5Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
    bytesRegion txBase txBytes) **
   (fun h =>
     rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff h ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h)))

set_option maxRecDepth 8000 in
theorem extractWalkNext5Call
    (txBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) (old1 : Word)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext5JalPc LinkWalkNext5 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext5Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkWalkNext5 &&& ~~~(1 : Word)) = LinkWalkNext5 := by
    simp only [LinkWalkNext5, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkWalkNext5 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext5 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext5) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext5Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractWalkNext5Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext5 extractLinkedCode
      ((.x1 ↦ᵣ LinkWalkNext5) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkWalkNext5) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion txBase txBytes) **
         (fun h =>
           rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff h ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [extractWalkNext5Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext5JalPc WN old1 walkNext5JalOff 87
    walkNext5JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E WalkNext5JalPc extractProg 71
        (.JAL .x1 walkNext5JalOff) (by simp only [WalkNext5JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (WalkNext5JalPc + 4 : Word) = LinkWalkNext5 from by
    simp only [WalkNext5JalPc, LinkWalkNext5]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractWalkNext5Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractWalkNext5BneOk :
    cpsTripleWithin 1 LinkWalkNext5 AfterWalkNext5Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (264 : BitVec 13)
    (0 : Word) (0 : Word) LinkWalkNext5
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkWalkNext5 extractProg 72
        (.BNE .x11 .x0 (264 : BitVec 13)) (by simp only [LinkWalkNext5]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkWalkNext5 + 4 : Word) = AfterWalkNext5Bne from by
    simp only [LinkWalkNext5, AfterWalkNext5Bne]; bv_omega] at hnt
  exact hnt

#print axioms extractWalkNext2Prep
#print axioms extractWalkNext2Call
#print axioms extractWalkNext2BneOk
#print axioms extractWalkNext3Prep
#print axioms extractWalkNext3Call
#print axioms extractWalkNext3BneOk
#print axioms extractWalkNext4Prep
#print axioms extractWalkNext4Call
#print axioms extractWalkNext4BneOk
#print axioms extractWalkNext5Prep
#print axioms extractWalkNext5Call
#print axioms extractWalkNext5BneOk

end EvmAsm.Codegen.TxExtractToAddressSpec
