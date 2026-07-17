/-
  Extract body: MV a0/a1 setup before rlp_walk_next call sites + second skip.
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
import EvmAsm.Codegen.Programs.TxExtractToAddressTypeBranch
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

set_option maxRecDepth 8000 in
/-- type234: `mv a0,s5; mv a1,s6` Type234Start → WalkNext0JalPc. -/
theorem extractType234LoadArgs (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin (1 + 1) Type234Start WalkNext0JalPc extractLinkedCode
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have hm0 := mv_spec_gen_within .x10 .x21 cursor a0Old Type234Start (by decide)
  have he0 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E Type234Start extractProg 44
        (.MV .x10 .x21) (by simp only [Type234Start]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hm0
  rw [show (Type234Start + 4 : Word) = E + 180 from by
    simp only [Type234Start]; bv_omega] at he0
  have hm0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he0
  have hm1 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 180) (by decide)
  have he1 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 180) extractProg 45
        (.MV .x11 .x22) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hm1
  rw [show ((E + 180 : Word) + 4) = WalkNext0JalPc from by
    simp only [WalkNext0JalPc]; bv_omega] at he1
  have hm1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) he1
  have h := cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) hm0F hm1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h

abbrev WalkNext1JalPc : Word := E + 204
abbrev LinkWalkNext1 : Word := E + 208
abbrev AfterWalkNext1Bne : Word := E + 212

set_option maxRecDepth 8000 in
/-- `mv s5,a0; mv a0,s5; mv a1,s6` AfterWalkNext0Bne → WalkNext1JalPc. -/
theorem extractWalkNext1Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext0Bne WalkNext1JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  -- MV s5, a0
  have s0 : cpsTripleWithin 1 AfterWalkNext0Bne (E + 196) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterWalkNext0Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterWalkNext0Bne extractProg 48
          (.MV .x21 .x10) (by simp only [AfterWalkNext0Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterWalkNext0Bne + 4 : Word) = E + 196 from by
      simp only [AfterWalkNext0Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  -- MV a0, s5 (both cursor)
  have s1 : cpsTripleWithin 1 (E + 196) (E + 200) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 196) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 196) extractProg 49
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 196 : Word) + 4) = E + 200 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  -- MV a1, s6
  have s2 : cpsTripleWithin 1 (E + 200) WalkNext1JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 200) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 200) extractProg 50
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 200 : Word) + 4) = WalkNext1JalPc from by
      simp only [WalkNext1JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def walkNext1JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 204)

theorem walkNext1JalOff_resolves :
    WalkNext1JalPc + signExtend21 walkNext1JalOff = WN := by
  simp only [WalkNext1JalPc, WN, walkNext1JalOff, E]; decide

def extractWalkNext1Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext1) **
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
theorem extractWalkNext1Call
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
    cpsTripleWithin (1 + 87) WalkNext1JalPc LinkWalkNext1 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext1Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkWalkNext1 &&& ~~~(1 : Word)) = LinkWalkNext1 := by
    simp only [LinkWalkNext1, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkWalkNext1 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext1 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext1Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractWalkNext1Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext1 extractLinkedCode
      ((.x1 ↦ᵣ LinkWalkNext1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkWalkNext1) **
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
      simp only [extractWalkNext1Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext1JalPc WN old1 walkNext1JalOff 87
    walkNext1JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E WalkNext1JalPc extractProg 51
        (.JAL .x1 walkNext1JalOff) (by simp only [WalkNext1JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (WalkNext1JalPc + 4 : Word) = LinkWalkNext1 from by
    simp only [WalkNext1JalPc, LinkWalkNext1]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractWalkNext1Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractWalkNext1BneOk :
    cpsTripleWithin 1 LinkWalkNext1 AfterWalkNext1Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (344 : BitVec 13)
    (0 : Word) (0 : Word) LinkWalkNext1
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkWalkNext1 extractProg 52
        (.BNE .x11 .x0 (344 : BitVec 13)) (by simp only [LinkWalkNext1]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkWalkNext1 + 4 : Word) = AfterWalkNext1Bne from by
    simp only [LinkWalkNext1, AfterWalkNext1Bne]; bv_omega] at hnt
  exact hnt

#print axioms extractType234LoadArgs
#print axioms extractWalkNext1Prep
#print axioms extractWalkNext1Call
#print axioms extractWalkNext1BneOk

end EvmAsm.Codegen.TxExtractToAddressSpec
