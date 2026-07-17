/-
  Extract body: type-1 walk_next chain (5 skips) + SUB fall-through to HaveField.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressTypeBranch
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressHaveField
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

abbrev T1Walk0JalPc : Word := E + 392
abbrev LinkT1Walk0 : Word := E + 396
abbrev AfterT1Walk0Bne : Word := E + 400

set_option maxRecDepth 8000 in
theorem extractT1LoadArgs (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin (1 + 1) T1Start T1Walk0JalPc extractLinkedCode
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have hm0 := mv_spec_gen_within .x10 .x21 cursor a0Old T1Start (by decide)
  have he0 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E T1Start extractProg 96
        (.MV .x10 .x21) (by simp only [T1Start]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hm0
  rw [show (T1Start + 4 : Word) = E + 388 from by
    simp only [T1Start]; bv_omega] at he0
  have hm0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he0
  have hm1 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 388) (by decide)
  have he1 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 388) extractProg 97
        (.MV .x11 .x22) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hm1
  rw [show ((E + 388 : Word) + 4) = T1Walk0JalPc from by
    simp only [T1Walk0JalPc]; bv_omega] at he1
  have hm1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) he1
  have h := cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) hm0F hm1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h

private def t1Walk0JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 392)

theorem t1Walk0JalOff_resolves :
    T1Walk0JalPc + signExtend21 t1Walk0JalOff = WN := by
  simp only [T1Walk0JalPc, WN, t1Walk0JalOff, E]; decide

def extractT1Walk0Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk0) **
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
theorem extractT1Walk0Call
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
    cpsTripleWithin (1 + 87) T1Walk0JalPc LinkT1Walk0 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractT1Walk0Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkT1Walk0 &&& ~~~(1 : Word)) = LinkT1Walk0 := by
    simp only [LinkT1Walk0, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkT1Walk0 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkT1Walk0 walkNextCode
      ((.x1 ↦ᵣ LinkT1Walk0) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractT1Walk0Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractT1Walk0Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkT1Walk0 extractLinkedCode
      ((.x1 ↦ᵣ LinkT1Walk0) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkT1Walk0) **
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
      simp only [extractT1Walk0Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec T1Walk0JalPc WN old1 t1Walk0JalOff 87
    t1Walk0JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E T1Walk0JalPc extractProg 98
        (.JAL .x1 t1Walk0JalOff) (by simp only [T1Walk0JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (T1Walk0JalPc + 4 : Word) = LinkT1Walk0 from by
    simp only [T1Walk0JalPc, LinkT1Walk0]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractT1Walk0Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractT1Walk0BneOk :
    cpsTripleWithin 1 LinkT1Walk0 AfterT1Walk0Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (156 : BitVec 13)
    (0 : Word) (0 : Word) LinkT1Walk0
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkT1Walk0 extractProg 99
        (.BNE .x11 .x0 (156 : BitVec 13)) (by simp only [LinkT1Walk0]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkT1Walk0 + 4 : Word) = AfterT1Walk0Bne from by
    simp only [LinkT1Walk0, AfterT1Walk0Bne]; bv_omega] at hnt
  exact hnt

abbrev T1Walk1JalPc : Word := E + 412
abbrev LinkT1Walk1 : Word := E + 416
abbrev AfterT1Walk1Bne : Word := E + 420

set_option maxRecDepth 8000 in
theorem extractT1Walk1Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk0Bne T1Walk1JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have s0 : cpsTripleWithin 1 AfterT1Walk0Bne (E + 404) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterT1Walk0Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterT1Walk0Bne extractProg 100
          (.MV .x21 .x10) (by simp only [AfterT1Walk0Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterT1Walk0Bne + 4 : Word) = E + 404 from by
      simp only [AfterT1Walk0Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s1 : cpsTripleWithin 1 (E + 404) (E + 408) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 404) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 404) extractProg 101
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 404 : Word) + 4) = E + 408 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s2 : cpsTripleWithin 1 (E + 408) T1Walk1JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 408) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 408) extractProg 102
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 408 : Word) + 4) = T1Walk1JalPc from by
      simp only [T1Walk1JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def t1Walk1JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 412)

theorem t1Walk1JalOff_resolves :
    T1Walk1JalPc + signExtend21 t1Walk1JalOff = WN := by
  simp only [T1Walk1JalPc, WN, t1Walk1JalOff, E]; decide

def extractT1Walk1Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk1) **
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
theorem extractT1Walk1Call
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
    cpsTripleWithin (1 + 87) T1Walk1JalPc LinkT1Walk1 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractT1Walk1Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkT1Walk1 &&& ~~~(1 : Word)) = LinkT1Walk1 := by
    simp only [LinkT1Walk1, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkT1Walk1 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkT1Walk1 walkNextCode
      ((.x1 ↦ᵣ LinkT1Walk1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractT1Walk1Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractT1Walk1Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkT1Walk1 extractLinkedCode
      ((.x1 ↦ᵣ LinkT1Walk1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkT1Walk1) **
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
      simp only [extractT1Walk1Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec T1Walk1JalPc WN old1 t1Walk1JalOff 87
    t1Walk1JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E T1Walk1JalPc extractProg 103
        (.JAL .x1 t1Walk1JalOff) (by simp only [T1Walk1JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (T1Walk1JalPc + 4 : Word) = LinkT1Walk1 from by
    simp only [T1Walk1JalPc, LinkT1Walk1]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractT1Walk1Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractT1Walk1BneOk :
    cpsTripleWithin 1 LinkT1Walk1 AfterT1Walk1Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (136 : BitVec 13)
    (0 : Word) (0 : Word) LinkT1Walk1
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkT1Walk1 extractProg 104
        (.BNE .x11 .x0 (136 : BitVec 13)) (by simp only [LinkT1Walk1]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkT1Walk1 + 4 : Word) = AfterT1Walk1Bne from by
    simp only [LinkT1Walk1, AfterT1Walk1Bne]; bv_omega] at hnt
  exact hnt

abbrev T1Walk2JalPc : Word := E + 432
abbrev LinkT1Walk2 : Word := E + 436
abbrev AfterT1Walk2Bne : Word := E + 440

set_option maxRecDepth 8000 in
theorem extractT1Walk2Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk1Bne T1Walk2JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have s0 : cpsTripleWithin 1 AfterT1Walk1Bne (E + 424) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterT1Walk1Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterT1Walk1Bne extractProg 105
          (.MV .x21 .x10) (by simp only [AfterT1Walk1Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterT1Walk1Bne + 4 : Word) = E + 424 from by
      simp only [AfterT1Walk1Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s1 : cpsTripleWithin 1 (E + 424) (E + 428) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 424) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 424) extractProg 106
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 424 : Word) + 4) = E + 428 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s2 : cpsTripleWithin 1 (E + 428) T1Walk2JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 428) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 428) extractProg 107
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 428 : Word) + 4) = T1Walk2JalPc from by
      simp only [T1Walk2JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def t1Walk2JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 432)

theorem t1Walk2JalOff_resolves :
    T1Walk2JalPc + signExtend21 t1Walk2JalOff = WN := by
  simp only [T1Walk2JalPc, WN, t1Walk2JalOff, E]; decide

def extractT1Walk2Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk2) **
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
theorem extractT1Walk2Call
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
    cpsTripleWithin (1 + 87) T1Walk2JalPc LinkT1Walk2 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractT1Walk2Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkT1Walk2 &&& ~~~(1 : Word)) = LinkT1Walk2 := by
    simp only [LinkT1Walk2, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkT1Walk2 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkT1Walk2 walkNextCode
      ((.x1 ↦ᵣ LinkT1Walk2) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractT1Walk2Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractT1Walk2Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkT1Walk2 extractLinkedCode
      ((.x1 ↦ᵣ LinkT1Walk2) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkT1Walk2) **
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
      simp only [extractT1Walk2Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec T1Walk2JalPc WN old1 t1Walk2JalOff 87
    t1Walk2JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E T1Walk2JalPc extractProg 108
        (.JAL .x1 t1Walk2JalOff) (by simp only [T1Walk2JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (T1Walk2JalPc + 4 : Word) = LinkT1Walk2 from by
    simp only [T1Walk2JalPc, LinkT1Walk2]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractT1Walk2Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractT1Walk2BneOk :
    cpsTripleWithin 1 LinkT1Walk2 AfterT1Walk2Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (116 : BitVec 13)
    (0 : Word) (0 : Word) LinkT1Walk2
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkT1Walk2 extractProg 109
        (.BNE .x11 .x0 (116 : BitVec 13)) (by simp only [LinkT1Walk2]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkT1Walk2 + 4 : Word) = AfterT1Walk2Bne from by
    simp only [LinkT1Walk2, AfterT1Walk2Bne]; bv_omega] at hnt
  exact hnt

abbrev T1Walk3JalPc : Word := E + 452
abbrev LinkT1Walk3 : Word := E + 456
abbrev AfterT1Walk3Bne : Word := E + 460

set_option maxRecDepth 8000 in
theorem extractT1Walk3Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk2Bne T1Walk3JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have s0 : cpsTripleWithin 1 AfterT1Walk2Bne (E + 444) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterT1Walk2Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterT1Walk2Bne extractProg 110
          (.MV .x21 .x10) (by simp only [AfterT1Walk2Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterT1Walk2Bne + 4 : Word) = E + 444 from by
      simp only [AfterT1Walk2Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s1 : cpsTripleWithin 1 (E + 444) (E + 448) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 444) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 444) extractProg 111
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 444 : Word) + 4) = E + 448 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s2 : cpsTripleWithin 1 (E + 448) T1Walk3JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 448) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 448) extractProg 112
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 448 : Word) + 4) = T1Walk3JalPc from by
      simp only [T1Walk3JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def t1Walk3JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 452)

theorem t1Walk3JalOff_resolves :
    T1Walk3JalPc + signExtend21 t1Walk3JalOff = WN := by
  simp only [T1Walk3JalPc, WN, t1Walk3JalOff, E]; decide

def extractT1Walk3Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk3) **
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
theorem extractT1Walk3Call
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
    cpsTripleWithin (1 + 87) T1Walk3JalPc LinkT1Walk3 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractT1Walk3Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkT1Walk3 &&& ~~~(1 : Word)) = LinkT1Walk3 := by
    simp only [LinkT1Walk3, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkT1Walk3 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkT1Walk3 walkNextCode
      ((.x1 ↦ᵣ LinkT1Walk3) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractT1Walk3Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractT1Walk3Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkT1Walk3 extractLinkedCode
      ((.x1 ↦ᵣ LinkT1Walk3) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkT1Walk3) **
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
      simp only [extractT1Walk3Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec T1Walk3JalPc WN old1 t1Walk3JalOff 87
    t1Walk3JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E T1Walk3JalPc extractProg 113
        (.JAL .x1 t1Walk3JalOff) (by simp only [T1Walk3JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (T1Walk3JalPc + 4 : Word) = LinkT1Walk3 from by
    simp only [T1Walk3JalPc, LinkT1Walk3]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractT1Walk3Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractT1Walk3BneOk :
    cpsTripleWithin 1 LinkT1Walk3 AfterT1Walk3Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (96 : BitVec 13)
    (0 : Word) (0 : Word) LinkT1Walk3
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkT1Walk3 extractProg 114
        (.BNE .x11 .x0 (96 : BitVec 13)) (by simp only [LinkT1Walk3]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkT1Walk3 + 4 : Word) = AfterT1Walk3Bne from by
    simp only [LinkT1Walk3, AfterT1Walk3Bne]; bv_omega] at hnt
  exact hnt

abbrev T1Walk4JalPc : Word := E + 472
abbrev LinkT1Walk4 : Word := E + 476
abbrev AfterT1Walk4Bne : Word := E + 480

set_option maxRecDepth 8000 in
theorem extractT1Walk4Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk3Bne T1Walk4JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have s0 : cpsTripleWithin 1 AfterT1Walk3Bne (E + 464) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterT1Walk3Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterT1Walk3Bne extractProg 115
          (.MV .x21 .x10) (by simp only [AfterT1Walk3Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterT1Walk3Bne + 4 : Word) = E + 464 from by
      simp only [AfterT1Walk3Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s1 : cpsTripleWithin 1 (E + 464) (E + 468) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 464) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 464) extractProg 116
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 464 : Word) + 4) = E + 468 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s2 : cpsTripleWithin 1 (E + 468) T1Walk4JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 468) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 468) extractProg 117
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 468 : Word) + 4) = T1Walk4JalPc from by
      simp only [T1Walk4JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def t1Walk4JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 472)

theorem t1Walk4JalOff_resolves :
    T1Walk4JalPc + signExtend21 t1Walk4JalOff = WN := by
  simp only [T1Walk4JalPc, WN, t1Walk4JalOff, E]; decide

def extractT1Walk4Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
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
theorem extractT1Walk4Call
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
    cpsTripleWithin (1 + 87) T1Walk4JalPc LinkT1Walk4 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractT1Walk4Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkT1Walk4 &&& ~~~(1 : Word)) = LinkT1Walk4 := by
    simp only [LinkT1Walk4, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkT1Walk4 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkT1Walk4 walkNextCode
      ((.x1 ↦ᵣ LinkT1Walk4) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractT1Walk4Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractT1Walk4Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkT1Walk4 extractLinkedCode
      ((.x1 ↦ᵣ LinkT1Walk4) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkT1Walk4) **
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
      simp only [extractT1Walk4Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec T1Walk4JalPc WN old1 t1Walk4JalOff 87
    t1Walk4JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E T1Walk4JalPc extractProg 118
        (.JAL .x1 t1Walk4JalOff) (by simp only [T1Walk4JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (T1Walk4JalPc + 4 : Word) = LinkT1Walk4 from by
    simp only [T1Walk4JalPc, LinkT1Walk4]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractT1Walk4Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractT1Walk4BneOk :
    cpsTripleWithin 1 LinkT1Walk4 AfterT1Walk4Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (76 : BitVec 13)
    (0 : Word) (0 : Word) LinkT1Walk4
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkT1Walk4 extractProg 119
        (.BNE .x11 .x0 (76 : BitVec 13)) (by simp only [LinkT1Walk4]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkT1Walk4 + 4 : Word) = AfterT1Walk4Bne from by
    simp only [LinkT1Walk4, AfterT1Walk4Bne]; bv_omega] at hnt
  exact hnt

set_option maxRecDepth 8000 in
/-- t1: `sub t6,a0,a2` AfterT1Walk4Bne → HaveField (fall-through). -/
theorem extractT1ToHaveField (a0 a2 t6Old : Word) :
    cpsTripleWithin 1 AfterT1Walk4Bne HaveField extractLinkedCode
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ t6Old))
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ (a0 - a2))) := by
  have hs := sub_spec_gen_within .x31 .x10 .x12 a0 a2 t6Old AfterT1Walk4Bne (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterT1Walk4Bne extractProg 120
        (.SUB .x31 .x10 .x12) (by simp only [AfterT1Walk4Bne]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hs
  simpa only [HaveField, AfterT1Walk4Bne] using he

#print axioms extractT1LoadArgs
#print axioms extractT1Walk0Call
#print axioms extractT1Walk4BneOk
#print axioms extractT1ToHaveField

end EvmAsm.Codegen.TxExtractToAddressSpec
