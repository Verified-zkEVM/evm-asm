/-
  Extract body: legacy (type 0) walk_next chain (4 skips) + SUB/JAL HaveField.
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

abbrev LegacyWalk0JalPc : Word := E + 308
abbrev LinkLegacyWalk0 : Word := E + 312
abbrev AfterLegacyWalk0Bne : Word := E + 316

set_option maxRecDepth 8000 in
theorem extractLegacyLoadArgs (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin (1 + 1) LegacyStart LegacyWalk0JalPc extractLinkedCode
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have hm0 := mv_spec_gen_within .x10 .x21 cursor a0Old LegacyStart (by decide)
  have he0 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LegacyStart extractProg 75
        (.MV .x10 .x21) (by simp only [LegacyStart]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hm0
  rw [show (LegacyStart + 4 : Word) = E + 304 from by
    simp only [LegacyStart]; bv_omega] at he0
  have hm0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he0
  have hm1 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 304) (by decide)
  have he1 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 304) extractProg 76
        (.MV .x11 .x22) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hm1
  rw [show ((E + 304 : Word) + 4) = LegacyWalk0JalPc from by
    simp only [LegacyWalk0JalPc]; bv_omega] at he1
  have hm1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) he1
  have h := cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) hm0F hm1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h

private def legacyWalk0JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 308)

theorem legacyWalk0JalOff_resolves :
    LegacyWalk0JalPc + signExtend21 legacyWalk0JalOff = WN := by
  simp only [LegacyWalk0JalPc, WN, legacyWalk0JalOff, E]; decide

def extractLegacyWalk0Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk0) **
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
theorem extractLegacyWalk0Call
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
    cpsTripleWithin (1 + 87) LegacyWalk0JalPc LinkLegacyWalk0 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractLegacyWalk0Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkLegacyWalk0 &&& ~~~(1 : Word)) = LinkLegacyWalk0 := by
    simp only [LinkLegacyWalk0, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkLegacyWalk0 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkLegacyWalk0 walkNextCode
      ((.x1 ↦ᵣ LinkLegacyWalk0) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractLegacyWalk0Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractLegacyWalk0Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkLegacyWalk0 extractLinkedCode
      ((.x1 ↦ᵣ LinkLegacyWalk0) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkLegacyWalk0) **
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
      simp only [extractLegacyWalk0Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec LegacyWalk0JalPc WN old1 legacyWalk0JalOff 87
    legacyWalk0JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LegacyWalk0JalPc extractProg 77
        (.JAL .x1 legacyWalk0JalOff) (by simp only [LegacyWalk0JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (LegacyWalk0JalPc + 4 : Word) = LinkLegacyWalk0 from by
    simp only [LegacyWalk0JalPc, LinkLegacyWalk0]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractLegacyWalk0Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractLegacyWalk0BneOk :
    cpsTripleWithin 1 LinkLegacyWalk0 AfterLegacyWalk0Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (240 : BitVec 13)
    (0 : Word) (0 : Word) LinkLegacyWalk0
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkLegacyWalk0 extractProg 78
        (.BNE .x11 .x0 (240 : BitVec 13)) (by simp only [LinkLegacyWalk0]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkLegacyWalk0 + 4 : Word) = AfterLegacyWalk0Bne from by
    simp only [LinkLegacyWalk0, AfterLegacyWalk0Bne]; bv_omega] at hnt
  exact hnt

abbrev LegacyWalk1JalPc : Word := E + 328
abbrev LinkLegacyWalk1 : Word := E + 332
abbrev AfterLegacyWalk1Bne : Word := E + 336

set_option maxRecDepth 8000 in
theorem extractLegacyWalk1Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk0Bne LegacyWalk1JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have s0 : cpsTripleWithin 1 AfterLegacyWalk0Bne (E + 320) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterLegacyWalk0Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterLegacyWalk0Bne extractProg 79
          (.MV .x21 .x10) (by simp only [AfterLegacyWalk0Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterLegacyWalk0Bne + 4 : Word) = E + 320 from by
      simp only [AfterLegacyWalk0Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s1 : cpsTripleWithin 1 (E + 320) (E + 324) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 320) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 320) extractProg 80
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 320 : Word) + 4) = E + 324 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s2 : cpsTripleWithin 1 (E + 324) LegacyWalk1JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 324) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 324) extractProg 81
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 324 : Word) + 4) = LegacyWalk1JalPc from by
      simp only [LegacyWalk1JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def legacyWalk1JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 328)

theorem legacyWalk1JalOff_resolves :
    LegacyWalk1JalPc + signExtend21 legacyWalk1JalOff = WN := by
  simp only [LegacyWalk1JalPc, WN, legacyWalk1JalOff, E]; decide

def extractLegacyWalk1Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk1) **
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
theorem extractLegacyWalk1Call
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
    cpsTripleWithin (1 + 87) LegacyWalk1JalPc LinkLegacyWalk1 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractLegacyWalk1Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkLegacyWalk1 &&& ~~~(1 : Word)) = LinkLegacyWalk1 := by
    simp only [LinkLegacyWalk1, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkLegacyWalk1 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkLegacyWalk1 walkNextCode
      ((.x1 ↦ᵣ LinkLegacyWalk1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractLegacyWalk1Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractLegacyWalk1Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkLegacyWalk1 extractLinkedCode
      ((.x1 ↦ᵣ LinkLegacyWalk1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkLegacyWalk1) **
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
      simp only [extractLegacyWalk1Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec LegacyWalk1JalPc WN old1 legacyWalk1JalOff 87
    legacyWalk1JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LegacyWalk1JalPc extractProg 82
        (.JAL .x1 legacyWalk1JalOff) (by simp only [LegacyWalk1JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (LegacyWalk1JalPc + 4 : Word) = LinkLegacyWalk1 from by
    simp only [LegacyWalk1JalPc, LinkLegacyWalk1]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractLegacyWalk1Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractLegacyWalk1BneOk :
    cpsTripleWithin 1 LinkLegacyWalk1 AfterLegacyWalk1Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (220 : BitVec 13)
    (0 : Word) (0 : Word) LinkLegacyWalk1
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkLegacyWalk1 extractProg 83
        (.BNE .x11 .x0 (220 : BitVec 13)) (by simp only [LinkLegacyWalk1]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkLegacyWalk1 + 4 : Word) = AfterLegacyWalk1Bne from by
    simp only [LinkLegacyWalk1, AfterLegacyWalk1Bne]; bv_omega] at hnt
  exact hnt

abbrev LegacyWalk2JalPc : Word := E + 348
abbrev LinkLegacyWalk2 : Word := E + 352
abbrev AfterLegacyWalk2Bne : Word := E + 356

set_option maxRecDepth 8000 in
theorem extractLegacyWalk2Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk1Bne LegacyWalk2JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have s0 : cpsTripleWithin 1 AfterLegacyWalk1Bne (E + 340) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterLegacyWalk1Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterLegacyWalk1Bne extractProg 84
          (.MV .x21 .x10) (by simp only [AfterLegacyWalk1Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterLegacyWalk1Bne + 4 : Word) = E + 340 from by
      simp only [AfterLegacyWalk1Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s1 : cpsTripleWithin 1 (E + 340) (E + 344) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 340) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 340) extractProg 85
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 340 : Word) + 4) = E + 344 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s2 : cpsTripleWithin 1 (E + 344) LegacyWalk2JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 344) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 344) extractProg 86
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 344 : Word) + 4) = LegacyWalk2JalPc from by
      simp only [LegacyWalk2JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def legacyWalk2JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 348)

theorem legacyWalk2JalOff_resolves :
    LegacyWalk2JalPc + signExtend21 legacyWalk2JalOff = WN := by
  simp only [LegacyWalk2JalPc, WN, legacyWalk2JalOff, E]; decide

def extractLegacyWalk2Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk2) **
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
theorem extractLegacyWalk2Call
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
    cpsTripleWithin (1 + 87) LegacyWalk2JalPc LinkLegacyWalk2 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractLegacyWalk2Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkLegacyWalk2 &&& ~~~(1 : Word)) = LinkLegacyWalk2 := by
    simp only [LinkLegacyWalk2, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkLegacyWalk2 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkLegacyWalk2 walkNextCode
      ((.x1 ↦ᵣ LinkLegacyWalk2) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractLegacyWalk2Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractLegacyWalk2Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkLegacyWalk2 extractLinkedCode
      ((.x1 ↦ᵣ LinkLegacyWalk2) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkLegacyWalk2) **
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
      simp only [extractLegacyWalk2Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec LegacyWalk2JalPc WN old1 legacyWalk2JalOff 87
    legacyWalk2JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LegacyWalk2JalPc extractProg 87
        (.JAL .x1 legacyWalk2JalOff) (by simp only [LegacyWalk2JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (LegacyWalk2JalPc + 4 : Word) = LinkLegacyWalk2 from by
    simp only [LegacyWalk2JalPc, LinkLegacyWalk2]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractLegacyWalk2Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractLegacyWalk2BneOk :
    cpsTripleWithin 1 LinkLegacyWalk2 AfterLegacyWalk2Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (200 : BitVec 13)
    (0 : Word) (0 : Word) LinkLegacyWalk2
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkLegacyWalk2 extractProg 88
        (.BNE .x11 .x0 (200 : BitVec 13)) (by simp only [LinkLegacyWalk2]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkLegacyWalk2 + 4 : Word) = AfterLegacyWalk2Bne from by
    simp only [LinkLegacyWalk2, AfterLegacyWalk2Bne]; bv_omega] at hnt
  exact hnt

abbrev LegacyWalk3JalPc : Word := E + 368
abbrev LinkLegacyWalk3 : Word := E + 372
abbrev AfterLegacyWalk3Bne : Word := E + 376

set_option maxRecDepth 8000 in
theorem extractLegacyWalk3Prep (cursor endPtr s5Old a1Old : Word) :
    cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk2Bne LegacyWalk3JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have s0 : cpsTripleWithin 1 AfterLegacyWalk2Bne (E + 360) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x21 .x10 cursor s5Old AfterLegacyWalk2Bne (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E AfterLegacyWalk2Bne extractProg 89
          (.MV .x21 .x10) (by simp only [AfterLegacyWalk2Bne]; bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show (AfterLegacyWalk2Bne + 4 : Word) = E + 360 from by
      simp only [AfterLegacyWalk2Bne]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s1 : cpsTripleWithin 1 (E + 360) (E + 364) extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old)) := by
    have hm := mv_spec_gen_within .x10 .x21 cursor cursor (E + 360) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 360) extractProg 90
          (.MV .x10 .x21) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 360 : Word) + 4) = E + 364 from by bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  have s2 : cpsTripleWithin 1 (E + 364) LegacyWalk3JalPc extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
    have hm := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 364) (by decide)
    have he := cpsTripleWithin_extend_code
      (fun a i hi => extract_mono a i
        (CodeReq.ofProg_mem_at E (E + 364) extractProg 91
          (.MV .x11 .x22) (by bv_omega)
          (by rw [extract_length]; decide) rfl
          (by rw [extract_length]; decide) a i hi)) hm
    rw [show ((E + 364 : Word) + 4) = LegacyWalk3JalPc from by
      simp only [LegacyWalk3JalPc]; bv_omega] at he
    have hf := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hf
  exact cpsTripleWithin_seq_same_cr s0 (cpsTripleWithin_seq_same_cr s1 s2)

private def legacyWalk3JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 368)

theorem legacyWalk3JalOff_resolves :
    LegacyWalk3JalPc + signExtend21 legacyWalk3JalOff = WN := by
  simp only [LegacyWalk3JalPc, WN, legacyWalk3JalOff, E]; decide

def extractLegacyWalk3Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
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
theorem extractLegacyWalk3Call
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
    cpsTripleWithin (1 + 87) LegacyWalk3JalPc LinkLegacyWalk3 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractLegacyWalk3Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkLegacyWalk3 &&& ~~~(1 : Word)) = LinkLegacyWalk3 := by
    simp only [LinkLegacyWalk3, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkLegacyWalk3 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkLegacyWalk3 walkNextCode
      ((.x1 ↦ᵣ LinkLegacyWalk3) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractLegacyWalk3Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractLegacyWalk3Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkLegacyWalk3 extractLinkedCode
      ((.x1 ↦ᵣ LinkLegacyWalk3) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkLegacyWalk3) **
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
      simp only [extractLegacyWalk3Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec LegacyWalk3JalPc WN old1 legacyWalk3JalOff 87
    legacyWalk3JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LegacyWalk3JalPc extractProg 92
        (.JAL .x1 legacyWalk3JalOff) (by simp only [LegacyWalk3JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (LegacyWalk3JalPc + 4 : Word) = LinkLegacyWalk3 from by
    simp only [LegacyWalk3JalPc, LinkLegacyWalk3]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractLegacyWalk3Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
theorem extractLegacyWalk3BneOk :
    cpsTripleWithin 1 LinkLegacyWalk3 AfterLegacyWalk3Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (180 : BitVec 13)
    (0 : Word) (0 : Word) LinkLegacyWalk3
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkLegacyWalk3 extractProg 93
        (.BNE .x11 .x0 (180 : BitVec 13)) (by simp only [LinkLegacyWalk3]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkLegacyWalk3 + 4 : Word) = AfterLegacyWalk3Bne from by
    simp only [LinkLegacyWalk3, AfterLegacyWalk3Bne]; bv_omega] at hnt
  exact hnt

abbrev LegacySubPc : Word := E + 376
abbrev LegacyJalHavePc : Word := E + 380

set_option maxRecDepth 8000 in
theorem extractLegacySub (a0 a2 t6Old : Word) :
    cpsTripleWithin 1 AfterLegacyWalk3Bne LegacyJalHavePc extractLinkedCode
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ t6Old))
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ (a0 - a2))) := by
  have hs := sub_spec_gen_within .x31 .x10 .x12 a0 a2 t6Old AfterLegacyWalk3Bne (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterLegacyWalk3Bne extractProg 94
        (.SUB .x31 .x10 .x12) (by simp only [AfterLegacyWalk3Bne]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hs
  simpa only [LegacyJalHavePc, AfterLegacyWalk3Bne] using he

set_option maxRecDepth 8000 in
theorem extractLegacyJalHave :
    cpsTripleWithin 1 LegacyJalHavePc HaveField extractLinkedCode
      empAssertion empAssertion := by
  have hj := jal_x0_spec_gen_within (104 : BitVec 21) LegacyJalHavePc
  have ht : LegacyJalHavePc + signExtend21 (104 : BitVec 21) = HaveField := by
    simp only [LegacyJalHavePc, HaveField, E]
    rw [show signExtend21 (104 : BitVec 21) = (104 : Word) from by decide]
    bv_omega
  rw [ht] at hj
  exact cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LegacyJalHavePc extractProg 95
        (.JAL .x0 (104 : BitVec 21)) (by simp only [LegacyJalHavePc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hj

set_option maxRecDepth 8000 in
theorem extractLegacyToHaveField (a0 a2 t6Old : Word) :
    cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ t6Old))
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ (a0 - a2))) := by
  have hs := extractLegacySub a0 a2 t6Old
  have hjF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ (a0 - a2))) (by pcf)
    extractLegacyJalHave
  have hjF' : cpsTripleWithin 1 LegacyJalHavePc HaveField extractLinkedCode
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ (a0 - a2)))
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ (a0 - a2))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simpa only [sepConj_emp_left'] using hp) (fun _ hq => by
      simpa only [sepConj_emp_left'] using hq) hjF
  exact cpsTripleWithin_seq_same_cr hs hjF'


#print axioms extractLegacyLoadArgs
#print axioms extractLegacyWalk0Call
#print axioms extractLegacyWalk3BneOk
#print axioms extractLegacyToHaveField

end EvmAsm.Codegen.TxExtractToAddressSpec
