/-
  Extract body: save cursor after walk_init + first rlp_walk_next skip packaging.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkInit
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpWalkCallSAsm

/-- After MV s5/s6: type-branch setup at E+160. -/
abbrev AfterSaveCursor : Word := E + 160

/-- First type-2/3/4 walk_next JAL PC (instr 46). -/
abbrev WalkNext0JalPc : Word := E + 184
abbrev LinkWalkNext0 : Word := E + 188
abbrev AfterWalkNext0Bne : Word := E + 192

private def walkNext0JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 184)

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
/-- `mv s5, a0; mv s6, a1` at AfterWalkInitOk → AfterSaveCursor. -/
theorem extractSaveCursor
    (cursor endPtr s5Old s6Old : Word) :
    cpsTripleWithin (1 + 1) AfterWalkInitOk AfterSaveCursor extractLinkedCode
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ s5Old) ** (.x22 ↦ᵣ s6Old))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  have hm5 := mv_spec_gen_within .x21 .x10 cursor s5Old AfterWalkInitOk (by decide)
  have he5 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterWalkInitOk extractProg 38
        (.MV .x21 .x10) (by simp only [AfterWalkInitOk]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hm5
  rw [show (AfterWalkInitOk + 4 : Word) = E + 156 from by
    simp only [AfterWalkInitOk]; bv_omega] at he5
  have hm5F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x22 ↦ᵣ s6Old)) (by pcf) he5
  have hm6 := mv_spec_gen_within .x22 .x11 endPtr s6Old (E + 156) (by decide)
  have he6 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 156) extractProg 39
        (.MV .x22 .x11) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hm6
  rw [show ((E + 156 : Word) + 4) = AfterSaveCursor from by
    simp only [AfterSaveCursor]; bv_omega] at he6
  have hm6F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ cursor) ** (.x21 ↦ᵣ cursor)) (by pcf) he6
  have h := cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) hm5F hm6F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h

theorem walkNext0JalOff_resolves :
    WalkNext0JalPc + signExtend21 walkNext0JalOff = WN := by
  simp only [WalkNext0JalPc, WN, walkNext0JalOff, E]; decide

/-- Prest for one walk_next call (cursor in a0, end in a1). -/
def extractWalkNextPrest (cursor endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
    (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion txBase txBytes

theorem extractWalkNextPrest_pcFree
    (cursor endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBase : Word) (txBytes : List (BitVec 8)) :
    (extractWalkNextPrest cursor endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      txBase txBytes).pcFree := by
  unfold extractWalkNextPrest; pcf

/-- Leaf-shaped post under walk_next (full 6-way); ra = LinkWalkNext0. -/
def extractWalkNext0Post (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext0) **
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
/-- First type-2/3/4 `jal rlp_walk_next` under extractLinkedCode (cursor = base+srcOff). -/
theorem extractWalkNext0Call
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
    cpsTripleWithin (1 + 87) WalkNext0JalPc LinkWalkNext0 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext0Post txBase endPtr txBytes srcOff) := by
  have hret : (LinkWalkNext0 &&& ~~~(1 : Word)) = LinkWalkNext0 := by
    simp only [LinkWalkNext0, E]; decide
  have hleaf := rlp_walk_next_spec_within WN txBase endPtr LinkWalkNext0 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext0 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext0) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      (extractWalkNext0Post txBase endPtr txBytes srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractWalkNext0Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkNext_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext0 extractLinkedCode
      ((.x1 ↦ᵣ LinkWalkNext0) **
        extractWalkNextPrest (txBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
      ((.x1 ↦ᵣ LinkWalkNext0) **
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
      simp only [extractWalkNext0Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext0JalPc WN old1 walkNext0JalOff 87
    walkNext0JalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E WalkNext0JalPc extractProg 46
        (.JAL .x1 walkNext0JalOff) (by simp only [WalkNext0JalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkNextPrest_pcFree (txBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBase txBytes)
    hcallee'
  rw [show (WalkNext0JalPc + 4 : Word) = LinkWalkNext0 from by
    simp only [WalkNext0JalPc, LinkWalkNext0]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractWalkNext0Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- BNE a1,x0 field_fail not-taken when a1=0 → AfterWalkNext0Bne. -/
theorem extractWalkNext0BneOk :
    cpsTripleWithin 1 LinkWalkNext0 AfterWalkNext0Bne extractLinkedCode
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 (364 : BitVec 13)
    (0 : Word) (0 : Word) LinkWalkNext0
  have hbr' := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkWalkNext0 extractProg 47
        (.BNE .x11 .x0 (364 : BitVec 13)) (by simp only [LinkWalkNext0]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr' (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (LinkWalkNext0 + 4 : Word) = AfterWalkNext0Bne from by
    simp only [LinkWalkNext0, AfterWalkNext0Bne]; bv_omega] at hnt
  exact hnt

#print axioms extractSaveCursor
#print axioms extractWalkNext0Call
#print axioms extractWalkNext0BneOk

end EvmAsm.Codegen.TxExtractToAddressSpec
