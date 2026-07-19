/-
  Teer: walk_next skip cycles 1–5 after first cycle.
  Each: MV a0,s8; MV a1,s9; JAL walk_next; BNE a1≠0; MV s8,a0.
  jal @ E+260/280/300/320/340 → AfterWalkNext5Save (E+352).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxEip7702TeerSpec
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkInit
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNext0
import EvmAsm.Rv64.SAsm.RwSubwindow
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

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

/-- 6-way post with arbitrary link ra. -/
def teerWalkNextPost (linkPc listBase endPtr : Word) (bs : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ linkPc) **
    bytesRegion listBase bs) **
   (fun h =>
     rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff h ∨
     (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
     (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h) ∨
     (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
          endPtr next len⌝) h)))


/-! ## Cycle 1 @ jal E+260 -/

abbrev WalkNext1JalPc : Word := E + 260
abbrev LinkWalkNext1 : Word := E + 264
abbrev AfterWalkNext1Bne : Word := E + 268
abbrev AfterWalkNext1Save : Word := E + 272
def walkNext1JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 260)
abbrev teerWalkNext1BneOff : BitVec 13 := (2592 : BitVec 13)

theorem walkNext1JalOff_resolves :
    (WalkNext1JalPc + signExtend21 walkNext1JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [WalkNext1JalPc, WN, walkNext1JalOff, E]; decide

theorem teerWalkNext1MvA0S8 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterWalkNext0Save (E + 256) teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x24 cursor a0Old AfterWalkNext0Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNext0Save teerProg 63
        (.MV .x10 .x24) (by simp only [AfterWalkNext0Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkNext0Save + 4 : Word) = E + 256 := by
    simp only [AfterWalkNext0Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNext1MvA1S9 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 256) WalkNext1JalPc teerLinkedEarly
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x25 endPtr a1Old (E + 256) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 256) teerProg 64
        (.MV .x11 .x25) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 256 : Word) + 4) = WalkNext1JalPc := by
    simp only [WalkNext1JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNext1Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterWalkNext0Save WalkNext1JalPc teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerWalkNext1MvA0S8 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerWalkNext1MvA1S9 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerWalkNext1Call
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext1JalPc LinkWalkNext1 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNext1 listBase endPtr bs srcOff) := by
  have hret : (LinkWalkNext1 &&& ~~~(1 : Word)) = LinkWalkNext1 := by
    simp only [LinkWalkNext1, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkWalkNext1 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext1 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNext1 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext1 teerLinkedEarly
      ((.x1 ↦ᵣ LinkWalkNext1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkWalkNext1) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) **
         (fun h =>
           rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff h ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext1JalPc WN old1 walkNext1JalOff 87
    walkNext1JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E WalkNext1JalPc teerProg 65
        (.JAL .x1 walkNext1JalOff) (by simp only [WalkNext1JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (WalkNext1JalPc + 4 : Word) = LinkWalkNext1 from by
    simp only [WalkNext1JalPc, LinkWalkNext1]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerWalkNext1BneOk :
    cpsTripleWithin 1 LinkWalkNext1 AfterWalkNext1Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerWalkNext1BneOff
    (0 : Word) (0 : Word) LinkWalkNext1
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkWalkNext1 teerProg 66
        (.BNE .x11 .x0 teerWalkNext1BneOff)
        (by simp only [LinkWalkNext1]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkNext1 + 4 = AfterWalkNext1Bne := by
    simp only [LinkWalkNext1, AfterWalkNext1Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerWalkNext1SaveS8 (next v24 : Word) :
    cpsTripleWithin 1 AfterWalkNext1Bne AfterWalkNext1Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ v24))
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x24 .x10 next v24 AfterWalkNext1Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNext1Bne teerProg 67
        (.MV .x24 .x10) (by simp only [AfterWalkNext1Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkNext1Bne + 4 : Word) = AfterWalkNext1Save := by
    simp only [AfterWalkNext1Bne, AfterWalkNext1Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Cycle 2 @ jal E+280 -/

abbrev WalkNext2JalPc : Word := E + 280
abbrev LinkWalkNext2 : Word := E + 284
abbrev AfterWalkNext2Bne : Word := E + 288
abbrev AfterWalkNext2Save : Word := E + 292
def walkNext2JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 280)
abbrev teerWalkNext2BneOff : BitVec 13 := (2572 : BitVec 13)

theorem walkNext2JalOff_resolves :
    (WalkNext2JalPc + signExtend21 walkNext2JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [WalkNext2JalPc, WN, walkNext2JalOff, E]; decide

theorem teerWalkNext2MvA0S8 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterWalkNext1Save (E + 276) teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x24 cursor a0Old AfterWalkNext1Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNext1Save teerProg 68
        (.MV .x10 .x24) (by simp only [AfterWalkNext1Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkNext1Save + 4 : Word) = E + 276 := by
    simp only [AfterWalkNext1Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNext2MvA1S9 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 276) WalkNext2JalPc teerLinkedEarly
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x25 endPtr a1Old (E + 276) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 276) teerProg 69
        (.MV .x11 .x25) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 276 : Word) + 4) = WalkNext2JalPc := by
    simp only [WalkNext2JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNext2Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterWalkNext1Save WalkNext2JalPc teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerWalkNext2MvA0S8 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerWalkNext2MvA1S9 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerWalkNext2Call
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext2JalPc LinkWalkNext2 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNext2 listBase endPtr bs srcOff) := by
  have hret : (LinkWalkNext2 &&& ~~~(1 : Word)) = LinkWalkNext2 := by
    simp only [LinkWalkNext2, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkWalkNext2 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext2 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext2) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNext2 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext2 teerLinkedEarly
      ((.x1 ↦ᵣ LinkWalkNext2) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkWalkNext2) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) **
         (fun h =>
           rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff h ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext2JalPc WN old1 walkNext2JalOff 87
    walkNext2JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E WalkNext2JalPc teerProg 70
        (.JAL .x1 walkNext2JalOff) (by simp only [WalkNext2JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (WalkNext2JalPc + 4 : Word) = LinkWalkNext2 from by
    simp only [WalkNext2JalPc, LinkWalkNext2]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerWalkNext2BneOk :
    cpsTripleWithin 1 LinkWalkNext2 AfterWalkNext2Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerWalkNext2BneOff
    (0 : Word) (0 : Word) LinkWalkNext2
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkWalkNext2 teerProg 71
        (.BNE .x11 .x0 teerWalkNext2BneOff)
        (by simp only [LinkWalkNext2]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkNext2 + 4 = AfterWalkNext2Bne := by
    simp only [LinkWalkNext2, AfterWalkNext2Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerWalkNext2SaveS8 (next v24 : Word) :
    cpsTripleWithin 1 AfterWalkNext2Bne AfterWalkNext2Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ v24))
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x24 .x10 next v24 AfterWalkNext2Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNext2Bne teerProg 72
        (.MV .x24 .x10) (by simp only [AfterWalkNext2Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkNext2Bne + 4 : Word) = AfterWalkNext2Save := by
    simp only [AfterWalkNext2Bne, AfterWalkNext2Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Cycle 3 @ jal E+300 -/

abbrev WalkNext3JalPc : Word := E + 300
abbrev LinkWalkNext3 : Word := E + 304
abbrev AfterWalkNext3Bne : Word := E + 308
abbrev AfterWalkNext3Save : Word := E + 312
def walkNext3JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 300)
abbrev teerWalkNext3BneOff : BitVec 13 := (2552 : BitVec 13)

theorem walkNext3JalOff_resolves :
    (WalkNext3JalPc + signExtend21 walkNext3JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [WalkNext3JalPc, WN, walkNext3JalOff, E]; decide

theorem teerWalkNext3MvA0S8 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterWalkNext2Save (E + 296) teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x24 cursor a0Old AfterWalkNext2Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNext2Save teerProg 73
        (.MV .x10 .x24) (by simp only [AfterWalkNext2Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkNext2Save + 4 : Word) = E + 296 := by
    simp only [AfterWalkNext2Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNext3MvA1S9 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 296) WalkNext3JalPc teerLinkedEarly
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x25 endPtr a1Old (E + 296) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 296) teerProg 74
        (.MV .x11 .x25) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 296 : Word) + 4) = WalkNext3JalPc := by
    simp only [WalkNext3JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNext3Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterWalkNext2Save WalkNext3JalPc teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerWalkNext3MvA0S8 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerWalkNext3MvA1S9 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerWalkNext3Call
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext3JalPc LinkWalkNext3 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNext3 listBase endPtr bs srcOff) := by
  have hret : (LinkWalkNext3 &&& ~~~(1 : Word)) = LinkWalkNext3 := by
    simp only [LinkWalkNext3, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkWalkNext3 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext3 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext3) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNext3 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext3 teerLinkedEarly
      ((.x1 ↦ᵣ LinkWalkNext3) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkWalkNext3) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) **
         (fun h =>
           rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff h ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext3JalPc WN old1 walkNext3JalOff 87
    walkNext3JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E WalkNext3JalPc teerProg 75
        (.JAL .x1 walkNext3JalOff) (by simp only [WalkNext3JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (WalkNext3JalPc + 4 : Word) = LinkWalkNext3 from by
    simp only [WalkNext3JalPc, LinkWalkNext3]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerWalkNext3BneOk :
    cpsTripleWithin 1 LinkWalkNext3 AfterWalkNext3Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerWalkNext3BneOff
    (0 : Word) (0 : Word) LinkWalkNext3
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkWalkNext3 teerProg 76
        (.BNE .x11 .x0 teerWalkNext3BneOff)
        (by simp only [LinkWalkNext3]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkNext3 + 4 = AfterWalkNext3Bne := by
    simp only [LinkWalkNext3, AfterWalkNext3Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerWalkNext3SaveS8 (next v24 : Word) :
    cpsTripleWithin 1 AfterWalkNext3Bne AfterWalkNext3Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ v24))
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x24 .x10 next v24 AfterWalkNext3Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNext3Bne teerProg 77
        (.MV .x24 .x10) (by simp only [AfterWalkNext3Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkNext3Bne + 4 : Word) = AfterWalkNext3Save := by
    simp only [AfterWalkNext3Bne, AfterWalkNext3Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Cycle 4 @ jal E+320 -/

abbrev WalkNext4JalPc : Word := E + 320
abbrev LinkWalkNext4 : Word := E + 324
abbrev AfterWalkNext4Bne : Word := E + 328
abbrev AfterWalkNext4Save : Word := E + 332
def walkNext4JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 320)
abbrev teerWalkNext4BneOff : BitVec 13 := (2532 : BitVec 13)

theorem walkNext4JalOff_resolves :
    (WalkNext4JalPc + signExtend21 walkNext4JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [WalkNext4JalPc, WN, walkNext4JalOff, E]; decide

theorem teerWalkNext4MvA0S8 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterWalkNext3Save (E + 316) teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x24 cursor a0Old AfterWalkNext3Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNext3Save teerProg 78
        (.MV .x10 .x24) (by simp only [AfterWalkNext3Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkNext3Save + 4 : Word) = E + 316 := by
    simp only [AfterWalkNext3Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNext4MvA1S9 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 316) WalkNext4JalPc teerLinkedEarly
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x25 endPtr a1Old (E + 316) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 316) teerProg 79
        (.MV .x11 .x25) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 316 : Word) + 4) = WalkNext4JalPc := by
    simp only [WalkNext4JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNext4Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterWalkNext3Save WalkNext4JalPc teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerWalkNext4MvA0S8 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerWalkNext4MvA1S9 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerWalkNext4Call
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext4JalPc LinkWalkNext4 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNext4 listBase endPtr bs srcOff) := by
  have hret : (LinkWalkNext4 &&& ~~~(1 : Word)) = LinkWalkNext4 := by
    simp only [LinkWalkNext4, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkWalkNext4 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext4 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext4) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNext4 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext4 teerLinkedEarly
      ((.x1 ↦ᵣ LinkWalkNext4) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkWalkNext4) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) **
         (fun h =>
           rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff h ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext4JalPc WN old1 walkNext4JalOff 87
    walkNext4JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E WalkNext4JalPc teerProg 80
        (.JAL .x1 walkNext4JalOff) (by simp only [WalkNext4JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (WalkNext4JalPc + 4 : Word) = LinkWalkNext4 from by
    simp only [WalkNext4JalPc, LinkWalkNext4]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerWalkNext4BneOk :
    cpsTripleWithin 1 LinkWalkNext4 AfterWalkNext4Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerWalkNext4BneOff
    (0 : Word) (0 : Word) LinkWalkNext4
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkWalkNext4 teerProg 81
        (.BNE .x11 .x0 teerWalkNext4BneOff)
        (by simp only [LinkWalkNext4]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkNext4 + 4 = AfterWalkNext4Bne := by
    simp only [LinkWalkNext4, AfterWalkNext4Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerWalkNext4SaveS8 (next v24 : Word) :
    cpsTripleWithin 1 AfterWalkNext4Bne AfterWalkNext4Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ v24))
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x24 .x10 next v24 AfterWalkNext4Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNext4Bne teerProg 82
        (.MV .x24 .x10) (by simp only [AfterWalkNext4Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkNext4Bne + 4 : Word) = AfterWalkNext4Save := by
    simp only [AfterWalkNext4Bne, AfterWalkNext4Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Cycle 5 @ jal E+340 -/

abbrev WalkNext5JalPc : Word := E + 340
abbrev LinkWalkNext5 : Word := E + 344
abbrev AfterWalkNext5Bne : Word := E + 348
/-- Cycle 5 has no MV s8; next is SUB for recipient_ptr (E+348). -/
abbrev AfterWalkNext5Save : Word := AfterWalkNext5Bne
def walkNext5JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 340)
abbrev teerWalkNext5BneOff : BitVec 13 := (2512 : BitVec 13)

theorem walkNext5JalOff_resolves :
    (WalkNext5JalPc + signExtend21 walkNext5JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [WalkNext5JalPc, WN, walkNext5JalOff, E]; decide

theorem teerWalkNext5MvA0S8 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterWalkNext4Save (E + 336) teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x24 cursor a0Old AfterWalkNext4Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNext4Save teerProg 83
        (.MV .x10 .x24) (by simp only [AfterWalkNext4Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkNext4Save + 4 : Word) = E + 336 := by
    simp only [AfterWalkNext4Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNext5MvA1S9 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 336) WalkNext5JalPc teerLinkedEarly
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x25 endPtr a1Old (E + 336) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 336) teerProg 84
        (.MV .x11 .x25) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 336 : Word) + 4) = WalkNext5JalPc := by
    simp only [WalkNext5JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNext5Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterWalkNext4Save WalkNext5JalPc teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerWalkNext5MvA0S8 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerWalkNext5MvA1S9 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerWalkNext5Call
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext5JalPc LinkWalkNext5 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNext5 listBase endPtr bs srcOff) := by
  have hret : (LinkWalkNext5 &&& ~~~(1 : Word)) = LinkWalkNext5 := by
    simp only [LinkWalkNext5, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkWalkNext5 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext5 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext5) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNext5 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext5 teerLinkedEarly
      ((.x1 ↦ᵣ LinkWalkNext5) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkWalkNext5) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) **
         (fun h =>
           rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff h ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext5JalPc WN old1 walkNext5JalOff 87
    walkNext5JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E WalkNext5JalPc teerProg 85
        (.JAL .x1 walkNext5JalOff) (by simp only [WalkNext5JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (WalkNext5JalPc + 4 : Word) = LinkWalkNext5 from by
    simp only [WalkNext5JalPc, LinkWalkNext5]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerWalkNext5BneOk :
    cpsTripleWithin 1 LinkWalkNext5 AfterWalkNext5Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerWalkNext5BneOff
    (0 : Word) (0 : Word) LinkWalkNext5
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkWalkNext5 teerProg 86
        (.BNE .x11 .x0 teerWalkNext5BneOff)
        (by simp only [LinkWalkNext5]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkNext5 + 4 = AfterWalkNext5Bne := by
    simp only [LinkWalkNext5, AfterWalkNext5Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt


#print axioms teerWalkNext1Prep
#print axioms teerWalkNext1Call
#print axioms teerWalkNext5Call

/-! ## Cycle 1 compose: Prep+Call+BNE+Save -/

/-- BNE framed under concrete ok regs (cycle 1). -/
theorem teerWalkNext1BneOk_framed
    (listBase next len : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 LinkWalkNext1 AfterWalkNext1Bne teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNext1BneOk
  have hF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

theorem teerWalkNext1OkNested_bne
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext1 AfterWalkNext1Bne teerLinkedEarly
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext1) **
        bytesRegion listBase bs) **
        rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff)
      (fun h => ∃ next len : Word,
        (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
          bytesRegion listBase bs) **
          ⌜rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
            endPtr next len⌝) h) := by
  let cursor := listBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext1) **
        bytesRegion listBase bs) **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hCom, hOk⟩ := hp
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
          bytesRegion listBase bs)))
    (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := teerWalkNext1BneOk_framed listBase next len bs
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

theorem teerWalkNext1SaveS8_framed
    (listBase next len v24 : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 AfterWalkNext1Bne AfterWalkNext1Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x24 ↦ᵣ v24) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x24 ↦ᵣ next) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNext1SaveS8 next v24
  have hF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

def teerWalkNext1Common (listBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext1) **
    bytesRegion listBase bs

theorem teerWalkNext1Post_to_commonOutcome
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, teerWalkNextPost LinkWalkNext1 listBase endPtr bs srcOff h →
      (teerWalkNext1Common listBase bs **
        teerWalkNext0Outcome listBase endPtr bs srcOff) h := by
  intro h hp
  simp only [teerWalkNextPost, teerWalkNext1Common, teerWalkNext0Outcome] at hp ⊢
  xperm_hyp hp

private abbrev nWalkNext1Cycle : Nat := 2 + (1 + 87) + 1 + 1

open EvmAsm.Rv64.SAsm (cpsTripleWithin_seq_exists_same_cr)

set_option maxRecDepth 8000 in
/-- Full cycle 1: Prep+Call+BNE ok+Save s8. -/
theorem teerWalkNext1CycleOk
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 v24 v25 a0Old a1Old : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ next len : Word,
      rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
        endPtr next len)
    (hinb : BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hcur : v24 = listBase + BitVec.ofNat 64 srcOff)
    (hend : v25 = endPtr) :
    let cursor := listBase + BitVec.ofNat 64 srcOff
    cpsTripleWithin nWalkNext1Cycle AfterWalkNext0Save AfterWalkNext1Save
      teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (fun h => ∃ next len : Word,
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x24 ↦ᵣ next) ** (.x25 ↦ᵣ endPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
          bytesRegion listBase bs **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h) := by
  intro cursor
  have hprep := teerWalkNext1Prep cursor endPtr a0Old a1Old
  have hprepF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) **
      (.x12 ↦ᵣ a2Old) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) hprep
  have hprep' :
      cpsTripleWithin 2 AfterWalkNext0Save WalkNext1JalPc teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [hcur, hend] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hprepF
  have hcall := teerWalkNext1Call listBase endPtr a2Old t0Old t1Old t2Old t3Old
    t4Old t5Old t6Old bs srcOff old1 hsalign hoff hover hvalid hss hls hll
  have hcallOk :
      cpsTripleWithin (1 + 87) WalkNext1JalPc LinkWalkNext1 teerLinkedEarly
        ((.x1 ↦ᵣ old1) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (teerWalkNext1Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hcall
    have hq' := teerWalkNext1Post_to_commonOutcome listBase endPtr bs srcOff h hq
    obtain ⟨hC, hO, hd, hu, hcom, hout⟩ := hq'
    exact ⟨hC, hO, hd, hu, hcom,
      teerWalkNext0Outcome_drop_fail_of_decode listBase endPtr bs srcOff
        hdec hinb hO hout⟩
  have hcallF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hcallOk
  have hcallF' :
      cpsTripleWithin (1 + 87) WalkNext1JalPc LinkWalkNext1 teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNext1Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hcallF
  have hseq1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [teerWalkNextPrest] at hp ⊢
    xperm_hyp hp) hprep' hcallF'
  have hbne := teerWalkNext1OkNested_bne listBase endPtr bs srcOff
  have hbneF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hbne
  let Mid (p : Word × Word) : Assertion :=
    (((.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
        bytesRegion listBase bs) **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝) **
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr))
  have hbneMid :
      cpsTripleWithin 1 LinkWalkNext1 AfterWalkNext1Bne teerLinkedEarly
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNext1Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff)
        (fun h => ∃ p : Word × Word, Mid p h) := by
    refine cpsTripleWithin_weaken (fun h hp => by
      simp only [teerWalkNext1Common] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hFr⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨(next, len), h1, h2, hd, hu, hOk, hFr⟩) hbneF
  have hseq2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hseq1 hbneMid
  let Fin (p : Word × Word) : Assertion :=
    (.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
      (.x24 ↦ᵣ p.1) ** (.x25 ↦ᵣ endPtr) **
      (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
      bytesRegion listBase bs **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝
  have hsave (p : Word × Word) :
      cpsTripleWithin 1 AfterWalkNext1Bne AfterWalkNext1Save teerLinkedEarly
        (Mid p) (Fin p) := by
    dsimp only [Mid, Fin]
    have h0 := teerWalkNext1SaveS8_framed listBase p.1 p.2 cursor bs
    have h0F := cpsTripleWithin_frameR
      ((.x25 ↦ᵣ endPtr) **
        ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝)
      (by pcf) h0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have hsaveE (p : Word × Word) :
      cpsTripleWithin 1 AfterWalkNext1Bne AfterWalkNext1Save teerLinkedEarly
        (Mid p) (fun h => ∃ q : Word × Word, Fin q h) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => ⟨p, hq⟩) (hsave p)
  have hseq3 := cpsTripleWithin_seq_exists_same_cr hseq2 hsaveE
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    obtain ⟨⟨next, len⟩, hq'⟩ := hq
    exact ⟨next, len, by dsimp only [Fin] at hq'; exact hq'⟩)
    (cpsTripleWithin_mono_nSteps
      (by decide : ((2 + (1 + 87) + 1) + 1) ≤ nWalkNext1Cycle) hseq3)

#print axioms teerWalkNext1CycleOk

/-! ## Cycle 2 compose: Prep+Call+BNE+Save -/

/-- BNE framed under concrete ok regs (cycle 2). -/
theorem teerWalkNext2BneOk_framed
    (listBase next len : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 LinkWalkNext2 AfterWalkNext2Bne teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNext2BneOk
  have hF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

theorem teerWalkNext2OkNested_bne
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext2 AfterWalkNext2Bne teerLinkedEarly
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext2) **
        bytesRegion listBase bs) **
        rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff)
      (fun h => ∃ next len : Word,
        (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
          bytesRegion listBase bs) **
          ⌜rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
            endPtr next len⌝) h) := by
  let cursor := listBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext2) **
        bytesRegion listBase bs) **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hCom, hOk⟩ := hp
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
          bytesRegion listBase bs)))
    (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := teerWalkNext2BneOk_framed listBase next len bs
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

theorem teerWalkNext2SaveS8_framed
    (listBase next len v24 : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 AfterWalkNext2Bne AfterWalkNext2Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x24 ↦ᵣ v24) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x24 ↦ᵣ next) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNext2SaveS8 next v24
  have hF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

def teerWalkNext2Common (listBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext2) **
    bytesRegion listBase bs

theorem teerWalkNext2Post_to_commonOutcome
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, teerWalkNextPost LinkWalkNext2 listBase endPtr bs srcOff h →
      (teerWalkNext2Common listBase bs **
        teerWalkNext0Outcome listBase endPtr bs srcOff) h := by
  intro h hp
  simp only [teerWalkNextPost, teerWalkNext2Common, teerWalkNext0Outcome] at hp ⊢
  xperm_hyp hp

private abbrev nWalkNext2Cycle : Nat := 2 + (1 + 87) + 1 + 1

open EvmAsm.Rv64.SAsm (cpsTripleWithin_seq_exists_same_cr)

set_option maxRecDepth 8000 in
/-- Full cycle 1: Prep+Call+BNE ok+Save s8. -/
theorem teerWalkNext2CycleOk
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 v24 v25 a0Old a1Old : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ next len : Word,
      rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
        endPtr next len)
    (hinb : BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hcur : v24 = listBase + BitVec.ofNat 64 srcOff)
    (hend : v25 = endPtr) :
    let cursor := listBase + BitVec.ofNat 64 srcOff
    cpsTripleWithin nWalkNext2Cycle AfterWalkNext1Save AfterWalkNext2Save
      teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (fun h => ∃ next len : Word,
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x24 ↦ᵣ next) ** (.x25 ↦ᵣ endPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
          bytesRegion listBase bs **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h) := by
  intro cursor
  have hprep := teerWalkNext2Prep cursor endPtr a0Old a1Old
  have hprepF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) **
      (.x12 ↦ᵣ a2Old) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) hprep
  have hprep' :
      cpsTripleWithin 2 AfterWalkNext1Save WalkNext2JalPc teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [hcur, hend] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hprepF
  have hcall := teerWalkNext2Call listBase endPtr a2Old t0Old t1Old t2Old t3Old
    t4Old t5Old t6Old bs srcOff old1 hsalign hoff hover hvalid hss hls hll
  have hcallOk :
      cpsTripleWithin (1 + 87) WalkNext2JalPc LinkWalkNext2 teerLinkedEarly
        ((.x1 ↦ᵣ old1) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (teerWalkNext2Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hcall
    have hq' := teerWalkNext2Post_to_commonOutcome listBase endPtr bs srcOff h hq
    obtain ⟨hC, hO, hd, hu, hcom, hout⟩ := hq'
    exact ⟨hC, hO, hd, hu, hcom,
      teerWalkNext0Outcome_drop_fail_of_decode listBase endPtr bs srcOff
        hdec hinb hO hout⟩
  have hcallF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hcallOk
  have hcallF' :
      cpsTripleWithin (1 + 87) WalkNext2JalPc LinkWalkNext2 teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNext2Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hcallF
  have hseq1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [teerWalkNextPrest] at hp ⊢
    xperm_hyp hp) hprep' hcallF'
  have hbne := teerWalkNext2OkNested_bne listBase endPtr bs srcOff
  have hbneF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hbne
  let Mid (p : Word × Word) : Assertion :=
    (((.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
        bytesRegion listBase bs) **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝) **
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr))
  have hbneMid :
      cpsTripleWithin 1 LinkWalkNext2 AfterWalkNext2Bne teerLinkedEarly
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNext2Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff)
        (fun h => ∃ p : Word × Word, Mid p h) := by
    refine cpsTripleWithin_weaken (fun h hp => by
      simp only [teerWalkNext2Common] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hFr⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨(next, len), h1, h2, hd, hu, hOk, hFr⟩) hbneF
  have hseq2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hseq1 hbneMid
  let Fin (p : Word × Word) : Assertion :=
    (.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
      (.x24 ↦ᵣ p.1) ** (.x25 ↦ᵣ endPtr) **
      (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
      bytesRegion listBase bs **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝
  have hsave (p : Word × Word) :
      cpsTripleWithin 1 AfterWalkNext2Bne AfterWalkNext2Save teerLinkedEarly
        (Mid p) (Fin p) := by
    dsimp only [Mid, Fin]
    have h0 := teerWalkNext2SaveS8_framed listBase p.1 p.2 cursor bs
    have h0F := cpsTripleWithin_frameR
      ((.x25 ↦ᵣ endPtr) **
        ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝)
      (by pcf) h0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have hsaveE (p : Word × Word) :
      cpsTripleWithin 1 AfterWalkNext2Bne AfterWalkNext2Save teerLinkedEarly
        (Mid p) (fun h => ∃ q : Word × Word, Fin q h) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => ⟨p, hq⟩) (hsave p)
  have hseq3 := cpsTripleWithin_seq_exists_same_cr hseq2 hsaveE
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    obtain ⟨⟨next, len⟩, hq'⟩ := hq
    exact ⟨next, len, by dsimp only [Fin] at hq'; exact hq'⟩)
    (cpsTripleWithin_mono_nSteps
      (by decide : ((2 + (1 + 87) + 1) + 1) ≤ nWalkNext2Cycle) hseq3)

#print axioms teerWalkNext2CycleOk

/-! ## Cycle 3 compose: Prep+Call+BNE+Save -/

/-- BNE framed under concrete ok regs (cycle 3). -/
theorem teerWalkNext3BneOk_framed
    (listBase next len : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 LinkWalkNext3 AfterWalkNext3Bne teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNext3BneOk
  have hF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

theorem teerWalkNext3OkNested_bne
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext3 AfterWalkNext3Bne teerLinkedEarly
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext3) **
        bytesRegion listBase bs) **
        rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff)
      (fun h => ∃ next len : Word,
        (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
          bytesRegion listBase bs) **
          ⌜rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
            endPtr next len⌝) h) := by
  let cursor := listBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext3) **
        bytesRegion listBase bs) **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hCom, hOk⟩ := hp
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
          bytesRegion listBase bs)))
    (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := teerWalkNext3BneOk_framed listBase next len bs
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

theorem teerWalkNext3SaveS8_framed
    (listBase next len v24 : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 AfterWalkNext3Bne AfterWalkNext3Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x24 ↦ᵣ v24) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x24 ↦ᵣ next) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNext3SaveS8 next v24
  have hF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

def teerWalkNext3Common (listBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext3) **
    bytesRegion listBase bs

theorem teerWalkNext3Post_to_commonOutcome
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, teerWalkNextPost LinkWalkNext3 listBase endPtr bs srcOff h →
      (teerWalkNext3Common listBase bs **
        teerWalkNext0Outcome listBase endPtr bs srcOff) h := by
  intro h hp
  simp only [teerWalkNextPost, teerWalkNext3Common, teerWalkNext0Outcome] at hp ⊢
  xperm_hyp hp

private abbrev nWalkNext3Cycle : Nat := 2 + (1 + 87) + 1 + 1

open EvmAsm.Rv64.SAsm (cpsTripleWithin_seq_exists_same_cr)

set_option maxRecDepth 8000 in
/-- Full cycle 1: Prep+Call+BNE ok+Save s8. -/
theorem teerWalkNext3CycleOk
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 v24 v25 a0Old a1Old : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ next len : Word,
      rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
        endPtr next len)
    (hinb : BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hcur : v24 = listBase + BitVec.ofNat 64 srcOff)
    (hend : v25 = endPtr) :
    let cursor := listBase + BitVec.ofNat 64 srcOff
    cpsTripleWithin nWalkNext3Cycle AfterWalkNext2Save AfterWalkNext3Save
      teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (fun h => ∃ next len : Word,
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x24 ↦ᵣ next) ** (.x25 ↦ᵣ endPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
          bytesRegion listBase bs **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h) := by
  intro cursor
  have hprep := teerWalkNext3Prep cursor endPtr a0Old a1Old
  have hprepF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) **
      (.x12 ↦ᵣ a2Old) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) hprep
  have hprep' :
      cpsTripleWithin 2 AfterWalkNext2Save WalkNext3JalPc teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [hcur, hend] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hprepF
  have hcall := teerWalkNext3Call listBase endPtr a2Old t0Old t1Old t2Old t3Old
    t4Old t5Old t6Old bs srcOff old1 hsalign hoff hover hvalid hss hls hll
  have hcallOk :
      cpsTripleWithin (1 + 87) WalkNext3JalPc LinkWalkNext3 teerLinkedEarly
        ((.x1 ↦ᵣ old1) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (teerWalkNext3Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hcall
    have hq' := teerWalkNext3Post_to_commonOutcome listBase endPtr bs srcOff h hq
    obtain ⟨hC, hO, hd, hu, hcom, hout⟩ := hq'
    exact ⟨hC, hO, hd, hu, hcom,
      teerWalkNext0Outcome_drop_fail_of_decode listBase endPtr bs srcOff
        hdec hinb hO hout⟩
  have hcallF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hcallOk
  have hcallF' :
      cpsTripleWithin (1 + 87) WalkNext3JalPc LinkWalkNext3 teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNext3Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hcallF
  have hseq1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [teerWalkNextPrest] at hp ⊢
    xperm_hyp hp) hprep' hcallF'
  have hbne := teerWalkNext3OkNested_bne listBase endPtr bs srcOff
  have hbneF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hbne
  let Mid (p : Word × Word) : Assertion :=
    (((.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
        bytesRegion listBase bs) **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝) **
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr))
  have hbneMid :
      cpsTripleWithin 1 LinkWalkNext3 AfterWalkNext3Bne teerLinkedEarly
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNext3Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff)
        (fun h => ∃ p : Word × Word, Mid p h) := by
    refine cpsTripleWithin_weaken (fun h hp => by
      simp only [teerWalkNext3Common] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hFr⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨(next, len), h1, h2, hd, hu, hOk, hFr⟩) hbneF
  have hseq2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hseq1 hbneMid
  let Fin (p : Word × Word) : Assertion :=
    (.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
      (.x24 ↦ᵣ p.1) ** (.x25 ↦ᵣ endPtr) **
      (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
      bytesRegion listBase bs **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝
  have hsave (p : Word × Word) :
      cpsTripleWithin 1 AfterWalkNext3Bne AfterWalkNext3Save teerLinkedEarly
        (Mid p) (Fin p) := by
    dsimp only [Mid, Fin]
    have h0 := teerWalkNext3SaveS8_framed listBase p.1 p.2 cursor bs
    have h0F := cpsTripleWithin_frameR
      ((.x25 ↦ᵣ endPtr) **
        ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝)
      (by pcf) h0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have hsaveE (p : Word × Word) :
      cpsTripleWithin 1 AfterWalkNext3Bne AfterWalkNext3Save teerLinkedEarly
        (Mid p) (fun h => ∃ q : Word × Word, Fin q h) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => ⟨p, hq⟩) (hsave p)
  have hseq3 := cpsTripleWithin_seq_exists_same_cr hseq2 hsaveE
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    obtain ⟨⟨next, len⟩, hq'⟩ := hq
    exact ⟨next, len, by dsimp only [Fin] at hq'; exact hq'⟩)
    (cpsTripleWithin_mono_nSteps
      (by decide : ((2 + (1 + 87) + 1) + 1) ≤ nWalkNext3Cycle) hseq3)

#print axioms teerWalkNext3CycleOk

/-! ## Cycle 4 compose: Prep+Call+BNE+Save -/

/-- BNE framed under concrete ok regs (cycle 4). -/
theorem teerWalkNext4BneOk_framed
    (listBase next len : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 LinkWalkNext4 AfterWalkNext4Bne teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNext4BneOk
  have hF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

theorem teerWalkNext4OkNested_bne
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext4 AfterWalkNext4Bne teerLinkedEarly
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext4) **
        bytesRegion listBase bs) **
        rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff)
      (fun h => ∃ next len : Word,
        (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
          bytesRegion listBase bs) **
          ⌜rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
            endPtr next len⌝) h) := by
  let cursor := listBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext4) **
        bytesRegion listBase bs) **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hCom, hOk⟩ := hp
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
          bytesRegion listBase bs)))
    (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := teerWalkNext4BneOk_framed listBase next len bs
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

theorem teerWalkNext4SaveS8_framed
    (listBase next len v24 : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 AfterWalkNext4Bne AfterWalkNext4Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x24 ↦ᵣ v24) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x24 ↦ᵣ next) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNext4SaveS8 next v24
  have hF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

def teerWalkNext4Common (listBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext4) **
    bytesRegion listBase bs

theorem teerWalkNext4Post_to_commonOutcome
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, teerWalkNextPost LinkWalkNext4 listBase endPtr bs srcOff h →
      (teerWalkNext4Common listBase bs **
        teerWalkNext0Outcome listBase endPtr bs srcOff) h := by
  intro h hp
  simp only [teerWalkNextPost, teerWalkNext4Common, teerWalkNext0Outcome] at hp ⊢
  xperm_hyp hp

private abbrev nWalkNext4Cycle : Nat := 2 + (1 + 87) + 1 + 1

open EvmAsm.Rv64.SAsm (cpsTripleWithin_seq_exists_same_cr)

set_option maxRecDepth 8000 in
/-- Full cycle 1: Prep+Call+BNE ok+Save s8. -/
theorem teerWalkNext4CycleOk
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 v24 v25 a0Old a1Old : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ next len : Word,
      rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
        endPtr next len)
    (hinb : BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hcur : v24 = listBase + BitVec.ofNat 64 srcOff)
    (hend : v25 = endPtr) :
    let cursor := listBase + BitVec.ofNat 64 srcOff
    cpsTripleWithin nWalkNext4Cycle AfterWalkNext3Save AfterWalkNext4Save
      teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (fun h => ∃ next len : Word,
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x24 ↦ᵣ next) ** (.x25 ↦ᵣ endPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
          bytesRegion listBase bs **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h) := by
  intro cursor
  have hprep := teerWalkNext4Prep cursor endPtr a0Old a1Old
  have hprepF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) **
      (.x12 ↦ᵣ a2Old) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) hprep
  have hprep' :
      cpsTripleWithin 2 AfterWalkNext3Save WalkNext4JalPc teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [hcur, hend] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hprepF
  have hcall := teerWalkNext4Call listBase endPtr a2Old t0Old t1Old t2Old t3Old
    t4Old t5Old t6Old bs srcOff old1 hsalign hoff hover hvalid hss hls hll
  have hcallOk :
      cpsTripleWithin (1 + 87) WalkNext4JalPc LinkWalkNext4 teerLinkedEarly
        ((.x1 ↦ᵣ old1) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (teerWalkNext4Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hcall
    have hq' := teerWalkNext4Post_to_commonOutcome listBase endPtr bs srcOff h hq
    obtain ⟨hC, hO, hd, hu, hcom, hout⟩ := hq'
    exact ⟨hC, hO, hd, hu, hcom,
      teerWalkNext0Outcome_drop_fail_of_decode listBase endPtr bs srcOff
        hdec hinb hO hout⟩
  have hcallF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hcallOk
  have hcallF' :
      cpsTripleWithin (1 + 87) WalkNext4JalPc LinkWalkNext4 teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNext4Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hcallF
  have hseq1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [teerWalkNextPrest] at hp ⊢
    xperm_hyp hp) hprep' hcallF'
  have hbne := teerWalkNext4OkNested_bne listBase endPtr bs srcOff
  have hbneF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hbne
  let Mid (p : Word × Word) : Assertion :=
    (((.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
        bytesRegion listBase bs) **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝) **
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr))
  have hbneMid :
      cpsTripleWithin 1 LinkWalkNext4 AfterWalkNext4Bne teerLinkedEarly
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNext4Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff)
        (fun h => ∃ p : Word × Word, Mid p h) := by
    refine cpsTripleWithin_weaken (fun h hp => by
      simp only [teerWalkNext4Common] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hFr⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨(next, len), h1, h2, hd, hu, hOk, hFr⟩) hbneF
  have hseq2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hseq1 hbneMid
  let Fin (p : Word × Word) : Assertion :=
    (.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
      (.x24 ↦ᵣ p.1) ** (.x25 ↦ᵣ endPtr) **
      (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
      bytesRegion listBase bs **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝
  have hsave (p : Word × Word) :
      cpsTripleWithin 1 AfterWalkNext4Bne AfterWalkNext4Save teerLinkedEarly
        (Mid p) (Fin p) := by
    dsimp only [Mid, Fin]
    have h0 := teerWalkNext4SaveS8_framed listBase p.1 p.2 cursor bs
    have h0F := cpsTripleWithin_frameR
      ((.x25 ↦ᵣ endPtr) **
        ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝)
      (by pcf) h0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have hsaveE (p : Word × Word) :
      cpsTripleWithin 1 AfterWalkNext4Bne AfterWalkNext4Save teerLinkedEarly
        (Mid p) (fun h => ∃ q : Word × Word, Fin q h) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => ⟨p, hq⟩) (hsave p)
  have hseq3 := cpsTripleWithin_seq_exists_same_cr hseq2 hsaveE
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    obtain ⟨⟨next, len⟩, hq'⟩ := hq
    exact ⟨next, len, by dsimp only [Fin] at hq'; exact hq'⟩)
    (cpsTripleWithin_mono_nSteps
      (by decide : ((2 + (1 + 87) + 1) + 1) ≤ nWalkNext4Cycle) hseq3)

#print axioms teerWalkNext4CycleOk

/-! ## Cycle 5 compose: Prep+Call+BNE (no SaveS8) -/

theorem teerWalkNext5BneOk_framed
    (listBase next len : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 LinkWalkNext5 AfterWalkNext5Bne teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNext5BneOk
  have hF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext5) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

theorem teerWalkNext5OkNested_bne
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext5 AfterWalkNext5Bne teerLinkedEarly
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion listBase bs) **
        rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff)
      (fun h => ∃ next len : Word,
        (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext5) **
          bytesRegion listBase bs) **
          ⌜rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
            endPtr next len⌝) h) := by
  let cursor := listBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion listBase bs) **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hCom, hOk⟩ := hp
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext5) **
          bytesRegion listBase bs)))
    (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := teerWalkNext5BneOk_framed listBase next len bs
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

def teerWalkNext5Common (listBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
    bytesRegion listBase bs

theorem teerWalkNext5Post_to_commonOutcome
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, teerWalkNextPost LinkWalkNext5 listBase endPtr bs srcOff h →
      (teerWalkNext5Common listBase bs **
        teerWalkNext0Outcome listBase endPtr bs srcOff) h := by
  intro h hp
  simp only [teerWalkNextPost, teerWalkNext5Common, teerWalkNext0Outcome] at hp ⊢
  xperm_hyp hp

private abbrev nWalkNext5Cycle : Nat := 2 + (1 + 87) + 1

set_option maxRecDepth 8000 in
/-- Cycle 5: Prep+Call+BNE ok (no Save). Post ∃ next len; s8 still prior cursor. -/
theorem teerWalkNext5CycleOk
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 v24 v25 a0Old a1Old : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ next len : Word,
      rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
        endPtr next len)
    (hinb : BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hcur : v24 = listBase + BitVec.ofNat 64 srcOff)
    (hend : v25 = endPtr) :
    let cursor := listBase + BitVec.ofNat 64 srcOff
    cpsTripleWithin nWalkNext5Cycle AfterWalkNext4Save AfterWalkNext5Bne
      teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (fun h => ∃ next len : Word,
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext5) **
          bytesRegion listBase bs **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h) := by
  intro cursor
  have hprep := teerWalkNext5Prep cursor endPtr a0Old a1Old
  have hprepF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) **
      (.x12 ↦ᵣ a2Old) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) hprep
  have hprep' :
      cpsTripleWithin 2 AfterWalkNext4Save WalkNext5JalPc teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [hcur, hend] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hprepF
  have hcall := teerWalkNext5Call listBase endPtr a2Old t0Old t1Old t2Old t3Old
    t4Old t5Old t6Old bs srcOff old1 hsalign hoff hover hvalid hss hls hll
  have hcallOk :
      cpsTripleWithin (1 + 87) WalkNext5JalPc LinkWalkNext5 teerLinkedEarly
        ((.x1 ↦ᵣ old1) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (teerWalkNext5Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hcall
    have hq' := teerWalkNext5Post_to_commonOutcome listBase endPtr bs srcOff h hq
    obtain ⟨hC, hO, hd, hu, hcom, hout⟩ := hq'
    exact ⟨hC, hO, hd, hu, hcom,
      teerWalkNext0Outcome_drop_fail_of_decode listBase endPtr bs srcOff
        hdec hinb hO hout⟩
  have hcallF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hcallOk
  have hcallF' :
      cpsTripleWithin (1 + 87) WalkNext5JalPc LinkWalkNext5 teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNext5Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hcallF
  have hseq1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [teerWalkNextPrest] at hp ⊢
    xperm_hyp hp) hprep' hcallF'
  have hbne := teerWalkNext5OkNested_bne listBase endPtr bs srcOff
  have hbneF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hbne
  have hbneMid :
      cpsTripleWithin 1 LinkWalkNext5 AfterWalkNext5Bne teerLinkedEarly
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNext5Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff)
        (fun h => ∃ next len : Word,
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext5) **
            bytesRegion listBase bs **
            ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h) := by
    refine cpsTripleWithin_weaken (fun h hp => by
      simp only [teerWalkNext5Common] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hFr⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      refine ⟨next, len, ?_⟩
      -- nest body**frame then xperm to flat post
      have hnest :
          ((((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext5) **
            bytesRegion listBase bs) **
            ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) **
            ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr))) h :=
        ⟨h1, h2, hd, hu, hOk, hFr⟩
      xperm_hyp hnest) hbneF
  have hseq2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hseq1 hbneMid
  exact cpsTripleWithin_mono_nSteps
    (by decide : ((2 + (1 + 87)) + 1) ≤ nWalkNext5Cycle) hseq2

#print axioms teerWalkNext5CycleOk

end EvmAsm.Codegen.TxEip7702TeerSpec
