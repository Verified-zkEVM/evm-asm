/-
  Teer auth-list walk_next skip cycles 0–9 after second walk_init.
  Each: MV a0,s5; MV a1,s6; JAL walk_next; BNE a1≠0; MV s5,a0 (except cycle 9: no save).
  jal @ E+464..644 → AfterAuthWalkNext9Bne (E+652).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxEip7702TeerSpec
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkInit2
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNext0
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNextSkip
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.RwSubwindow
import EvmAsm.Rv64.SAsm.MeasureLoop

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


/-! ## Auth walk_next cycle 0 @ jal E+464 -/

abbrev AuthWalkNext0JalPc : Word := E + 464
abbrev LinkAuthWalkNext0 : Word := E + 468
abbrev AfterAuthWalkNext0Bne : Word := E + 472
abbrev AfterAuthWalkNext0Save : Word := E + 476
def authWalkNext0JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 464)
abbrev teerAuthWalkNext0BneOff : BitVec 13 := (2388 : BitVec 13)

theorem authWalkNext0JalOff_resolves :
    (AuthWalkNext0JalPc + signExtend21 authWalkNext0JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthWalkNext0JalPc, WN, authWalkNext0JalOff, E]; decide

theorem teerAuthWalkNext0MvA0S5 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterWalkInit2Save (E + 460) teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x21 cursor a0Old AfterWalkInit2Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkInit2Save teerProg 114
        (.MV .x10 .x21) (by simp only [AfterWalkInit2Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkInit2Save + 4 : Word) = E + 460 := by
    simp only [AfterWalkInit2Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext0MvA1S6 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 460) AuthWalkNext0JalPc teerLinkedEarly
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 460) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 460) teerProg 115
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 460 : Word) + 4) = AuthWalkNext0JalPc := by
    simp only [AuthWalkNext0JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext0Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterWalkInit2Save AuthWalkNext0JalPc teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerAuthWalkNext0MvA0S5 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerAuthWalkNext0MvA1S6 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext0Call
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
    cpsTripleWithin (1 + 87) AuthWalkNext0JalPc LinkAuthWalkNext0 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext0 listBase endPtr bs srcOff) := by
  have hret : (LinkAuthWalkNext0 &&& ~~~(1 : Word)) = LinkAuthWalkNext0 := by
    simp only [LinkAuthWalkNext0, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthWalkNext0 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthWalkNext0 walkNextCode
      ((.x1 ↦ᵣ LinkAuthWalkNext0) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext0 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthWalkNext0 teerLinkedEarly
      ((.x1 ↦ᵣ LinkAuthWalkNext0) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthWalkNext0) **
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
  have hcall := callWithin_spec AuthWalkNext0JalPc WN old1 authWalkNext0JalOff 87
    authWalkNext0JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthWalkNext0JalPc teerProg 116
        (.JAL .x1 authWalkNext0JalOff) (by simp only [AuthWalkNext0JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthWalkNext0JalPc + 4 : Word) = LinkAuthWalkNext0 from by
    simp only [AuthWalkNext0JalPc, LinkAuthWalkNext0]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerAuthWalkNext0BneOk :
    cpsTripleWithin 1 LinkAuthWalkNext0 AfterAuthWalkNext0Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthWalkNext0BneOff
    (0 : Word) (0 : Word) LinkAuthWalkNext0
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthWalkNext0 teerProg 117
        (.BNE .x11 .x0 teerAuthWalkNext0BneOff)
        (by simp only [LinkAuthWalkNext0]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthWalkNext0 + 4 = AfterAuthWalkNext0Bne := by
    simp only [LinkAuthWalkNext0, AfterAuthWalkNext0Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerAuthWalkNext0SaveS5 (next v21 : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext0Bne AfterAuthWalkNext0Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x21 .x10 next v21 AfterAuthWalkNext0Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext0Bne teerProg 118
        (.MV .x21 .x10) (by simp only [AfterAuthWalkNext0Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext0Bne + 4 : Word) = AfterAuthWalkNext0Save := by
    simp only [AfterAuthWalkNext0Bne, AfterAuthWalkNext0Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Auth walk_next cycle 1 @ jal E+484 -/

abbrev AuthWalkNext1JalPc : Word := E + 484
abbrev LinkAuthWalkNext1 : Word := E + 488
abbrev AfterAuthWalkNext1Bne : Word := E + 492
abbrev AfterAuthWalkNext1Save : Word := E + 496
def authWalkNext1JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 484)
abbrev teerAuthWalkNext1BneOff : BitVec 13 := (2368 : BitVec 13)

theorem authWalkNext1JalOff_resolves :
    (AuthWalkNext1JalPc + signExtend21 authWalkNext1JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthWalkNext1JalPc, WN, authWalkNext1JalOff, E]; decide

theorem teerAuthWalkNext1MvA0S5 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext0Save (E + 480) teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x21 cursor a0Old AfterAuthWalkNext0Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext0Save teerProg 119
        (.MV .x10 .x21) (by simp only [AfterAuthWalkNext0Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext0Save + 4 : Word) = E + 480 := by
    simp only [AfterAuthWalkNext0Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext1MvA1S6 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 480) AuthWalkNext1JalPc teerLinkedEarly
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 480) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 480) teerProg 120
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 480 : Word) + 4) = AuthWalkNext1JalPc := by
    simp only [AuthWalkNext1JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext1Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthWalkNext0Save AuthWalkNext1JalPc teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerAuthWalkNext1MvA0S5 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerAuthWalkNext1MvA1S6 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext1Call
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
    cpsTripleWithin (1 + 87) AuthWalkNext1JalPc LinkAuthWalkNext1 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext1 listBase endPtr bs srcOff) := by
  have hret : (LinkAuthWalkNext1 &&& ~~~(1 : Word)) = LinkAuthWalkNext1 := by
    simp only [LinkAuthWalkNext1, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthWalkNext1 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthWalkNext1 walkNextCode
      ((.x1 ↦ᵣ LinkAuthWalkNext1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext1 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthWalkNext1 teerLinkedEarly
      ((.x1 ↦ᵣ LinkAuthWalkNext1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthWalkNext1) **
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
  have hcall := callWithin_spec AuthWalkNext1JalPc WN old1 authWalkNext1JalOff 87
    authWalkNext1JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthWalkNext1JalPc teerProg 121
        (.JAL .x1 authWalkNext1JalOff) (by simp only [AuthWalkNext1JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthWalkNext1JalPc + 4 : Word) = LinkAuthWalkNext1 from by
    simp only [AuthWalkNext1JalPc, LinkAuthWalkNext1]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerAuthWalkNext1BneOk :
    cpsTripleWithin 1 LinkAuthWalkNext1 AfterAuthWalkNext1Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthWalkNext1BneOff
    (0 : Word) (0 : Word) LinkAuthWalkNext1
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthWalkNext1 teerProg 122
        (.BNE .x11 .x0 teerAuthWalkNext1BneOff)
        (by simp only [LinkAuthWalkNext1]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthWalkNext1 + 4 = AfterAuthWalkNext1Bne := by
    simp only [LinkAuthWalkNext1, AfterAuthWalkNext1Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerAuthWalkNext1SaveS5 (next v21 : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext1Bne AfterAuthWalkNext1Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x21 .x10 next v21 AfterAuthWalkNext1Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext1Bne teerProg 123
        (.MV .x21 .x10) (by simp only [AfterAuthWalkNext1Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext1Bne + 4 : Word) = AfterAuthWalkNext1Save := by
    simp only [AfterAuthWalkNext1Bne, AfterAuthWalkNext1Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Auth walk_next cycle 2 @ jal E+504 -/

abbrev AuthWalkNext2JalPc : Word := E + 504
abbrev LinkAuthWalkNext2 : Word := E + 508
abbrev AfterAuthWalkNext2Bne : Word := E + 512
abbrev AfterAuthWalkNext2Save : Word := E + 516
def authWalkNext2JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 504)
abbrev teerAuthWalkNext2BneOff : BitVec 13 := (2348 : BitVec 13)

theorem authWalkNext2JalOff_resolves :
    (AuthWalkNext2JalPc + signExtend21 authWalkNext2JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthWalkNext2JalPc, WN, authWalkNext2JalOff, E]; decide

theorem teerAuthWalkNext2MvA0S5 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext1Save (E + 500) teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x21 cursor a0Old AfterAuthWalkNext1Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext1Save teerProg 124
        (.MV .x10 .x21) (by simp only [AfterAuthWalkNext1Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext1Save + 4 : Word) = E + 500 := by
    simp only [AfterAuthWalkNext1Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext2MvA1S6 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 500) AuthWalkNext2JalPc teerLinkedEarly
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 500) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 500) teerProg 125
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 500 : Word) + 4) = AuthWalkNext2JalPc := by
    simp only [AuthWalkNext2JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext2Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthWalkNext1Save AuthWalkNext2JalPc teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerAuthWalkNext2MvA0S5 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerAuthWalkNext2MvA1S6 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext2Call
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
    cpsTripleWithin (1 + 87) AuthWalkNext2JalPc LinkAuthWalkNext2 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext2 listBase endPtr bs srcOff) := by
  have hret : (LinkAuthWalkNext2 &&& ~~~(1 : Word)) = LinkAuthWalkNext2 := by
    simp only [LinkAuthWalkNext2, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthWalkNext2 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthWalkNext2 walkNextCode
      ((.x1 ↦ᵣ LinkAuthWalkNext2) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext2 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthWalkNext2 teerLinkedEarly
      ((.x1 ↦ᵣ LinkAuthWalkNext2) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthWalkNext2) **
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
  have hcall := callWithin_spec AuthWalkNext2JalPc WN old1 authWalkNext2JalOff 87
    authWalkNext2JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthWalkNext2JalPc teerProg 126
        (.JAL .x1 authWalkNext2JalOff) (by simp only [AuthWalkNext2JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthWalkNext2JalPc + 4 : Word) = LinkAuthWalkNext2 from by
    simp only [AuthWalkNext2JalPc, LinkAuthWalkNext2]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerAuthWalkNext2BneOk :
    cpsTripleWithin 1 LinkAuthWalkNext2 AfterAuthWalkNext2Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthWalkNext2BneOff
    (0 : Word) (0 : Word) LinkAuthWalkNext2
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthWalkNext2 teerProg 127
        (.BNE .x11 .x0 teerAuthWalkNext2BneOff)
        (by simp only [LinkAuthWalkNext2]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthWalkNext2 + 4 = AfterAuthWalkNext2Bne := by
    simp only [LinkAuthWalkNext2, AfterAuthWalkNext2Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerAuthWalkNext2SaveS5 (next v21 : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext2Bne AfterAuthWalkNext2Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x21 .x10 next v21 AfterAuthWalkNext2Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext2Bne teerProg 128
        (.MV .x21 .x10) (by simp only [AfterAuthWalkNext2Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext2Bne + 4 : Word) = AfterAuthWalkNext2Save := by
    simp only [AfterAuthWalkNext2Bne, AfterAuthWalkNext2Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Auth walk_next cycle 3 @ jal E+524 -/

abbrev AuthWalkNext3JalPc : Word := E + 524
abbrev LinkAuthWalkNext3 : Word := E + 528
abbrev AfterAuthWalkNext3Bne : Word := E + 532
abbrev AfterAuthWalkNext3Save : Word := E + 536
def authWalkNext3JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 524)
abbrev teerAuthWalkNext3BneOff : BitVec 13 := (2328 : BitVec 13)

theorem authWalkNext3JalOff_resolves :
    (AuthWalkNext3JalPc + signExtend21 authWalkNext3JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthWalkNext3JalPc, WN, authWalkNext3JalOff, E]; decide

theorem teerAuthWalkNext3MvA0S5 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext2Save (E + 520) teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x21 cursor a0Old AfterAuthWalkNext2Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext2Save teerProg 129
        (.MV .x10 .x21) (by simp only [AfterAuthWalkNext2Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext2Save + 4 : Word) = E + 520 := by
    simp only [AfterAuthWalkNext2Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext3MvA1S6 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 520) AuthWalkNext3JalPc teerLinkedEarly
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 520) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 520) teerProg 130
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 520 : Word) + 4) = AuthWalkNext3JalPc := by
    simp only [AuthWalkNext3JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext3Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthWalkNext2Save AuthWalkNext3JalPc teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerAuthWalkNext3MvA0S5 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerAuthWalkNext3MvA1S6 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext3Call
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
    cpsTripleWithin (1 + 87) AuthWalkNext3JalPc LinkAuthWalkNext3 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext3 listBase endPtr bs srcOff) := by
  have hret : (LinkAuthWalkNext3 &&& ~~~(1 : Word)) = LinkAuthWalkNext3 := by
    simp only [LinkAuthWalkNext3, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthWalkNext3 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthWalkNext3 walkNextCode
      ((.x1 ↦ᵣ LinkAuthWalkNext3) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext3 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthWalkNext3 teerLinkedEarly
      ((.x1 ↦ᵣ LinkAuthWalkNext3) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthWalkNext3) **
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
  have hcall := callWithin_spec AuthWalkNext3JalPc WN old1 authWalkNext3JalOff 87
    authWalkNext3JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthWalkNext3JalPc teerProg 131
        (.JAL .x1 authWalkNext3JalOff) (by simp only [AuthWalkNext3JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthWalkNext3JalPc + 4 : Word) = LinkAuthWalkNext3 from by
    simp only [AuthWalkNext3JalPc, LinkAuthWalkNext3]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerAuthWalkNext3BneOk :
    cpsTripleWithin 1 LinkAuthWalkNext3 AfterAuthWalkNext3Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthWalkNext3BneOff
    (0 : Word) (0 : Word) LinkAuthWalkNext3
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthWalkNext3 teerProg 132
        (.BNE .x11 .x0 teerAuthWalkNext3BneOff)
        (by simp only [LinkAuthWalkNext3]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthWalkNext3 + 4 = AfterAuthWalkNext3Bne := by
    simp only [LinkAuthWalkNext3, AfterAuthWalkNext3Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerAuthWalkNext3SaveS5 (next v21 : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext3Bne AfterAuthWalkNext3Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x21 .x10 next v21 AfterAuthWalkNext3Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext3Bne teerProg 133
        (.MV .x21 .x10) (by simp only [AfterAuthWalkNext3Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext3Bne + 4 : Word) = AfterAuthWalkNext3Save := by
    simp only [AfterAuthWalkNext3Bne, AfterAuthWalkNext3Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Auth walk_next cycle 4 @ jal E+544 -/

abbrev AuthWalkNext4JalPc : Word := E + 544
abbrev LinkAuthWalkNext4 : Word := E + 548
abbrev AfterAuthWalkNext4Bne : Word := E + 552
abbrev AfterAuthWalkNext4Save : Word := E + 556
def authWalkNext4JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 544)
abbrev teerAuthWalkNext4BneOff : BitVec 13 := (2308 : BitVec 13)

theorem authWalkNext4JalOff_resolves :
    (AuthWalkNext4JalPc + signExtend21 authWalkNext4JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthWalkNext4JalPc, WN, authWalkNext4JalOff, E]; decide

theorem teerAuthWalkNext4MvA0S5 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext3Save (E + 540) teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x21 cursor a0Old AfterAuthWalkNext3Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext3Save teerProg 134
        (.MV .x10 .x21) (by simp only [AfterAuthWalkNext3Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext3Save + 4 : Word) = E + 540 := by
    simp only [AfterAuthWalkNext3Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext4MvA1S6 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 540) AuthWalkNext4JalPc teerLinkedEarly
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 540) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 540) teerProg 135
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 540 : Word) + 4) = AuthWalkNext4JalPc := by
    simp only [AuthWalkNext4JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext4Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthWalkNext3Save AuthWalkNext4JalPc teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerAuthWalkNext4MvA0S5 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerAuthWalkNext4MvA1S6 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext4Call
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
    cpsTripleWithin (1 + 87) AuthWalkNext4JalPc LinkAuthWalkNext4 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext4 listBase endPtr bs srcOff) := by
  have hret : (LinkAuthWalkNext4 &&& ~~~(1 : Word)) = LinkAuthWalkNext4 := by
    simp only [LinkAuthWalkNext4, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthWalkNext4 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthWalkNext4 walkNextCode
      ((.x1 ↦ᵣ LinkAuthWalkNext4) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext4 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthWalkNext4 teerLinkedEarly
      ((.x1 ↦ᵣ LinkAuthWalkNext4) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthWalkNext4) **
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
  have hcall := callWithin_spec AuthWalkNext4JalPc WN old1 authWalkNext4JalOff 87
    authWalkNext4JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthWalkNext4JalPc teerProg 136
        (.JAL .x1 authWalkNext4JalOff) (by simp only [AuthWalkNext4JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthWalkNext4JalPc + 4 : Word) = LinkAuthWalkNext4 from by
    simp only [AuthWalkNext4JalPc, LinkAuthWalkNext4]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerAuthWalkNext4BneOk :
    cpsTripleWithin 1 LinkAuthWalkNext4 AfterAuthWalkNext4Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthWalkNext4BneOff
    (0 : Word) (0 : Word) LinkAuthWalkNext4
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthWalkNext4 teerProg 137
        (.BNE .x11 .x0 teerAuthWalkNext4BneOff)
        (by simp only [LinkAuthWalkNext4]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthWalkNext4 + 4 = AfterAuthWalkNext4Bne := by
    simp only [LinkAuthWalkNext4, AfterAuthWalkNext4Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerAuthWalkNext4SaveS5 (next v21 : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext4Bne AfterAuthWalkNext4Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x21 .x10 next v21 AfterAuthWalkNext4Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext4Bne teerProg 138
        (.MV .x21 .x10) (by simp only [AfterAuthWalkNext4Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext4Bne + 4 : Word) = AfterAuthWalkNext4Save := by
    simp only [AfterAuthWalkNext4Bne, AfterAuthWalkNext4Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Auth walk_next cycle 5 @ jal E+564 -/

abbrev AuthWalkNext5JalPc : Word := E + 564
abbrev LinkAuthWalkNext5 : Word := E + 568
abbrev AfterAuthWalkNext5Bne : Word := E + 572
abbrev AfterAuthWalkNext5Save : Word := E + 576
def authWalkNext5JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 564)
abbrev teerAuthWalkNext5BneOff : BitVec 13 := (2288 : BitVec 13)

theorem authWalkNext5JalOff_resolves :
    (AuthWalkNext5JalPc + signExtend21 authWalkNext5JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthWalkNext5JalPc, WN, authWalkNext5JalOff, E]; decide

theorem teerAuthWalkNext5MvA0S5 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext4Save (E + 560) teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x21 cursor a0Old AfterAuthWalkNext4Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext4Save teerProg 139
        (.MV .x10 .x21) (by simp only [AfterAuthWalkNext4Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext4Save + 4 : Word) = E + 560 := by
    simp only [AfterAuthWalkNext4Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext5MvA1S6 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 560) AuthWalkNext5JalPc teerLinkedEarly
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 560) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 560) teerProg 140
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 560 : Word) + 4) = AuthWalkNext5JalPc := by
    simp only [AuthWalkNext5JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext5Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthWalkNext4Save AuthWalkNext5JalPc teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerAuthWalkNext5MvA0S5 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerAuthWalkNext5MvA1S6 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext5Call
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
    cpsTripleWithin (1 + 87) AuthWalkNext5JalPc LinkAuthWalkNext5 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext5 listBase endPtr bs srcOff) := by
  have hret : (LinkAuthWalkNext5 &&& ~~~(1 : Word)) = LinkAuthWalkNext5 := by
    simp only [LinkAuthWalkNext5, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthWalkNext5 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthWalkNext5 walkNextCode
      ((.x1 ↦ᵣ LinkAuthWalkNext5) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext5 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthWalkNext5 teerLinkedEarly
      ((.x1 ↦ᵣ LinkAuthWalkNext5) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthWalkNext5) **
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
  have hcall := callWithin_spec AuthWalkNext5JalPc WN old1 authWalkNext5JalOff 87
    authWalkNext5JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthWalkNext5JalPc teerProg 141
        (.JAL .x1 authWalkNext5JalOff) (by simp only [AuthWalkNext5JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthWalkNext5JalPc + 4 : Word) = LinkAuthWalkNext5 from by
    simp only [AuthWalkNext5JalPc, LinkAuthWalkNext5]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerAuthWalkNext5BneOk :
    cpsTripleWithin 1 LinkAuthWalkNext5 AfterAuthWalkNext5Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthWalkNext5BneOff
    (0 : Word) (0 : Word) LinkAuthWalkNext5
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthWalkNext5 teerProg 142
        (.BNE .x11 .x0 teerAuthWalkNext5BneOff)
        (by simp only [LinkAuthWalkNext5]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthWalkNext5 + 4 = AfterAuthWalkNext5Bne := by
    simp only [LinkAuthWalkNext5, AfterAuthWalkNext5Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerAuthWalkNext5SaveS5 (next v21 : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext5Bne AfterAuthWalkNext5Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x21 .x10 next v21 AfterAuthWalkNext5Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext5Bne teerProg 143
        (.MV .x21 .x10) (by simp only [AfterAuthWalkNext5Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext5Bne + 4 : Word) = AfterAuthWalkNext5Save := by
    simp only [AfterAuthWalkNext5Bne, AfterAuthWalkNext5Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Auth walk_next cycle 6 @ jal E+584 -/

abbrev AuthWalkNext6JalPc : Word := E + 584
abbrev LinkAuthWalkNext6 : Word := E + 588
abbrev AfterAuthWalkNext6Bne : Word := E + 592
abbrev AfterAuthWalkNext6Save : Word := E + 596
def authWalkNext6JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 584)
abbrev teerAuthWalkNext6BneOff : BitVec 13 := (2268 : BitVec 13)

theorem authWalkNext6JalOff_resolves :
    (AuthWalkNext6JalPc + signExtend21 authWalkNext6JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthWalkNext6JalPc, WN, authWalkNext6JalOff, E]; decide

theorem teerAuthWalkNext6MvA0S5 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext5Save (E + 580) teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x21 cursor a0Old AfterAuthWalkNext5Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext5Save teerProg 144
        (.MV .x10 .x21) (by simp only [AfterAuthWalkNext5Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext5Save + 4 : Word) = E + 580 := by
    simp only [AfterAuthWalkNext5Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext6MvA1S6 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 580) AuthWalkNext6JalPc teerLinkedEarly
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 580) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 580) teerProg 145
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 580 : Word) + 4) = AuthWalkNext6JalPc := by
    simp only [AuthWalkNext6JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext6Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthWalkNext5Save AuthWalkNext6JalPc teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerAuthWalkNext6MvA0S5 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerAuthWalkNext6MvA1S6 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext6Call
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
    cpsTripleWithin (1 + 87) AuthWalkNext6JalPc LinkAuthWalkNext6 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext6 listBase endPtr bs srcOff) := by
  have hret : (LinkAuthWalkNext6 &&& ~~~(1 : Word)) = LinkAuthWalkNext6 := by
    simp only [LinkAuthWalkNext6, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthWalkNext6 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthWalkNext6 walkNextCode
      ((.x1 ↦ᵣ LinkAuthWalkNext6) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext6 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthWalkNext6 teerLinkedEarly
      ((.x1 ↦ᵣ LinkAuthWalkNext6) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthWalkNext6) **
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
  have hcall := callWithin_spec AuthWalkNext6JalPc WN old1 authWalkNext6JalOff 87
    authWalkNext6JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthWalkNext6JalPc teerProg 146
        (.JAL .x1 authWalkNext6JalOff) (by simp only [AuthWalkNext6JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthWalkNext6JalPc + 4 : Word) = LinkAuthWalkNext6 from by
    simp only [AuthWalkNext6JalPc, LinkAuthWalkNext6]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerAuthWalkNext6BneOk :
    cpsTripleWithin 1 LinkAuthWalkNext6 AfterAuthWalkNext6Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthWalkNext6BneOff
    (0 : Word) (0 : Word) LinkAuthWalkNext6
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthWalkNext6 teerProg 147
        (.BNE .x11 .x0 teerAuthWalkNext6BneOff)
        (by simp only [LinkAuthWalkNext6]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthWalkNext6 + 4 = AfterAuthWalkNext6Bne := by
    simp only [LinkAuthWalkNext6, AfterAuthWalkNext6Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerAuthWalkNext6SaveS5 (next v21 : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext6Bne AfterAuthWalkNext6Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x21 .x10 next v21 AfterAuthWalkNext6Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext6Bne teerProg 148
        (.MV .x21 .x10) (by simp only [AfterAuthWalkNext6Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext6Bne + 4 : Word) = AfterAuthWalkNext6Save := by
    simp only [AfterAuthWalkNext6Bne, AfterAuthWalkNext6Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Auth walk_next cycle 7 @ jal E+604 -/

abbrev AuthWalkNext7JalPc : Word := E + 604
abbrev LinkAuthWalkNext7 : Word := E + 608
abbrev AfterAuthWalkNext7Bne : Word := E + 612
abbrev AfterAuthWalkNext7Save : Word := E + 616
def authWalkNext7JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 604)
abbrev teerAuthWalkNext7BneOff : BitVec 13 := (2248 : BitVec 13)

theorem authWalkNext7JalOff_resolves :
    (AuthWalkNext7JalPc + signExtend21 authWalkNext7JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthWalkNext7JalPc, WN, authWalkNext7JalOff, E]; decide

theorem teerAuthWalkNext7MvA0S5 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext6Save (E + 600) teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x21 cursor a0Old AfterAuthWalkNext6Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext6Save teerProg 149
        (.MV .x10 .x21) (by simp only [AfterAuthWalkNext6Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext6Save + 4 : Word) = E + 600 := by
    simp only [AfterAuthWalkNext6Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext7MvA1S6 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 600) AuthWalkNext7JalPc teerLinkedEarly
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 600) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 600) teerProg 150
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 600 : Word) + 4) = AuthWalkNext7JalPc := by
    simp only [AuthWalkNext7JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext7Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthWalkNext6Save AuthWalkNext7JalPc teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerAuthWalkNext7MvA0S5 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerAuthWalkNext7MvA1S6 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext7Call
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
    cpsTripleWithin (1 + 87) AuthWalkNext7JalPc LinkAuthWalkNext7 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext7 listBase endPtr bs srcOff) := by
  have hret : (LinkAuthWalkNext7 &&& ~~~(1 : Word)) = LinkAuthWalkNext7 := by
    simp only [LinkAuthWalkNext7, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthWalkNext7 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthWalkNext7 walkNextCode
      ((.x1 ↦ᵣ LinkAuthWalkNext7) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext7 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthWalkNext7 teerLinkedEarly
      ((.x1 ↦ᵣ LinkAuthWalkNext7) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthWalkNext7) **
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
  have hcall := callWithin_spec AuthWalkNext7JalPc WN old1 authWalkNext7JalOff 87
    authWalkNext7JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthWalkNext7JalPc teerProg 151
        (.JAL .x1 authWalkNext7JalOff) (by simp only [AuthWalkNext7JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthWalkNext7JalPc + 4 : Word) = LinkAuthWalkNext7 from by
    simp only [AuthWalkNext7JalPc, LinkAuthWalkNext7]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerAuthWalkNext7BneOk :
    cpsTripleWithin 1 LinkAuthWalkNext7 AfterAuthWalkNext7Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthWalkNext7BneOff
    (0 : Word) (0 : Word) LinkAuthWalkNext7
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthWalkNext7 teerProg 152
        (.BNE .x11 .x0 teerAuthWalkNext7BneOff)
        (by simp only [LinkAuthWalkNext7]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthWalkNext7 + 4 = AfterAuthWalkNext7Bne := by
    simp only [LinkAuthWalkNext7, AfterAuthWalkNext7Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerAuthWalkNext7SaveS5 (next v21 : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext7Bne AfterAuthWalkNext7Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x21 .x10 next v21 AfterAuthWalkNext7Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext7Bne teerProg 153
        (.MV .x21 .x10) (by simp only [AfterAuthWalkNext7Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext7Bne + 4 : Word) = AfterAuthWalkNext7Save := by
    simp only [AfterAuthWalkNext7Bne, AfterAuthWalkNext7Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Auth walk_next cycle 8 @ jal E+624 -/

abbrev AuthWalkNext8JalPc : Word := E + 624
abbrev LinkAuthWalkNext8 : Word := E + 628
abbrev AfterAuthWalkNext8Bne : Word := E + 632
abbrev AfterAuthWalkNext8Save : Word := E + 636
def authWalkNext8JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 624)
abbrev teerAuthWalkNext8BneOff : BitVec 13 := (2228 : BitVec 13)

theorem authWalkNext8JalOff_resolves :
    (AuthWalkNext8JalPc + signExtend21 authWalkNext8JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthWalkNext8JalPc, WN, authWalkNext8JalOff, E]; decide

theorem teerAuthWalkNext8MvA0S5 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext7Save (E + 620) teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x21 cursor a0Old AfterAuthWalkNext7Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext7Save teerProg 154
        (.MV .x10 .x21) (by simp only [AfterAuthWalkNext7Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext7Save + 4 : Word) = E + 620 := by
    simp only [AfterAuthWalkNext7Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext8MvA1S6 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 620) AuthWalkNext8JalPc teerLinkedEarly
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 620) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 620) teerProg 155
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 620 : Word) + 4) = AuthWalkNext8JalPc := by
    simp only [AuthWalkNext8JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext8Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthWalkNext7Save AuthWalkNext8JalPc teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerAuthWalkNext8MvA0S5 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerAuthWalkNext8MvA1S6 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext8Call
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
    cpsTripleWithin (1 + 87) AuthWalkNext8JalPc LinkAuthWalkNext8 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext8 listBase endPtr bs srcOff) := by
  have hret : (LinkAuthWalkNext8 &&& ~~~(1 : Word)) = LinkAuthWalkNext8 := by
    simp only [LinkAuthWalkNext8, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthWalkNext8 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthWalkNext8 walkNextCode
      ((.x1 ↦ᵣ LinkAuthWalkNext8) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext8 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthWalkNext8 teerLinkedEarly
      ((.x1 ↦ᵣ LinkAuthWalkNext8) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthWalkNext8) **
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
  have hcall := callWithin_spec AuthWalkNext8JalPc WN old1 authWalkNext8JalOff 87
    authWalkNext8JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthWalkNext8JalPc teerProg 156
        (.JAL .x1 authWalkNext8JalOff) (by simp only [AuthWalkNext8JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthWalkNext8JalPc + 4 : Word) = LinkAuthWalkNext8 from by
    simp only [AuthWalkNext8JalPc, LinkAuthWalkNext8]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerAuthWalkNext8BneOk :
    cpsTripleWithin 1 LinkAuthWalkNext8 AfterAuthWalkNext8Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthWalkNext8BneOff
    (0 : Word) (0 : Word) LinkAuthWalkNext8
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthWalkNext8 teerProg 157
        (.BNE .x11 .x0 teerAuthWalkNext8BneOff)
        (by simp only [LinkAuthWalkNext8]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthWalkNext8 + 4 = AfterAuthWalkNext8Bne := by
    simp only [LinkAuthWalkNext8, AfterAuthWalkNext8Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerAuthWalkNext8SaveS5 (next v21 : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext8Bne AfterAuthWalkNext8Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x21 .x10 next v21 AfterAuthWalkNext8Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext8Bne teerProg 158
        (.MV .x21 .x10) (by simp only [AfterAuthWalkNext8Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext8Bne + 4 : Word) = AfterAuthWalkNext8Save := by
    simp only [AfterAuthWalkNext8Bne, AfterAuthWalkNext8Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-! ## Auth walk_next cycle 9 @ jal E+644 -/

abbrev AuthWalkNext9JalPc : Word := E + 644
abbrev LinkAuthWalkNext9 : Word := E + 648
abbrev AfterAuthWalkNext9Bne : Word := E + 652
def authWalkNext9JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 644)
abbrev teerAuthWalkNext9BneOff : BitVec 13 := (2208 : BitVec 13)

theorem authWalkNext9JalOff_resolves :
    (AuthWalkNext9JalPc + signExtend21 authWalkNext9JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthWalkNext9JalPc, WN, authWalkNext9JalOff, E]; decide

theorem teerAuthWalkNext9MvA0S5 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext8Save (E + 640) teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x21 cursor a0Old AfterAuthWalkNext8Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext8Save teerProg 159
        (.MV .x10 .x21) (by simp only [AfterAuthWalkNext8Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext8Save + 4 : Word) = E + 640 := by
    simp only [AfterAuthWalkNext8Save]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext9MvA1S6 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 640) AuthWalkNext9JalPc teerLinkedEarly
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 640) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 640) teerProg 160
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 640 : Word) + 4) = AuthWalkNext9JalPc := by
    simp only [AuthWalkNext9JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthWalkNext9Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthWalkNext8Save AuthWalkNext9JalPc teerLinkedEarly
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerAuthWalkNext9MvA0S5 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerAuthWalkNext9MvA1S6 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext9Call
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
    cpsTripleWithin (1 + 87) AuthWalkNext9JalPc LinkAuthWalkNext9 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext9 listBase endPtr bs srcOff) := by
  have hret : (LinkAuthWalkNext9 &&& ~~~(1 : Word)) = LinkAuthWalkNext9 := by
    simp only [LinkAuthWalkNext9, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthWalkNext9 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthWalkNext9 walkNextCode
      ((.x1 ↦ᵣ LinkAuthWalkNext9) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthWalkNext9 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthWalkNext9 teerLinkedEarly
      ((.x1 ↦ᵣ LinkAuthWalkNext9) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthWalkNext9) **
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
  have hcall := callWithin_spec AuthWalkNext9JalPc WN old1 authWalkNext9JalOff 87
    authWalkNext9JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthWalkNext9JalPc teerProg 161
        (.JAL .x1 authWalkNext9JalOff) (by simp only [AuthWalkNext9JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthWalkNext9JalPc + 4 : Word) = LinkAuthWalkNext9 from by
    simp only [AuthWalkNext9JalPc, LinkAuthWalkNext9]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerAuthWalkNext9BneOk :
    cpsTripleWithin 1 LinkAuthWalkNext9 AfterAuthWalkNext9Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthWalkNext9BneOff
    (0 : Word) (0 : Word) LinkAuthWalkNext9
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthWalkNext9 teerProg 162
        (.BNE .x11 .x0 teerAuthWalkNext9BneOff)
        (by simp only [LinkAuthWalkNext9]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthWalkNext9 + 4 = AfterAuthWalkNext9Bne := by
    simp only [LinkAuthWalkNext9, AfterAuthWalkNext9Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

#print axioms teerAuthWalkNext0Prep
#print axioms teerAuthWalkNext0Call
#print axioms teerAuthWalkNext0BneOk
#print axioms teerAuthWalkNext0SaveS5
#print axioms teerAuthWalkNext9Prep
#print axioms teerAuthWalkNext9Call
#print axioms teerAuthWalkNext9BneOk

/-! ## Auth cycle 0 CycleOk (Prep+Call+BNE+Save s5) -/

def teerAuthWalkNext0Common (listBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
    bytesRegion listBase bs

theorem teerAuthWalkNext0Post_to_commonOutcome
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, teerWalkNextPost LinkAuthWalkNext0 listBase endPtr bs srcOff h →
      (teerAuthWalkNext0Common listBase bs **
        teerWalkNext0Outcome listBase endPtr bs srcOff) h := by
  intro h hp
  simp only [teerWalkNextPost, teerAuthWalkNext0Common] at hp ⊢
  xperm_hyp hp

theorem teerAuthWalkNext0BneOk_framed
    (listBase next len : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 LinkAuthWalkNext0 AfterAuthWalkNext0Bne teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
        bytesRegion listBase bs) := by
  have h0 := teerAuthWalkNext0BneOk
  have hF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

theorem teerAuthWalkNext0OkNested_bne
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkAuthWalkNext0 AfterAuthWalkNext0Bne teerLinkedEarly
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
        bytesRegion listBase bs) **
        rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff)
      (fun h => ∃ next len : Word,
        (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
          bytesRegion listBase bs) **
          ⌜rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
            endPtr next len⌝) h) := by
  let cursor := listBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
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
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
          bytesRegion listBase bs)))
    (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := teerAuthWalkNext0BneOk_framed listBase next len bs
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

theorem teerAuthWalkNext0SaveS5_framed
    (listBase next len v21 : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 AfterAuthWalkNext0Bne AfterAuthWalkNext0Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x21 ↦ᵣ v21) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x21 ↦ᵣ next) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
        bytesRegion listBase bs) := by
  have h0 := teerAuthWalkNext0SaveS5 next v21
  have hF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

private abbrev nAuthWalkNext0Cycle : Nat := 2 + (1 + 87) + 1 + 1

open EvmAsm.Rv64.SAsm (cpsTripleWithin_seq_exists_same_cr sepConj_exists_left)

set_option maxRecDepth 8000 in
/-- Full auth cycle 0: Prep+Call+BNE ok+Save s5. Post ∃ next len (s5←next). -/
theorem teerAuthWalkNext0CycleOk
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 v21 v22 a0Old a1Old : Word)
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
    (hcur : v21 = listBase + BitVec.ofNat 64 srcOff)
    (hend : v22 = endPtr) :
    let cursor := listBase + BitVec.ofNat 64 srcOff
    cpsTripleWithin nAuthWalkNext0Cycle AfterWalkInit2Save AfterAuthWalkNext0Save
      teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (fun h => ∃ next len : Word,
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x21 ↦ᵣ next) ** (.x22 ↦ᵣ endPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
          bytesRegion listBase bs **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h) := by
  intro cursor
  have hprep := teerAuthWalkNext0Prep cursor endPtr a0Old a1Old
  have hprepF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) **
      (.x12 ↦ᵣ a2Old) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) hprep
  have hprep' :
      cpsTripleWithin 2 AfterWalkInit2Save AuthWalkNext0JalPc teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
        ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [hcur, hend] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hprepF
  have hcall := teerAuthWalkNext0Call listBase endPtr a2Old t0Old t1Old t2Old t3Old
    t4Old t5Old t6Old bs srcOff old1 hsalign hoff hover hvalid hss hls hll
  have hcallOk :
      cpsTripleWithin (1 + 87) AuthWalkNext0JalPc LinkAuthWalkNext0 teerLinkedEarly
        ((.x1 ↦ᵣ old1) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (teerAuthWalkNext0Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hcall
    have hq' := teerAuthWalkNext0Post_to_commonOutcome listBase endPtr bs srcOff h hq
    obtain ⟨hC, hO, hd, hu, hcom, hout⟩ := hq'
    exact ⟨hC, hO, hd, hu, hcom,
      teerWalkNext0Outcome_drop_fail_of_decode listBase endPtr bs srcOff
        hdec hinb hO hout⟩
  have hcallF := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) (by pcf) hcallOk
  have hcallF' :
      cpsTripleWithin (1 + 87) AuthWalkNext0JalPc LinkAuthWalkNext0 teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) **
          teerAuthWalkNext0Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hcallF
  have hseq1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [teerWalkNextPrest] at hp ⊢
    xperm_hyp hp) hprep' hcallF'
  have hbne := teerAuthWalkNext0OkNested_bne listBase endPtr bs srcOff
  have hbneF := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) (by pcf) hbne
  let Mid (p : Word × Word) : Assertion :=
    (((.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
        bytesRegion listBase bs) **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝) **
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr))
  have hbneMid :
      cpsTripleWithin 1 LinkAuthWalkNext0 AfterAuthWalkNext0Bne teerLinkedEarly
        (((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) **
          teerAuthWalkNext0Common listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff)
        (fun h => ∃ p : Word × Word, Mid p h) := by
    refine cpsTripleWithin_weaken (fun h hp => by
      simp only [teerAuthWalkNext0Common] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hFr⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨(next, len), h1, h2, hd, hu, hOk, hFr⟩) hbneF
  have hseq2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hseq1 hbneMid
  let Fin (p : Word × Word) : Assertion :=
    (.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
      (.x21 ↦ᵣ p.1) ** (.x22 ↦ᵣ endPtr) **
      (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkAuthWalkNext0) **
      bytesRegion listBase bs **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝
  have hsave (p : Word × Word) :
      cpsTripleWithin 1 AfterAuthWalkNext0Bne AfterAuthWalkNext0Save teerLinkedEarly
        (Mid p) (Fin p) := by
    dsimp only [Mid, Fin]
    have h0 := teerAuthWalkNext0SaveS5_framed listBase p.1 p.2 cursor bs
    have h0F := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ endPtr) **
        ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝)
      (by pcf) h0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have hsaveE (p : Word × Word) :
      cpsTripleWithin 1 AfterAuthWalkNext0Bne AfterAuthWalkNext0Save teerLinkedEarly
        (Mid p) (fun h => ∃ q : Word × Word, Fin q h) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => ⟨p, hq⟩) (hsave p)
  have hseq3 := cpsTripleWithin_seq_exists_same_cr hseq2 hsaveE
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    obtain ⟨⟨next, len⟩, hq'⟩ := hq
    exact ⟨next, len, by dsimp only [Fin] at hq'; exact hq'⟩)
    (cpsTripleWithin_mono_nSteps
      (by decide : ((2 + (1 + 87) + 1) + 1) ≤ nAuthWalkNext0Cycle) hseq3)

#print axioms teerAuthWalkNext0CycleOk

end EvmAsm.Codegen.TxEip7702TeerSpec
