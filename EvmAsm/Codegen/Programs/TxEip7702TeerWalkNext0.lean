/-
  Teer: first rlp_walk_next cycle after walk_init save.
  AfterWalkInitSave (E+232): MV a0,s8; MV a1,s9; JAL walk_next; BNE a1≠0; MV s8,a0.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxEip7702TeerSpec
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkInit
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

abbrev WN : Word := BitVec.ofNat 64 GuestAddrs.rlp_walk_next

abbrev WalkNext0JalPc : Word := E + 240
abbrev LinkWalkNext0 : Word := E + 244
abbrev AfterWalkNext0Bne : Word := E + 248
abbrev AfterWalkNext0Save : Word := E + 252

def walkNext0JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 240)

theorem walkNext0JalOff_resolves :
    (WalkNext0JalPc + signExtend21 walkNext0JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [WalkNext0JalPc, WN, walkNext0JalOff, E]; decide

abbrev teerWalkNext0BneOff : BitVec 13 := 2612

private theorem teer_type_walkInit_walkNext_disjoint' :
    ((teerCode.union typeCode).union walkInitCode).Disjoint walkNextCode := by
  apply CodeReq.Disjoint.union_left
  · apply CodeReq.Disjoint.union_left
    · unfold teerCode walkNextCode E
      apply CodeReq.Disjoint.ofProg_ranges
      · rw [teer_length]; decide
      · rw [rlp_walk_next_prog_length]; decide
      · rw [teer_length, rlp_walk_next_prog_length]; decide
    · unfold typeCode walkNextCode
      apply CodeReq.Disjoint.ofProg_ranges
      · rw [type_length']; decide
      · rw [rlp_walk_next_prog_length]; decide
      · rw [type_length', rlp_walk_next_prog_length]; decide
  · unfold walkInitCode walkNextCode
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [rlp_walk_init_prog_length]; decide
    · rw [rlp_walk_next_prog_length]; decide
    · rw [rlp_walk_init_prog_length, rlp_walk_next_prog_length]; decide

/-- Mono walkNextCode into teerLinkedEarly (rightmost union arm). -/
theorem teerEarly_mono_walkNext :
    ∀ a i, walkNextCode a = some i → teerLinkedEarly a = some i := by
  intro a i hi
  unfold teerLinkedEarly
  exact CodeReq.mono_union_right teer_type_walkInit_walkNext_disjoint'
    (fun _ _ h => h) a i hi

/-- Prest for walk_next call (cursor in a0, end in a1). -/
def teerWalkNextPrest (cursor endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (listBase : Word) (bs : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
    (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs

theorem teerWalkNextPrest_pcFree
    (cursor endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (listBase : Word) (bs : List (BitVec 8)) :
    (teerWalkNextPrest cursor endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      listBase bs).pcFree := by
  unfold teerWalkNextPrest; pcf

/-- Leaf-shaped 6-way post under walk_next; ra = LinkWalkNext0. -/
def teerWalkNext0Post (listBase endPtr : Word) (bs : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext0) **
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

/-- `mv a0, s8` at AfterWalkInitSave. -/
theorem teerWalkNext0MvA0S8 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterWalkInitSave (E + 236) teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x24 cursor a0Old AfterWalkInitSave (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkInitSave teerProg 58
        (.MV .x10 .x24) (by simp only [AfterWalkInitSave]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkInitSave + 4 : Word) = E + 236 := by
    simp only [AfterWalkInitSave]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv a1, s9` at E+236. -/
theorem teerWalkNext0MvA1S9 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 236) WalkNext0JalPc teerLinkedEarly
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x25 endPtr a1Old (E + 236) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 236) teerProg 59
        (.MV .x11 .x25) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 236 : Word) + 4) = WalkNext0JalPc := by
    simp only [WalkNext0JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

/-- Prep: MV a0,s8; MV a1,s9 at AfterWalkInitSave → WalkNext0JalPc. -/
theorem teerWalkNext0Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterWalkInitSave WalkNext0JalPc teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerWalkNext0MvA0S8 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerWalkNext0MvA1S9 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- JAL walk_next under teerLinkedEarly (full 87-step leaf, 6-way post). -/
theorem teerWalkNext0Call
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
    cpsTripleWithin (1 + 87) WalkNext0JalPc LinkWalkNext0 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNext0Post listBase endPtr bs srcOff) := by
  have hret : (LinkWalkNext0 &&& ~~~(1 : Word)) = LinkWalkNext0 := by
    simp only [LinkWalkNext0, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkWalkNext0 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNext0 walkNextCode
      ((.x1 ↦ᵣ LinkWalkNext0) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNext0Post listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNext0Post] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNext0 teerLinkedEarly
      ((.x1 ↦ᵣ LinkWalkNext0) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkWalkNext0) **
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
      simp only [teerWalkNext0Post] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNext0JalPc WN old1 walkNext0JalOff 87
    walkNext0JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E WalkNext0JalPc teerProg 60
        (.JAL .x1 walkNext0JalOff) (by simp only [WalkNext0JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (WalkNext0JalPc + 4 : Word) = LinkWalkNext0 from by
    simp only [WalkNext0JalPc, LinkWalkNext0]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNext0Post]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- BNE a1,x0 fail: not-taken when a1=0 → AfterWalkNext0Bne. -/
theorem teerWalkNext0BneOk :
    cpsTripleWithin 1 LinkWalkNext0 AfterWalkNext0Bne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerWalkNext0BneOff
    (0 : Word) (0 : Word) LinkWalkNext0
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkWalkNext0 teerProg 61
        (.BNE .x11 .x0 teerWalkNext0BneOff)
        (by simp only [LinkWalkNext0]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkNext0 + 4 = AfterWalkNext0Bne := by
    simp only [LinkWalkNext0, AfterWalkNext0Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `mv s8, a0` after first walk_next success: x24 ← next. -/
theorem teerWalkNext0SaveS8 (next v24 : Word) :
    cpsTripleWithin 1 AfterWalkNext0Bne AfterWalkNext0Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ v24))
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x24 .x10 next v24 AfterWalkNext0Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNext0Bne teerProg 62
        (.MV .x24 .x10) (by simp only [AfterWalkNext0Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkNext0Bne + 4 : Word) = AfterWalkNext0Save := by
    simp only [AfterWalkNext0Bne, AfterWalkNext0Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-- BNE framed under concrete ok regs (a1=0). -/
theorem teerWalkNext0BneOk_framed
    (listBase next len : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 LinkWalkNext0 AfterWalkNext0Bne teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNext0BneOk
  have hF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

/-- From `rlpWalkNextOk`, float ∃ and BNE ntaken → concrete next/len + pure decode. -/
theorem teerWalkNext0OkNested_bne
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext0 AfterWalkNext0Bne teerLinkedEarly
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext0) **
        bytesRegion listBase bs) **
        rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff)
      (fun h => ∃ next len : Word,
        (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
          bytesRegion listBase bs) **
          ⌜rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
            endPtr next len⌝) h) := by
  let cursor := listBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext0) **
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
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
          bytesRegion listBase bs)))
    (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := teerWalkNext0BneOk_framed listBase next len bs
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

/-- Save s8 after ok BNE, framed under next/len + temps + blob. -/
theorem teerWalkNext0SaveS8_framed
    (listBase next len v24 : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 AfterWalkNext0Bne AfterWalkNext0Save teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x24 ↦ᵣ v24) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x24 ↦ᵣ next) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNext0SaveS8 next v24
  have hF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

#print axioms teerWalkNext0Prep
#print axioms teerWalkNext0Call
#print axioms teerWalkNext0BneOk
#print axioms teerWalkNext0SaveS8
#print axioms teerWalkNext0OkNested_bne

end EvmAsm.Codegen.TxEip7702TeerSpec
