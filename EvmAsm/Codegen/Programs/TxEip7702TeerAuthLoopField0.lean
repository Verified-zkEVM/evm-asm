/-
  Teer auth-loop field0: reload cursors from 112/120(sp), walk_next@788,
  SD cursor, SUB content, content_to_u64@808, BNE ok.
  AfterAuthItemWiSave (E+780) → AfterAuthField0Bne (E+816).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopInner
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNext0
import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmCode
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.AsmReloc
import EvmAsm.EL.RLP.Scalar

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpListCountItemsSAsm
open EvmAsm.EL.RLP (Nat.fromBytesBE)

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _)

/-! ## CodeReq: content_to_u64 into teer linked -/

abbrev C64 : Word := (GuestAddrs.rlp_content_to_u64 : Word)
def contentToU64Code : CodeReq := rlp_content_to_u64_code C64

def teerLinkedField0 : CodeReq := teerLinkedCount.union contentToU64Code

private theorem teer_field0_disjoint :
    teerLinkedCount.Disjoint contentToU64Code := by
  unfold teerLinkedCount teerLinkedEarly listCountCode contentToU64Code
    teerCode typeCode walkInitCode walkNextCode LC C64
  apply CodeReq.Disjoint.union_left
  · apply CodeReq.Disjoint.union_left
    · apply CodeReq.Disjoint.union_left
      · apply CodeReq.Disjoint.union_left
        · apply CodeReq.Disjoint.ofProg_ranges
          · rw [teer_length]; decide
          · rw [rlp_content_to_u64_prog_length]; decide
          · rw [teer_length, rlp_content_to_u64_prog_length]; decide
        · apply CodeReq.Disjoint.ofProg_ranges
          · rw [type_length']; decide
          · rw [rlp_content_to_u64_prog_length]; decide
          · rw [type_length', rlp_content_to_u64_prog_length]; decide
      · apply CodeReq.Disjoint.ofProg_ranges
        · rw [rlp_walk_init_prog_length]; decide
        · rw [rlp_content_to_u64_prog_length]; decide
        · rw [rlp_walk_init_prog_length, rlp_content_to_u64_prog_length]; decide
    · apply CodeReq.Disjoint.ofProg_ranges
      · rw [rlp_walk_next_prog_length]; decide
      · rw [rlp_content_to_u64_prog_length]; decide
      · rw [rlp_walk_next_prog_length, rlp_content_to_u64_prog_length]; decide
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [total_length]; decide
    · rw [rlp_content_to_u64_prog_length]; decide
    · rw [total_length, rlp_content_to_u64_prog_length]; decide

theorem teerField0_mono_count :
    ∀ a i, teerLinkedCount a = some i → teerLinkedField0 a = some i := by
  intro a i hi
  exact CodeReq.union_mono_left (cr1 := teerLinkedCount) (cr2 := contentToU64Code) a i hi

theorem teerField0_mono_content :
    ∀ a i, contentToU64Code a = some i → teerLinkedField0 a = some i :=
  CodeReq.mono_union_right teer_field0_disjoint (fun _ _ h => h)

theorem teerField0_mono_teer :
    ∀ a i, teerCode a = some i → teerLinkedField0 a = some i :=
  fun a i hi => teerField0_mono_count a i (teerCount_mono_teer a i hi)

theorem teerField0_mono_walkNext :
    ∀ a i, walkNextCode a = some i → teerLinkedField0 a = some i :=
  fun a i hi => teerField0_mono_count a i (teerCount_mono_walkNext a i hi)

/-! ## PCs -/

abbrev AuthField0WnJalPc : Word := E + 788
abbrev LinkAuthField0Wn : Word := E + 792
abbrev AfterAuthField0WnBne : Word := E + 796
abbrev AfterAuthField0WnSd : Word := E + 800
abbrev AfterAuthField0Sub : Word := E + 804
abbrev AtContentToU64 : Word := E + 808
abbrev LinkContentToU64 : Word := E + 812
abbrev AfterAuthField0Bne : Word := E + 816

def authField0WnJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 788)

abbrev teerAuthField0WnBneOff : BitVec 13 := (2056 : BitVec 13)

def contentToU64JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_content_to_u64
    (GuestAddrs.tx_eip7702_existing_authority_refund + 808)

abbrev teerContentToU64BneOff : BitVec 13 := (2036 : BitVec 13)

theorem authField0WnJalOff_resolves :
    (AuthField0WnJalPc + signExtend21 authField0WnJalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthField0WnJalPc, WN, authField0WnJalOff, E]; decide

theorem contentToU64JalOff_resolves :
    AtContentToU64 + signExtend21 contentToU64JalOff = C64 := by
  simp only [AtContentToU64, C64, contentToU64JalOff, E]; decide

private theorem se12_112_f0 :
    signExtend12 (112 : BitVec 12) = (112 : Word) := by decide

private theorem se12_120_f0 :
    signExtend12 (120 : BitVec 12) = (120 : Word) := by decide

/-- `ld a0, 112(sp)` reload cursor. -/
theorem teerAuthField0LdA0 (spC cur a0Old : Word) :
    cpsTripleWithin 1 AfterAuthItemWiSave (E + 784) teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ a0Old) ** ((spC + (112 : Word)) ↦ₘ cur))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** ((spC + (112 : Word)) ↦ₘ cur)) := by
  have h0 := ld_spec_gen_within .x10 .x2 spC a0Old cur
    (112 : BitVec 12) AfterAuthItemWiSave (by decide)
  rw [show spC + signExtend12 (112 : BitVec 12) = spC + (112 : Word) from by
    rw [se12_112_f0]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthItemWiSave teerProg 195
        (.LD .x10 .x2 (112 : BitVec 12))
        (by simp only [AfterAuthItemWiSave]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthItemWiSave + 4 : Word) = E + 784 := by
    simp only [AfterAuthItemWiSave]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `ld a1, 120(sp)` reload end. -/
theorem teerAuthField0LdA1 (spC endW a1Old : Word) :
    cpsTripleWithin 1 (E + 784) AuthField0WnJalPc teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ a1Old) ** ((spC + (120 : Word)) ↦ₘ endW))
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ endW) ** ((spC + (120 : Word)) ↦ₘ endW)) := by
  have h0 := ld_spec_gen_within .x11 .x2 spC a1Old endW
    (120 : BitVec 12) (E + 784) (by decide)
  rw [show spC + signExtend12 (120 : BitVec 12) = spC + (120 : Word) from by
    rw [se12_120_f0]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 784) teerProg 196
        (.LD .x11 .x2 (120 : BitVec 12)) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 784 : Word) + 4 = AuthField0WnJalPc := by
    simp only [AuthField0WnJalPc]; bv_omega
  rw [hpc] at e0
  exact e0

/-- Reload a0/a1 from scratch: AfterAuthItemWiSave → AuthField0WnJalPc. -/
theorem teerAuthField0Prep (spC cur endW a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthItemWiSave AuthField0WnJalPc teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        ((spC + (112 : Word)) ↦ₘ cur) ** ((spC + (120 : Word)) ↦ₘ endW))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        ((spC + (112 : Word)) ↦ₘ cur) ** ((spC + (120 : Word)) ↦ₘ endW)) := by
  have h0 := teerAuthField0LdA0 spC cur a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ a1Old) ** ((spC + (120 : Word)) ↦ₘ endW)) (by pcf) h0
  have h1 := teerAuthField0LdA1 spC endW a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ cur) ** ((spC + (112 : Word)) ↦ₘ cur)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- JAL walk_next field0 under teerLinkedField0. -/
theorem teerAuthField0WnCall
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
    cpsTripleWithin (1 + 87) AuthField0WnJalPc LinkAuthField0Wn teerLinkedField0
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthField0Wn listBase endPtr bs srcOff) := by
  have hret : (LinkAuthField0Wn &&& ~~~(1 : Word)) = LinkAuthField0Wn := by
    simp only [LinkAuthField0Wn, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthField0Wn a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthField0Wn walkNextCode
      ((.x1 ↦ᵣ LinkAuthField0Wn) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthField0Wn listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerField0_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthField0Wn teerLinkedField0
      ((.x1 ↦ᵣ LinkAuthField0Wn) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthField0Wn) **
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
  have hcall := callWithin_spec AuthField0WnJalPc WN old1 authField0WnJalOff 87
    authField0WnJalOff_resolves
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthField0WnJalPc teerProg 197
        (.JAL .x1 authField0WnJalOff) (by simp only [AuthField0WnJalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthField0WnJalPc + 4 : Word) = LinkAuthField0Wn from by
    simp only [AuthField0WnJalPc, LinkAuthField0Wn]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- BNE a1,x0 ok (status 0) → AfterAuthField0WnBne. -/
theorem teerAuthField0WnBneOk :
    cpsTripleWithin 1 LinkAuthField0Wn AfterAuthField0WnBne teerLinkedField0
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthField0WnBneOff
    (0 : Word) (0 : Word) LinkAuthField0Wn
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthField0Wn teerProg 198
        (.BNE .x11 .x0 teerAuthField0WnBneOff)
        (by simp only [LinkAuthField0Wn]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthField0Wn + 4 = AfterAuthField0WnBne := by
    simp only [LinkAuthField0Wn, AfterAuthField0WnBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `sd a0, 112(sp)` save next cursor after field0 walk_next. -/
theorem teerAuthField0WnSd (spC next : Word) :
    cpsTripleWithin 1 AfterAuthField0WnBne AfterAuthField0WnSd teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** memOwn (spC + (112 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** memOwn (spC + (112 : Word))) := by
  have h0 := sd_spec_gen_own_within .x2 .x10 spC next (112 : BitVec 12)
    AfterAuthField0WnBne
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthField0WnBne teerProg 199
        (.SD .x2 .x10 (112 : BitVec 12))
        (by simp only [AfterAuthField0WnBne]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) h0
  have h2 : cpsTripleWithin 1 AfterAuthField0WnBne (AfterAuthField0WnBne + 4)
      teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** memOwn (spC + (112 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** ((spC + (112 : Word)) ↦ₘ next)) := by
    simpa only [se12_112_f0] using h1
  have h3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2
  have hpc : (AfterAuthField0WnBne + 4 : Word) = AfterAuthField0WnSd := by
    simp only [AfterAuthField0WnBne, AfterAuthField0WnSd]; bv_omega
  rw [hpc] at h3
  exact h3

/-- `sub a0, a0, a2` content = next - len (rd = rs1). -/
theorem teerAuthField0Sub (next lenW : Word) :
    cpsTripleWithin 1 AfterAuthField0WnSd AfterAuthField0Sub teerLinkedField0
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW))
      ((.x10 ↦ᵣ next - lenW) ** (.x12 ↦ᵣ lenW)) := by
  have h0 := sub_spec_gen_rd_eq_rs1_within .x10 .x12 next lenW
    AfterAuthField0WnSd (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthField0WnSd teerProg 200
        (.SUB .x10 .x10 .x12) (by simp only [AfterAuthField0WnSd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthField0WnSd + 4 : Word) = AfterAuthField0Sub := by
    simp only [AfterAuthField0WnSd, AfterAuthField0Sub]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv a1, a2` — len into a1 for content_to_u64. -/
theorem teerAuthField0MvA1 (lenW a1Old : Word) :
    cpsTripleWithin 1 AfterAuthField0Sub AtContentToU64 teerLinkedField0
      ((.x12 ↦ᵣ lenW) ** (.x11 ↦ᵣ a1Old))
      ((.x12 ↦ᵣ lenW) ** (.x11 ↦ᵣ lenW)) := by
  have h0 := mv_spec_gen_within .x11 .x12 lenW a1Old AfterAuthField0Sub (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthField0Sub teerProg 201
        (.MV .x11 .x12) (by simp only [AfterAuthField0Sub]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthField0Sub + 4 : Word) = AtContentToU64 := by
    simp only [AfterAuthField0Sub, AtContentToU64]; bv_omega
  rw [hpc] at e0
  exact e0

/-- SUB content + MV a1: AfterAuthField0WnSd → AtContentToU64. -/
theorem teerAuthField0ContentSetup (next lenW a1Old : Word) :
    cpsTripleWithin 2 AfterAuthField0WnSd AtContentToU64 teerLinkedField0
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ next - lenW) ** (.x12 ↦ᵣ lenW) ** (.x11 ↦ᵣ lenW)) := by
  have h0 := teerAuthField0Sub next lenW
  have h0F := cpsTripleWithin_frameR (.x11 ↦ᵣ a1Old) (by pcf) h0
  have h1 := teerAuthField0MvA1 lenW a1Old
  have h1F := cpsTripleWithin_frameR (.x10 ↦ᵣ next - lenW) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

/-- content_to_u64 step bound. -/
def nContentToU64Steps (len : Nat) : Nat := 7 * len + 11

set_option maxRecDepth 8000 in
/-- JAL content_to_u64 under teerLinkedField0.
    a0 = content ptr = srcBase + srcOff; a1 = len. -/
theorem teerContentToU64Call
    (srcBase t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat) (old1 : Word)
    (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (1 + nContentToU64Steps len) AtContentToU64 LinkContentToU64
      teerLinkedField0
      ((.x1 ↦ᵣ old1) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x1 ↦ᵣ LinkContentToU64) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        (fun h =>
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
             ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
          (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
             (.x11 ↦ᵣ (0 : Word)) **
             ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff ≠ 0⌝) h))) := by
  have hret : (LinkContentToU64 &&& ~~~(1 : Word)) = LinkContentToU64 := by
    simp only [LinkContentToU64, E]; decide
  have hleaf := rlp_content_to_u64_spec_within C64 srcBase LinkContentToU64
    t0Old x6Old t2Old t3Old srcBytes srcOff len hlen64 hsalign hslen hsover hsvalid
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin (nContentToU64Steps len) C64 LinkContentToU64 contentToU64Code
      ((.x1 ↦ᵣ LinkContentToU64) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x1 ↦ᵣ LinkContentToU64) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        (fun h =>
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
          (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
             ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
          (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
             (.x11 ↦ᵣ (0 : Word)) **
             ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff ≠ 0⌝) h))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
      -- leaf post has ra already; reshape
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerField0_mono_content hleafP
  have hcall := callWithin_spec AtContentToU64 C64 old1 contentToU64JalOff
    (nContentToU64Steps len) contentToU64JalOff_resolves
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtContentToU64 teerProg 202
        (.JAL .x1 contentToU64JalOff) (by simp only [AtContentToU64]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (by pcf) hcallee
  rw [show (AtContentToU64 + 4 : Word) = LinkContentToU64 from by
    simp only [AtContentToU64, LinkContentToU64]; bv_omega] at hcall
  exact hcall

set_option maxRecDepth 8000 in
/-- BNE a1,x0 ok after content_to_u64 success (status 0) → AfterAuthField0Bne. -/
theorem teerContentToU64BneOk :
    cpsTripleWithin 1 LinkContentToU64 AfterAuthField0Bne teerLinkedField0
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerContentToU64BneOff
    (0 : Word) (0 : Word) LinkContentToU64
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkContentToU64 teerProg 203
        (.BNE .x11 .x0 teerContentToU64BneOff)
        (by simp only [LinkContentToU64]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkContentToU64 + 4 = AfterAuthField0Bne := by
    simp only [LinkContentToU64, AfterAuthField0Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

#print axioms teerAuthField0Prep
#print axioms teerAuthField0WnCall
#print axioms teerAuthField0WnBneOk
#print axioms teerAuthField0WnSd
#print axioms teerAuthField0ContentSetup
#print axioms teerContentToU64Call
#print axioms teerContentToU64BneOk

end EvmAsm.Codegen.TxEip7702TeerSpec
