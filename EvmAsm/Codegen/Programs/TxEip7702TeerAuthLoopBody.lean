/-
  Teer auth-loop body: first walk_next of auth item + content SUB/SD scratch.
  AfterAuthLoopBeq (E+728) → AfterAuthItemContentSd (E+756).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopBeq
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNext0
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNextSkip
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

/-- Mono walkNextCode into teerLinkedCount. -/
theorem teerCount_mono_walkNext :
    ∀ a i, walkNextCode a = some i → teerLinkedCount a = some i :=
  fun a i hi => teerCount_mono_early a i (teerEarly_mono_walkNext a i hi)

/-! ## Auth-loop body walk_next 0 @ jal E+736 -/

abbrev AuthLoopWn0JalPc : Word := E + 736
abbrev LinkAuthLoopWn0 : Word := E + 740
abbrev AfterAuthLoopWn0Bne : Word := E + 744
abbrev AfterAuthLoopWn0Save : Word := E + 748
abbrev AfterAuthItemContentSub : Word := E + 752
abbrev AfterAuthItemContentSd : Word := E + 756

def authLoopWn0JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 736)

abbrev teerAuthLoopWn0BneOff : BitVec 13 := (2116 : BitVec 13)

theorem authLoopWn0JalOff_resolves :
    (AuthLoopWn0JalPc + signExtend21 authLoopWn0JalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthLoopWn0JalPc, WN, authLoopWn0JalOff, E]; decide

theorem teerAuthLoopWn0MvA0S5 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterAuthLoopBeq (E + 732) teerLinkedCount
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x21 cursor a0Old AfterAuthLoopBeq (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthLoopBeq teerProg 182
        (.MV .x10 .x21) (by simp only [AfterAuthLoopBeq, AfterAuthLoopLi]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthLoopBeq + 4 : Word) = E + 732 := by
    simp only [AfterAuthLoopBeq, AfterAuthLoopLi]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthLoopWn0MvA1S6 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 732) AuthLoopWn0JalPc teerLinkedCount
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x22 endPtr a1Old (E + 732) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 732) teerProg 183
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 732 : Word) + 4) = AuthLoopWn0JalPc := by
    simp only [AuthLoopWn0JalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerAuthLoopWn0Prep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthLoopBeq AuthLoopWn0JalPc teerLinkedCount
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerAuthLoopWn0MvA0S5 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerAuthLoopWn0MvA1S6 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerAuthLoopWn0Call
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
    cpsTripleWithin (1 + 87) AuthLoopWn0JalPc LinkAuthLoopWn0 teerLinkedCount
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthLoopWn0 listBase endPtr bs srcOff) := by
  have hret : (LinkAuthLoopWn0 &&& ~~~(1 : Word)) = LinkAuthLoopWn0 := by
    simp only [LinkAuthLoopWn0, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthLoopWn0 a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthLoopWn0 walkNextCode
      ((.x1 ↦ᵣ LinkAuthLoopWn0) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthLoopWn0 listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerCount_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthLoopWn0 teerLinkedCount
      ((.x1 ↦ᵣ LinkAuthLoopWn0) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthLoopWn0) **
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
  have hcall := callWithin_spec AuthLoopWn0JalPc WN old1 authLoopWn0JalOff 87
    authLoopWn0JalOff_resolves
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthLoopWn0JalPc teerProg 184
        (.JAL .x1 authLoopWn0JalOff) (by simp only [AuthLoopWn0JalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthLoopWn0JalPc + 4 : Word) = LinkAuthLoopWn0 from by
    simp only [AuthLoopWn0JalPc, LinkAuthLoopWn0]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerAuthLoopWn0BneOk :
    cpsTripleWithin 1 LinkAuthLoopWn0 AfterAuthLoopWn0Bne teerLinkedCount
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthLoopWn0BneOff
    (0 : Word) (0 : Word) LinkAuthLoopWn0
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthLoopWn0 teerProg 185
        (.BNE .x11 .x0 teerAuthLoopWn0BneOff)
        (by simp only [LinkAuthLoopWn0]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthLoopWn0 + 4 = AfterAuthLoopWn0Bne := by
    simp only [LinkAuthLoopWn0, AfterAuthLoopWn0Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerAuthLoopWn0SaveS5 (next v21 : Word) :
    cpsTripleWithin 1 AfterAuthLoopWn0Bne AfterAuthLoopWn0Save teerLinkedCount
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ next) ** (.x21 ↦ᵣ next)) := by
  have h0 := mv_spec_gen_within .x21 .x10 next v21 AfterAuthLoopWn0Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthLoopWn0Bne teerProg 186
        (.MV .x21 .x10) (by simp only [AfterAuthLoopWn0Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthLoopWn0Bne + 4 : Word) = AfterAuthLoopWn0Save := by
    simp only [AfterAuthLoopWn0Bne, AfterAuthLoopWn0Save]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `sub s9, a0, a2` → content = next - len in x25. -/
theorem teerAuthItemContentSub (next lenW v25 : Word) :
    cpsTripleWithin 1 AfterAuthLoopWn0Save AfterAuthItemContentSub teerLinkedCount
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x25 ↦ᵣ v25))
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x25 ↦ᵣ next - lenW)) := by
  have h0 := sub_spec_gen_within .x25 .x10 .x12 next lenW v25
    AfterAuthLoopWn0Save (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthLoopWn0Save teerProg 187
        (.SUB .x25 .x10 .x12) (by simp only [AfterAuthLoopWn0Save]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthLoopWn0Save + 4 : Word) = AfterAuthItemContentSub := by
    simp only [AfterAuthLoopWn0Save, AfterAuthItemContentSub]; bv_omega
  rw [hpc] at e0
  exact e0

private theorem se12_136 :
    signExtend12 (136 : BitVec 12) = (136 : Word) := by decide

/-- `sd a2, 136(sp)` — store auth-item content length into frame scratch. -/
theorem teerAuthItemContentSd (spC lenW : Word) :
    cpsTripleWithin 1 AfterAuthItemContentSub AfterAuthItemContentSd teerLinkedCount
      ((.x2 ↦ᵣ spC) ** (.x12 ↦ᵣ lenW) **
        memOwn (spC + (136 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x12 ↦ᵣ lenW) **
        memOwn (spC + (136 : Word))) := by
  have h0 := sd_spec_gen_own_within .x2 .x12 spC lenW (136 : BitVec 12)
    AfterAuthItemContentSub
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthItemContentSub teerProg 188
        (.SD .x2 .x12 (136 : BitVec 12))
        (by simp only [AfterAuthItemContentSub]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) h0
  have h2 : cpsTripleWithin 1 AfterAuthItemContentSub (AfterAuthItemContentSub + 4)
      teerLinkedCount
      ((.x2 ↦ᵣ spC) ** (.x12 ↦ᵣ lenW) ** memOwn (spC + (136 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x12 ↦ᵣ lenW) ** ((spC + (136 : Word)) ↦ₘ lenW)) := by
    simpa only [se12_136] using h1
  have h3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2
  have hpc : (AfterAuthItemContentSub + 4 : Word) = AfterAuthItemContentSd := by
    simp only [AfterAuthItemContentSub, AfterAuthItemContentSd]; bv_omega
  rw [hpc] at h3
  exact h3

#print axioms teerAuthLoopWn0Prep
#print axioms teerAuthLoopWn0Call
#print axioms teerAuthLoopWn0BneOk
#print axioms teerAuthLoopWn0SaveS5
#print axioms teerAuthItemContentSub
#print axioms teerAuthItemContentSd

end EvmAsm.Codegen.TxEip7702TeerSpec
