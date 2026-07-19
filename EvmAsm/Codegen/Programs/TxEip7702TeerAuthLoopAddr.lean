/-
  Teer auth-loop address field after chain-id ok:
  reload 112/120, walk_next@836, SD, LI 20, BNE len=20, SUB x27=content.
  AfterChainOk (E+828) → AfterAuthAddrSub (E+860).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopChain
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNext0
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen

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

abbrev AuthAddrWnJalPc : Word := E + 836
abbrev LinkAuthAddrWn : Word := E + 840
abbrev AfterAuthAddrWnBne : Word := E + 844
abbrev AfterAuthAddrWnSd : Word := E + 848
abbrev AfterAuthAddrLi20 : Word := E + 852
abbrev AfterAuthAddrLenBne : Word := E + 856
abbrev AfterAuthAddrSub : Word := E + 860

def authAddrWnJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 836)

abbrev teerAuthAddrWnBneOff : BitVec 13 := (2008 : BitVec 13)
abbrev teerAuthAddrLenBneOff : BitVec 13 := (1996 : BitVec 13)

theorem authAddrWnJalOff_resolves :
    (AuthAddrWnJalPc + signExtend21 authAddrWnJalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthAddrWnJalPc, WN, authAddrWnJalOff, E]; decide

private theorem se12_112_addr :
    signExtend12 (112 : BitVec 12) = (112 : Word) := by decide

private theorem se12_120_addr :
    signExtend12 (120 : BitVec 12) = (120 : Word) := by decide

/-- `ld a0, 112(sp)` reload cursor. -/
theorem teerAuthAddrLdA0 (spC cur a0Old : Word) :
    cpsTripleWithin 1 AfterChainOk (E + 832) teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ a0Old) ** ((spC + (112 : Word)) ↦ₘ cur))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** ((spC + (112 : Word)) ↦ₘ cur)) := by
  have h0 := ld_spec_gen_within .x10 .x2 spC a0Old cur
    (112 : BitVec 12) AfterChainOk (by decide)
  rw [show spC + signExtend12 (112 : BitVec 12) = spC + (112 : Word) from by
    rw [se12_112_addr]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterChainOk teerProg 207
        (.LD .x10 .x2 (112 : BitVec 12))
        (by simp only [AfterChainOk]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterChainOk + 4 : Word) = E + 832 := by
    simp only [AfterChainOk]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `ld a1, 120(sp)` reload end. -/
theorem teerAuthAddrLdA1 (spC endW a1Old : Word) :
    cpsTripleWithin 1 (E + 832) AuthAddrWnJalPc teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ a1Old) ** ((spC + (120 : Word)) ↦ₘ endW))
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ endW) ** ((spC + (120 : Word)) ↦ₘ endW)) := by
  have h0 := ld_spec_gen_within .x11 .x2 spC a1Old endW
    (120 : BitVec 12) (E + 832) (by decide)
  rw [show spC + signExtend12 (120 : BitVec 12) = spC + (120 : Word) from by
    rw [se12_120_addr]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 832) teerProg 208
        (.LD .x11 .x2 (120 : BitVec 12)) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 832 : Word) + 4 = AuthAddrWnJalPc := by
    simp only [AuthAddrWnJalPc]; bv_omega
  rw [hpc] at e0
  exact e0

/-- Reload a0/a1 from scratch: AfterChainOk → AuthAddrWnJalPc. -/
theorem teerAuthAddrPrep (spC cur endW a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterChainOk AuthAddrWnJalPc teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        ((spC + (112 : Word)) ↦ₘ cur) ** ((spC + (120 : Word)) ↦ₘ endW))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        ((spC + (112 : Word)) ↦ₘ cur) ** ((spC + (120 : Word)) ↦ₘ endW)) := by
  have h0 := teerAuthAddrLdA0 spC cur a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ a1Old) ** ((spC + (120 : Word)) ↦ₘ endW)) (by pcf) h0
  have h1 := teerAuthAddrLdA1 spC endW a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ cur) ** ((spC + (112 : Word)) ↦ₘ cur)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- JAL walk_next address field under teerLinkedField0. -/
theorem teerAuthAddrWnCall
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
    cpsTripleWithin (1 + 87) AuthAddrWnJalPc LinkAuthAddrWn teerLinkedField0
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthAddrWn listBase endPtr bs srcOff) := by
  have hret : (LinkAuthAddrWn &&& ~~~(1 : Word)) = LinkAuthAddrWn := by
    simp only [LinkAuthAddrWn, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthAddrWn a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthAddrWn walkNextCode
      ((.x1 ↦ᵣ LinkAuthAddrWn) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthAddrWn listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerField0_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthAddrWn teerLinkedField0
      ((.x1 ↦ᵣ LinkAuthAddrWn) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthAddrWn) **
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
  have hcall := callWithin_spec AuthAddrWnJalPc WN old1 authAddrWnJalOff 87
    authAddrWnJalOff_resolves
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthAddrWnJalPc teerProg 209
        (.JAL .x1 authAddrWnJalOff) (by simp only [AuthAddrWnJalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthAddrWnJalPc + 4 : Word) = LinkAuthAddrWn from by
    simp only [AuthAddrWnJalPc, LinkAuthAddrWn]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- BNE a1,x0 ok (status 0) → AfterAuthAddrWnBne. -/
theorem teerAuthAddrWnBneOk :
    cpsTripleWithin 1 LinkAuthAddrWn AfterAuthAddrWnBne teerLinkedField0
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthAddrWnBneOff
    (0 : Word) (0 : Word) LinkAuthAddrWn
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthAddrWn teerProg 210
        (.BNE .x11 .x0 teerAuthAddrWnBneOff)
        (by simp only [LinkAuthAddrWn]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthAddrWn + 4 = AfterAuthAddrWnBne := by
    simp only [LinkAuthAddrWn, AfterAuthAddrWnBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `sd a0, 112(sp)` save next cursor after address walk_next. -/
theorem teerAuthAddrWnSd (spC next : Word) :
    cpsTripleWithin 1 AfterAuthAddrWnBne AfterAuthAddrWnSd teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** memOwn (spC + (112 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** memOwn (spC + (112 : Word))) := by
  have h0 := sd_spec_gen_own_within .x2 .x10 spC next (112 : BitVec 12)
    AfterAuthAddrWnBne
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthAddrWnBne teerProg 211
        (.SD .x2 .x10 (112 : BitVec 12))
        (by simp only [AfterAuthAddrWnBne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have h2 : cpsTripleWithin 1 AfterAuthAddrWnBne (AfterAuthAddrWnBne + 4)
      teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** memOwn (spC + (112 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** ((spC + (112 : Word)) ↦ₘ next)) := by
    simpa only [se12_112_addr] using h1
  have h3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2
  have hpc : (AfterAuthAddrWnBne + 4 : Word) = AfterAuthAddrWnSd := by
    simp only [AfterAuthAddrWnBne, AfterAuthAddrWnSd]; bv_omega
  rw [hpc] at h3
  exact h3

/-- `li t2, 20` expected address length. -/
theorem teerAuthAddrLi20 (t2Old : Word) :
    cpsTripleWithin 1 AfterAuthAddrWnSd AfterAuthAddrLi20 teerLinkedField0
      (.x7 ↦ᵣ t2Old)
      (.x7 ↦ᵣ (20 : Word)) := by
  have h0 := li_spec_gen_within .x7 t2Old (20 : Word) AfterAuthAddrWnSd (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthAddrWnSd teerProg 212
        (.LI .x7 (20 : Word)) (by simp only [AfterAuthAddrWnSd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthAddrWnSd + 4 : Word) = AfterAuthAddrLi20 := by
    simp only [AfterAuthAddrWnSd, AfterAuthAddrLi20]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `bne a2, t2` not-taken: content length = 20 → AfterAuthAddrLenBne. -/
theorem teerAuthAddrLenBneOk :
    cpsTripleWithin 1 AfterAuthAddrLi20 AfterAuthAddrLenBne teerLinkedField0
      ((.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)))
      ((.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word))) := by
  have hbr := bne_spec_gen_within .x12 .x7 teerAuthAddrLenBneOff
    (20 : Word) (20 : Word) AfterAuthAddrLi20
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthAddrLi20 teerProg 213
        (.BNE .x12 .x7 teerAuthAddrLenBneOff)
        (by simp only [AfterAuthAddrLi20]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterAuthAddrLi20 + 4 = AfterAuthAddrLenBne := by
    simp only [AfterAuthAddrLi20, AfterAuthAddrLenBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `sub s11, a0, a2` → address content ptr in x27. -/
theorem teerAuthAddrSub (next lenW v27 : Word) :
    cpsTripleWithin 1 AfterAuthAddrLenBne AfterAuthAddrSub teerLinkedField0
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x27 ↦ᵣ v27))
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x27 ↦ᵣ next - lenW)) := by
  have h0 := sub_spec_gen_within .x27 .x10 .x12 next lenW v27
    AfterAuthAddrLenBne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthAddrLenBne teerProg 214
        (.SUB .x27 .x10 .x12) (by simp only [AfterAuthAddrLenBne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthAddrLenBne + 4 : Word) = AfterAuthAddrSub := by
    simp only [AfterAuthAddrLenBne, AfterAuthAddrSub]; bv_omega
  rw [hpc] at e0
  exact e0

#print axioms teerAuthAddrPrep
#print axioms teerAuthAddrWnCall
#print axioms teerAuthAddrWnBneOk
#print axioms teerAuthAddrWnSd
#print axioms teerAuthAddrLi20
#print axioms teerAuthAddrLenBneOk
#print axioms teerAuthAddrSub

end EvmAsm.Codegen.TxEip7702TeerSpec
