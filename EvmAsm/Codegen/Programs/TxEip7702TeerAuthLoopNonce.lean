/-
  Teer auth-loop nonce field after address content ptr in x27:
  reload 112/120, walk_next@868, SD, SUB+MV, content_to_u64@888, BNE ok.
  AfterAuthAddrSub (E+860) → AfterAuthNonceBne (E+896).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopAddr
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

abbrev AuthNonceWnJalPc : Word := E + 868
abbrev LinkAuthNonceWn : Word := E + 872
abbrev AfterAuthNonceWnBne : Word := E + 876
abbrev AfterAuthNonceWnSd : Word := E + 880
abbrev AfterAuthNonceSub : Word := E + 884
abbrev AtContentToU64Nonce : Word := E + 888
abbrev LinkContentToU64Nonce : Word := E + 892
abbrev AfterAuthNonceBne : Word := E + 896

def authNonceWnJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 868)

abbrev teerAuthNonceWnBneOff : BitVec 13 := (1976 : BitVec 13)

def contentToU64NonceJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_content_to_u64
    (GuestAddrs.tx_eip7702_existing_authority_refund + 888)

abbrev teerContentToU64NonceBneOff : BitVec 13 := (1956 : BitVec 13)

theorem authNonceWnJalOff_resolves :
    (AuthNonceWnJalPc + signExtend21 authNonceWnJalOff) &&& ~~~(1 : Word) = WN := by
  simp only [AuthNonceWnJalPc, WN, authNonceWnJalOff, E]; decide

theorem contentToU64NonceJalOff_resolves :
    AtContentToU64Nonce + signExtend21 contentToU64NonceJalOff = C64 := by
  simp only [AtContentToU64Nonce, C64, contentToU64NonceJalOff, E]; decide

private theorem se12_112_n :
    signExtend12 (112 : BitVec 12) = (112 : Word) := by decide

private theorem se12_120_n :
    signExtend12 (120 : BitVec 12) = (120 : Word) := by decide

/-- `ld a0, 112(sp)` reload cursor. -/
theorem teerAuthNonceLdA0 (spC cur a0Old : Word) :
    cpsTripleWithin 1 AfterAuthAddrSub (E + 864) teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ a0Old) ** ((spC + (112 : Word)) ↦ₘ cur))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** ((spC + (112 : Word)) ↦ₘ cur)) := by
  have h0 := ld_spec_gen_within .x10 .x2 spC a0Old cur
    (112 : BitVec 12) AfterAuthAddrSub (by decide)
  rw [show spC + signExtend12 (112 : BitVec 12) = spC + (112 : Word) from by
    rw [se12_112_n]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthAddrSub teerProg 215
        (.LD .x10 .x2 (112 : BitVec 12))
        (by simp only [AfterAuthAddrSub]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthAddrSub + 4 : Word) = E + 864 := by
    simp only [AfterAuthAddrSub]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `ld a1, 120(sp)` reload end. -/
theorem teerAuthNonceLdA1 (spC endW a1Old : Word) :
    cpsTripleWithin 1 (E + 864) AuthNonceWnJalPc teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ a1Old) ** ((spC + (120 : Word)) ↦ₘ endW))
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ endW) ** ((spC + (120 : Word)) ↦ₘ endW)) := by
  have h0 := ld_spec_gen_within .x11 .x2 spC a1Old endW
    (120 : BitVec 12) (E + 864) (by decide)
  rw [show spC + signExtend12 (120 : BitVec 12) = spC + (120 : Word) from by
    rw [se12_120_n]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 864) teerProg 216
        (.LD .x11 .x2 (120 : BitVec 12)) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 864 : Word) + 4 = AuthNonceWnJalPc := by
    simp only [AuthNonceWnJalPc]; bv_omega
  rw [hpc] at e0
  exact e0

/-- Reload a0/a1: AfterAuthAddrSub → AuthNonceWnJalPc. -/
theorem teerAuthNoncePrep (spC cur endW a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterAuthAddrSub AuthNonceWnJalPc teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        ((spC + (112 : Word)) ↦ₘ cur) ** ((spC + (120 : Word)) ↦ₘ endW))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        ((spC + (112 : Word)) ↦ₘ cur) ** ((spC + (120 : Word)) ↦ₘ endW)) := by
  have h0 := teerAuthNonceLdA0 spC cur a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ a1Old) ** ((spC + (120 : Word)) ↦ₘ endW)) (by pcf) h0
  have h1 := teerAuthNonceLdA1 spC endW a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ cur) ** ((spC + (112 : Word)) ↦ₘ cur)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- JAL walk_next nonce field. -/
theorem teerAuthNonceWnCall
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
    cpsTripleWithin (1 + 87) AuthNonceWnJalPc LinkAuthNonceWn teerLinkedField0
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthNonceWn listBase endPtr bs srcOff) := by
  have hret : (LinkAuthNonceWn &&& ~~~(1 : Word)) = LinkAuthNonceWn := by
    simp only [LinkAuthNonceWn, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkAuthNonceWn a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkAuthNonceWn walkNextCode
      ((.x1 ↦ᵣ LinkAuthNonceWn) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkAuthNonceWn listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerField0_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkAuthNonceWn teerLinkedField0
      ((.x1 ↦ᵣ LinkAuthNonceWn) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkAuthNonceWn) **
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
  have hcall := callWithin_spec AuthNonceWnJalPc WN old1 authNonceWnJalOff 87
    authNonceWnJalOff_resolves
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AuthNonceWnJalPc teerProg 217
        (.JAL .x1 authNonceWnJalOff) (by simp only [AuthNonceWnJalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (AuthNonceWnJalPc + 4 : Word) = LinkAuthNonceWn from by
    simp only [AuthNonceWnJalPc, LinkAuthNonceWn]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- BNE a1,x0 ok → AfterAuthNonceWnBne. -/
theorem teerAuthNonceWnBneOk :
    cpsTripleWithin 1 LinkAuthNonceWn AfterAuthNonceWnBne teerLinkedField0
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerAuthNonceWnBneOff
    (0 : Word) (0 : Word) LinkAuthNonceWn
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkAuthNonceWn teerProg 218
        (.BNE .x11 .x0 teerAuthNonceWnBneOff)
        (by simp only [LinkAuthNonceWn]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkAuthNonceWn + 4 = AfterAuthNonceWnBne := by
    simp only [LinkAuthNonceWn, AfterAuthNonceWnBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `sd a0, 112(sp)` save next cursor. -/
theorem teerAuthNonceWnSd (spC next : Word) :
    cpsTripleWithin 1 AfterAuthNonceWnBne AfterAuthNonceWnSd teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** memOwn (spC + (112 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** memOwn (spC + (112 : Word))) := by
  have h0 := sd_spec_gen_own_within .x2 .x10 spC next (112 : BitVec 12)
    AfterAuthNonceWnBne
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthNonceWnBne teerProg 219
        (.SD .x2 .x10 (112 : BitVec 12))
        (by simp only [AfterAuthNonceWnBne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have h2 : cpsTripleWithin 1 AfterAuthNonceWnBne (AfterAuthNonceWnBne + 4)
      teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** memOwn (spC + (112 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ next) ** ((spC + (112 : Word)) ↦ₘ next)) := by
    simpa only [se12_112_n] using h1
  have h3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2
  have hpc : (AfterAuthNonceWnBne + 4 : Word) = AfterAuthNonceWnSd := by
    simp only [AfterAuthNonceWnBne, AfterAuthNonceWnSd]; bv_omega
  rw [hpc] at h3
  exact h3

/-- `sub a0, a0, a2` content = next - len. -/
theorem teerAuthNonceSub (next lenW : Word) :
    cpsTripleWithin 1 AfterAuthNonceWnSd AfterAuthNonceSub teerLinkedField0
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW))
      ((.x10 ↦ᵣ next - lenW) ** (.x12 ↦ᵣ lenW)) := by
  have h0 := sub_spec_gen_rd_eq_rs1_within .x10 .x12 next lenW
    AfterAuthNonceWnSd (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthNonceWnSd teerProg 220
        (.SUB .x10 .x10 .x12) (by simp only [AfterAuthNonceWnSd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthNonceWnSd + 4 : Word) = AfterAuthNonceSub := by
    simp only [AfterAuthNonceWnSd, AfterAuthNonceSub]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv a1, a2` len into a1. -/
theorem teerAuthNonceMvA1 (lenW a1Old : Word) :
    cpsTripleWithin 1 AfterAuthNonceSub AtContentToU64Nonce teerLinkedField0
      ((.x12 ↦ᵣ lenW) ** (.x11 ↦ᵣ a1Old))
      ((.x12 ↦ᵣ lenW) ** (.x11 ↦ᵣ lenW)) := by
  have h0 := mv_spec_gen_within .x11 .x12 lenW a1Old AfterAuthNonceSub (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthNonceSub teerProg 221
        (.MV .x11 .x12) (by simp only [AfterAuthNonceSub]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthNonceSub + 4 : Word) = AtContentToU64Nonce := by
    simp only [AfterAuthNonceSub, AtContentToU64Nonce]; bv_omega
  rw [hpc] at e0
  exact e0

/-- SUB + MV a1: AfterAuthNonceWnSd → AtContentToU64Nonce. -/
theorem teerAuthNonceContentSetup (next lenW a1Old : Word) :
    cpsTripleWithin 2 AfterAuthNonceWnSd AtContentToU64Nonce teerLinkedField0
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x11 ↦ᵣ a1Old))
      ((.x10 ↦ᵣ next - lenW) ** (.x12 ↦ᵣ lenW) ** (.x11 ↦ᵣ lenW)) := by
  have h0 := teerAuthNonceSub next lenW
  have h0F := cpsTripleWithin_frameR (.x11 ↦ᵣ a1Old) (by pcf) h0
  have h1 := teerAuthNonceMvA1 lenW a1Old
  have h1F := cpsTripleWithin_frameR (.x10 ↦ᵣ next - lenW) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- JAL content_to_u64 for nonce under teerLinkedField0.
    a0 = content ptr = srcBase + srcOff; a1 = len. -/
theorem teerContentToU64NonceCall
    (srcBase t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat) (old1 : Word)
    (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (1 + nContentToU64Steps len) AtContentToU64Nonce LinkContentToU64Nonce
      teerLinkedField0
      ((.x1 ↦ᵣ old1) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x1 ↦ᵣ LinkContentToU64Nonce) **
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
  have hret : (LinkContentToU64Nonce &&& ~~~(1 : Word)) = LinkContentToU64Nonce := by
    simp only [LinkContentToU64Nonce, E]; decide
  have hleaf := rlp_content_to_u64_spec_within C64 srcBase LinkContentToU64Nonce
    t0Old x6Old t2Old t3Old srcBytes srcOff len hlen64 hsalign hslen hsover hsvalid
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin (nContentToU64Steps len) C64 LinkContentToU64Nonce
      contentToU64Code
      ((.x1 ↦ᵣ LinkContentToU64Nonce) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x1 ↦ᵣ LinkContentToU64Nonce) **
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
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerField0_mono_content hleafP
  have hcall := callWithin_spec AtContentToU64Nonce C64 old1 contentToU64NonceJalOff
    (nContentToU64Steps len) contentToU64NonceJalOff_resolves
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtContentToU64Nonce teerProg 222
        (.JAL .x1 contentToU64NonceJalOff) (by simp only [AtContentToU64Nonce]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (by pcf) hcallee
  rw [show (AtContentToU64Nonce + 4 : Word) = LinkContentToU64Nonce from by
    simp only [AtContentToU64Nonce, LinkContentToU64Nonce]; bv_omega] at hcall
  exact hcall

set_option maxRecDepth 8000 in
/-- BNE a1,x0 ok after content_to_u64 nonce → AfterAuthNonceBne. -/
theorem teerContentToU64NonceBneOk :
    cpsTripleWithin 1 LinkContentToU64Nonce AfterAuthNonceBne teerLinkedField0
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerContentToU64NonceBneOff
    (0 : Word) (0 : Word) LinkContentToU64Nonce
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkContentToU64Nonce teerProg 223
        (.BNE .x11 .x0 teerContentToU64NonceBneOff)
        (by simp only [LinkContentToU64Nonce]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkContentToU64Nonce + 4 = AfterAuthNonceBne := by
    simp only [LinkContentToU64Nonce, AfterAuthNonceBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

#print axioms teerAuthNoncePrep
#print axioms teerAuthNonceWnCall
#print axioms teerAuthNonceWnBneOk
#print axioms teerAuthNonceWnSd
#print axioms teerAuthNonceContentSetup
#print axioms teerContentToU64NonceCall
#print axioms teerContentToU64NonceBneOk

end EvmAsm.Codegen.TxEip7702TeerSpec
