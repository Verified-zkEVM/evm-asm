/-
  Teer auth-loop inner walk_init on auth-item content:
  MV a0,s9; LD a1,136(sp); JAL walk_init; BNE a2; SD cursors to 112/120(sp).
  AfterAuthItemContentSd (E+756) → AfterAuthItemWiSave (E+780).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopBody
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkInit
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.SAsm.AbiFrameCall
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

/-- PC of auth-item content walk_init JAL (E+764). -/
abbrev AtWalkInitItem : Word := E + 764
abbrev LinkWalkInitItem : Word := E + 768
abbrev AfterWalkInitItemOk : Word := E + 772
abbrev AfterAuthItemWiSave : Word := E + 780

abbrev walkInitItemJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_init
    (GuestAddrs.tx_eip7702_existing_authority_refund + 764)

abbrev teerWalkInitItemBneOff : BitVec 13 := (2080 : BitVec 13)

theorem walkInitItemJalOff_resolves :
    AtWalkInitItem + signExtend21 walkInitItemJalOff = WI := by
  simp only [AtWalkInitItem, WI, walkInitItemJalOff, E]; decide

private theorem se12_112 :
    signExtend12 (112 : BitVec 12) = (112 : Word) := by decide

private theorem se12_120 :
    signExtend12 (120 : BitVec 12) = (120 : Word) := by decide

private theorem se12_136_item :
    signExtend12 (136 : BitVec 12) = (136 : Word) := by decide

/-- `mv a0, s9` (x25 = content ptr) at AfterAuthItemContentSd. -/
theorem teerAuthItemMvA0S9 (content v10 : Word) :
    cpsTripleWithin 1 AfterAuthItemContentSd (E + 760) teerLinkedCount
      ((.x25 ↦ᵣ content) ** (.x10 ↦ᵣ v10))
      ((.x25 ↦ᵣ content) ** (.x10 ↦ᵣ content)) := by
  have h0 := mv_spec_gen_within .x10 .x25 content v10 AfterAuthItemContentSd (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthItemContentSd teerProg 189
        (.MV .x10 .x25) (by simp only [AfterAuthItemContentSd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthItemContentSd + 4 : Word) = E + 760 := by
    simp only [AfterAuthItemContentSd]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `ld a1, 136(sp)` — load content length from frame scratch. -/
theorem teerAuthItemLdA1Len (spC lenW a1Old : Word) :
    cpsTripleWithin 1 (E + 760) AtWalkInitItem teerLinkedCount
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ a1Old) **
        ((spC + (136 : Word)) ↦ₘ lenW))
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ lenW) **
        ((spC + (136 : Word)) ↦ₘ lenW)) := by
  have h0 := ld_spec_gen_within .x11 .x2 spC a1Old lenW
    (136 : BitVec 12) (E + 760) (by decide)
  rw [show spC + signExtend12 (136 : BitVec 12) = spC + (136 : Word) from by
    rw [se12_136_item]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 760) teerProg 190
        (.LD .x11 .x2 (136 : BitVec 12)) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 760 : Word) + 4 = AtWalkInitItem := by
    simp only [AtWalkInitItem]; bv_omega
  rw [hpc] at e0
  exact e0

/-- Prep a0/a1 from s9 + scratch len: AfterAuthItemContentSd → AtWalkInitItem. -/
theorem teerAuthItemWiPrep (spC content lenW v10 v11 : Word) :
    cpsTripleWithin 2 AfterAuthItemContentSd AtWalkInitItem teerLinkedCount
      ((.x25 ↦ᵣ content) ** (.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        ((spC + (136 : Word)) ↦ₘ lenW))
      ((.x25 ↦ᵣ content) ** (.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ content) ** (.x11 ↦ᵣ lenW) **
        ((spC + (136 : Word)) ↦ₘ lenW)) := by
  have h0 := teerAuthItemMvA0S9 content v10
  have h0F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ v11) ** ((spC + (136 : Word)) ↦ₘ lenW)) (by pcf) h0
  have h1 := teerAuthItemLdA1Len spC lenW v11
  have h1F := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ content) ** (.x10 ↦ᵣ content)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

def teerWalkInitItemPrest (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (listOff : Nat) : Assertion :=
  teerWalkInitPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    bs listOff

def teerWalkInitItemShortPost (listBase listLen : Word) (bs : List (BitVec 8))
    (listOff : Nat) (t5Old t6Old : Word) : Assertion :=
  (.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
    (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
    (.x12 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkInitItem) **
    bytesRegion listBase bs

set_option maxRecDepth 8000 in
/-- JAL auth-item walk_init short-success under teerLinkedCount. -/
theorem teerWalkInitItemCall_short
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (listOff : Nat) (old1 : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < bs.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 listOff) + listLen) :
    cpsTripleWithin (1 + 15) AtWalkInitItem LinkWalkInitItem teerLinkedCount
      ((.x1 ↦ᵣ old1) **
        teerWalkInitItemPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      (teerWalkInitItemShortPost listBase listLen bs listOff t5Old t6Old) := by
  have hret : (LinkWalkInitItem &&& ~~~(1 : Word)) = LinkWalkInitItem := by
    simp only [LinkWalkInitItem, E]; decide
  have hleaf0 := rlp_walk_init_short_spec_within WI listBase LinkWalkInitItem listLen
    a2Old t0Old t1Old t2Old t3Old t4Old bs listOff
    hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  rw [hret] at hleaf0
  have hleafF := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
    (by
      apply pcFree_sepConj
      · exact pcFree_regIs
      · exact pcFree_regIs) hleaf0
  have hleafP : cpsTripleWithin 15 WI LinkWalkInitItem walkInitCode
      ((.x1 ↦ᵣ LinkWalkInitItem) **
        teerWalkInitItemPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      (teerWalkInitItemShortPost listBase listLen bs listOff t5Old t6Old) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkInitItemPrest, teerWalkInitPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkInitItemShortPost] at hq ⊢
      xperm_hyp hq) hleafF
  have hcallee := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_early a i (teerEarly_mono_walkInit a i hi)) hleafP
  have hcallee' : cpsTripleWithin 15 WI LinkWalkInitItem teerLinkedCount
      ((.x1 ↦ᵣ LinkWalkInitItem) **
        teerWalkInitItemPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInitItem) **
        ((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
          (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
          (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [teerWalkInitItemShortPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec AtWalkInitItem WI old1 walkInitItemJalOff 15
    walkInitItemJalOff_resolves
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AtWalkInitItem teerProg 191
        (.JAL .x1 walkInitItemJalOff) (by simp only [AtWalkInitItem]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (by
      unfold teerWalkInitItemPrest
      exact teerWalkInitPrest_pcFree listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old
        t5Old t6Old bs listOff)
    hcallee'
  rw [show (AtWalkInitItem + 4 : Word) = LinkWalkInitItem from by
    simp only [AtWalkInitItem, LinkWalkInitItem]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkInitItemShortPost]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- BNE a2,x0 fail: not-taken when a2=0 → AfterWalkInitItemOk. -/
theorem teerWalkInitItemBneOk :
    cpsTripleWithin 1 LinkWalkInitItem AfterWalkInitItemOk teerLinkedCount
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x12 .x0 teerWalkInitItemBneOff
    (0 : Word) (0 : Word) LinkWalkInitItem
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkWalkInitItem teerProg 192
        (.BNE .x12 .x0 teerWalkInitItemBneOff)
        (by simp only [LinkWalkInitItem]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkInitItem + 4 = AfterWalkInitItemOk := by
    simp only [LinkWalkInitItem, AfterWalkInitItemOk]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `sd a0, 112(sp)` — store cursor after item WI. -/
theorem teerAuthItemSdCursor (spC cur : Word) :
    cpsTripleWithin 1 AfterWalkInitItemOk (E + 776) teerLinkedCount
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** memOwn (spC + (112 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** memOwn (spC + (112 : Word))) := by
  have h0 := sd_spec_gen_own_within .x2 .x10 spC cur (112 : BitVec 12)
    AfterWalkInitItemOk
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkInitItemOk teerProg 193
        (.SD .x2 .x10 (112 : BitVec 12))
        (by simp only [AfterWalkInitItemOk]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) h0
  have h2 : cpsTripleWithin 1 AfterWalkInitItemOk (AfterWalkInitItemOk + 4)
      teerLinkedCount
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** memOwn (spC + (112 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** ((spC + (112 : Word)) ↦ₘ cur)) := by
    simpa only [se12_112] using h1
  have h3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2
  have hpc : (AfterWalkInitItemOk + 4 : Word) = E + 776 := by
    simp only [AfterWalkInitItemOk]; bv_omega
  rw [hpc] at h3
  exact h3

/-- `sd a1, 120(sp)` — store end after item WI. -/
theorem teerAuthItemSdEnd (spC endW : Word) :
    cpsTripleWithin 1 (E + 776) AfterAuthItemWiSave teerLinkedCount
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ endW) ** memOwn (spC + (120 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ endW) ** memOwn (spC + (120 : Word))) := by
  have h0 := sd_spec_gen_own_within .x2 .x11 spC endW (120 : BitVec 12)
    (E + 776)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 776) teerProg 194
        (.SD .x2 .x11 (120 : BitVec 12))
        (by bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) h0
  have h2 : cpsTripleWithin 1 (E + 776) ((E + 776 : Word) + 4)
      teerLinkedCount
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ endW) ** memOwn (spC + (120 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ endW) ** ((spC + (120 : Word)) ↦ₘ endW)) := by
    simpa only [se12_120] using h1
  have h3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2
  have hpc : ((E + 776 : Word) + 4) = AfterAuthItemWiSave := by
    simp only [AfterAuthItemWiSave]; bv_omega
  rw [hpc] at h3
  exact h3

/-- Save item WI cursors to 112/120(sp). -/
theorem teerAuthItemWiSaveCursors (spC cur endW : Word) :
    cpsTripleWithin 2 AfterWalkInitItemOk AfterAuthItemWiSave teerLinkedCount
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        memOwn (spC + (112 : Word)) ** memOwn (spC + (120 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        memOwn (spC + (112 : Word)) ** memOwn (spC + (120 : Word))) := by
  have h0 := teerAuthItemSdCursor spC cur
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endW) ** memOwn (spC + (120 : Word))) (by pcf) h0
  have h1 := teerAuthItemSdEnd spC endW
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ cur) ** memOwn (spC + (112 : Word))) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- Short walk_init item + BNE ok + SD cursors: AtWalkInitItem → AfterAuthItemWiSave.
    (a0/a1 already set; use `teerAuthItemWiPrep` first.) -/
theorem teerWalkInitItemShortSuccess
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (listOff : Nat) (old1 spC : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < bs.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 listOff) + listLen) :
    let cur := (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12)
    let endW := (listBase + BitVec.ofNat 64 listOff) + listLen
    cpsTripleWithin (1 + 15 + 1 + 2) AtWalkInitItem AfterAuthItemWiSave teerLinkedCount
      ((.x1 ↦ᵣ old1) ** (.x2 ↦ᵣ spC) **
        memOwn (spC + (112 : Word)) ** memOwn (spC + (120 : Word)) **
        teerWalkInitItemPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInitItem) ** (.x2 ↦ᵣ spC) **
        (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ (0 : Word)) **
        memOwn (spC + (112 : Word)) ** memOwn (spC + (120 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
  intro cur endW
  have hcall := teerWalkInitItemCall_short listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old
    t5Old t6Old bs listOff old1 hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  have hcallF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** memOwn (spC + (112 : Word)) ** memOwn (spC + (120 : Word)))
    (by pcf) hcall
  have hbne := teerWalkInitItemBneOk
  have hbneF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkWalkInitItem) ** (.x2 ↦ᵣ spC) **
      (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
      memOwn (spC + (112 : Word)) ** memOwn (spC + (120 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      bytesRegion listBase bs) (by pcf) hbne
  have hcall' : cpsTripleWithin (1 + 15) AtWalkInitItem LinkWalkInitItem teerLinkedCount
      ((.x1 ↦ᵣ old1) ** (.x2 ↦ᵣ spC) **
        memOwn (spC + (112 : Word)) ** memOwn (spC + (120 : Word)) **
        teerWalkInitItemPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInitItem) ** (.x2 ↦ᵣ spC) **
        (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ (0 : Word)) **
        memOwn (spC + (112 : Word)) ** memOwn (spC + (120 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkInitItemShortPost, cur, endW] at hq ⊢
      xperm_hyp hq) hcallF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcall' hbneF
  have hsave := teerAuthItemWiSaveCursors spC cur endW
  have hsaveF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkWalkInitItem) ** (.x12 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) (by pcf) hsave
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hsaveF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

#print axioms teerAuthItemWiPrep
#print axioms teerWalkInitItemCall_short
#print axioms teerWalkInitItemBneOk
#print axioms teerAuthItemWiSaveCursors
#print axioms teerWalkInitItemShortSuccess

end EvmAsm.Codegen.TxEip7702TeerSpec
