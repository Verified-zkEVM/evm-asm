/-
  Teer auth-loop start: MV a0/a1 from s5/s6 + walk_init short Call+BNE+save
  s5/s6 + LI s8,0. AfterAuthCountLoad (E+696) → AfterAuthLoopLi (E+724).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerListCount
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkInit
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.MeasureLoop
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

/-- PC of auth-loop walk_init JAL (E+704). -/
abbrev AtWalkInitAuth : Word := E + 704
abbrev LinkWalkInitAuth : Word := E + 708
abbrev AfterWalkInitAuthOk : Word := E + 712
abbrev AfterWalkInitAuthSave : Word := E + 720
abbrev AfterAuthLoopLi : Word := E + 724

abbrev walkInitAuthJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_init
    (GuestAddrs.tx_eip7702_existing_authority_refund + 704)

abbrev teerWalkInitAuthBneOff : BitVec 13 := (2148 : BitVec 13)

theorem walkInitAuthJalOff_resolves :
    AtWalkInitAuth + signExtend21 walkInitAuthJalOff = WI := by
  simp only [AtWalkInitAuth, WI, walkInitAuthJalOff, E]; decide

/-- `mv a0, s5` at AfterAuthCountLoad. -/
theorem teerAuthLoopMvA0 (s5 v10 : Word) :
    cpsTripleWithin 1 AfterAuthCountLoad (E + 700) teerLinkedCount
      ((.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ v10))
      ((.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ s5)) := by
  have h0 := mv_spec_gen_within .x10 .x21 s5 v10 AfterAuthCountLoad (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthCountLoad teerProg 174
        (.MV .x10 .x21) (by simp only [AfterAuthCountLoad]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthCountLoad + 4 : Word) = E + 700 := by
    simp only [AfterAuthCountLoad]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv a1, s6` at E+700 → AtWalkInitAuth. -/
theorem teerAuthLoopMvA1 (s6 v11 : Word) :
    cpsTripleWithin 1 (E + 700) AtWalkInitAuth teerLinkedCount
      ((.x22 ↦ᵣ s6) ** (.x11 ↦ᵣ v11))
      ((.x22 ↦ᵣ s6) ** (.x11 ↦ᵣ s6)) := by
  have h0 := mv_spec_gen_within .x11 .x22 s6 v11 (E + 700) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 700) teerProg 175
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 700 : Word) + 4 = AtWalkInitAuth := by
    simp only [AtWalkInitAuth]; bv_omega
  rw [hpc] at e0
  exact e0

/-- Prep a0/a1 from s5/s6: AfterAuthCountLoad → AtWalkInitAuth. -/
theorem teerAuthLoopPrep (s5 s6 v10 v11 : Word) :
    cpsTripleWithin 2 AfterAuthCountLoad AtWalkInitAuth teerLinkedCount
      ((.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11))
      ((.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x10 ↦ᵣ s5) ** (.x11 ↦ᵣ s6)) := by
  have h0 := teerAuthLoopMvA0 s5 v10
  have h0F := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ s6) ** (.x11 ↦ᵣ v11)) (by pcf) h0
  have h1 := teerAuthLoopMvA1 s6 v11
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ s5)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

def teerWalkInitAuthPrest (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (listOff : Nat) : Assertion :=
  teerWalkInitPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    bs listOff

def teerWalkInitAuthShortPost (listBase listLen : Word) (bs : List (BitVec 8))
    (listOff : Nat) (t5Old t6Old : Word) : Assertion :=
  (.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
    (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
    (.x12 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkInitAuth) **
    bytesRegion listBase bs

set_option maxRecDepth 8000 in
/-- JAL auth-loop walk_init short-success under teerLinkedCount. -/
theorem teerWalkInitAuthCall_short
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
    cpsTripleWithin (1 + 15) AtWalkInitAuth LinkWalkInitAuth teerLinkedCount
      ((.x1 ↦ᵣ old1) **
        teerWalkInitAuthPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      (teerWalkInitAuthShortPost listBase listLen bs listOff t5Old t6Old) := by
  have hret : (LinkWalkInitAuth &&& ~~~(1 : Word)) = LinkWalkInitAuth := by
    simp only [LinkWalkInitAuth, E]; decide
  have hleaf0 := rlp_walk_init_short_spec_within WI listBase LinkWalkInitAuth listLen
    a2Old t0Old t1Old t2Old t3Old t4Old bs listOff
    hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  rw [hret] at hleaf0
  have hleafF := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
    (by
      apply pcFree_sepConj
      · exact pcFree_regIs
      · exact pcFree_regIs) hleaf0
  have hleafP : cpsTripleWithin 15 WI LinkWalkInitAuth walkInitCode
      ((.x1 ↦ᵣ LinkWalkInitAuth) **
        teerWalkInitAuthPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      (teerWalkInitAuthShortPost listBase listLen bs listOff t5Old t6Old) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkInitAuthPrest, teerWalkInitPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkInitAuthShortPost] at hq ⊢
      xperm_hyp hq) hleafF
  have hcallee := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_early a i (teerEarly_mono_walkInit a i hi)) hleafP
  have hcallee' : cpsTripleWithin 15 WI LinkWalkInitAuth teerLinkedCount
      ((.x1 ↦ᵣ LinkWalkInitAuth) **
        teerWalkInitAuthPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInitAuth) **
        ((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
          (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
          (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [teerWalkInitAuthShortPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec AtWalkInitAuth WI old1 walkInitAuthJalOff 15
    walkInitAuthJalOff_resolves
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AtWalkInitAuth teerProg 176
        (.JAL .x1 walkInitAuthJalOff) (by simp only [AtWalkInitAuth]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (by
      unfold teerWalkInitAuthPrest
      exact teerWalkInitPrest_pcFree listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old
        t5Old t6Old bs listOff)
    hcallee'
  rw [show (AtWalkInitAuth + 4 : Word) = LinkWalkInitAuth from by
    simp only [AtWalkInitAuth, LinkWalkInitAuth]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkInitAuthShortPost]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- BNE a2,x0 fail: not-taken when a2=0 → AfterWalkInitAuthOk. -/
theorem teerWalkInitAuthBneOk :
    cpsTripleWithin 1 LinkWalkInitAuth AfterWalkInitAuthOk teerLinkedCount
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x12 .x0 teerWalkInitAuthBneOff
    (0 : Word) (0 : Word) LinkWalkInitAuth
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkWalkInitAuth teerProg 177
        (.BNE .x12 .x0 teerWalkInitAuthBneOff)
        (by simp only [LinkWalkInitAuth]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkInitAuth + 4 = AfterWalkInitAuthOk := by
    simp only [LinkWalkInitAuth, AfterWalkInitAuthOk]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `mv s5, a0` after auth WI ok. -/
theorem teerAuthLoopMvS5 (cur v21 : Word) :
    cpsTripleWithin 1 AfterWalkInitAuthOk (E + 716) teerLinkedCount
      ((.x10 ↦ᵣ cur) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ cur) ** (.x21 ↦ᵣ cur)) := by
  have h0 := mv_spec_gen_within .x21 .x10 cur v21 AfterWalkInitAuthOk (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkInitAuthOk teerProg 178
        (.MV .x21 .x10) (by simp only [AfterWalkInitAuthOk]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkInitAuthOk + 4 : Word) = E + 716 := by
    simp only [AfterWalkInitAuthOk]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv s6, a1` → AfterWalkInitAuthSave. -/
theorem teerAuthLoopMvS6 (endW v22 : Word) :
    cpsTripleWithin 1 (E + 716) AfterWalkInitAuthSave teerLinkedCount
      ((.x11 ↦ᵣ endW) ** (.x22 ↦ᵣ v22))
      ((.x11 ↦ᵣ endW) ** (.x22 ↦ᵣ endW)) := by
  have h0 := mv_spec_gen_within .x22 .x11 endW v22 (E + 716) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 716) teerProg 179
        (.MV .x22 .x11) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 716 : Word) + 4 = AfterWalkInitAuthSave := by
    simp only [AfterWalkInitAuthSave]; bv_omega
  rw [hpc] at e0
  exact e0

set_option maxRecDepth 8000 in
/-- Save auth cursors s5/s6. -/
theorem teerWalkInitAuthSaveCursors (cur endW v21 v22 : Word) :
    cpsTripleWithin 2 AfterWalkInitAuthOk AfterWalkInitAuthSave teerLinkedCount
      ((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW)) := by
  have h0 := teerAuthLoopMvS5 cur v21
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endW) ** (.x22 ↦ᵣ v22)) (by pcf) h0
  have h1 := teerAuthLoopMvS6 endW v22
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ cur) ** (.x21 ↦ᵣ cur)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

/-- `li s8, 0` at AfterWalkInitAuthSave → AfterAuthLoopLi. -/
theorem teerAuthLoopLiS8 (v24 : Word) :
    cpsTripleWithin 1 AfterWalkInitAuthSave AfterAuthLoopLi teerLinkedCount
      (.x24 ↦ᵣ v24) (.x24 ↦ᵣ (0 : Word)) := by
  have h0 := li_spec_gen_within .x24 v24 (0 : Word) AfterWalkInitAuthSave (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkInitAuthSave teerProg 180
        (.LI .x24 (0 : Word)) (by simp only [AfterWalkInitAuthSave]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkInitAuthSave + 4 : Word) = AfterAuthLoopLi := by
    simp only [AfterWalkInitAuthSave, AfterAuthLoopLi]; bv_omega
  rw [hpc] at e0
  exact e0

set_option maxRecDepth 8000 in
/-- Short walk_init auth call + BNE ok + save s5/s6: AtWalkInitAuth → AfterWalkInitAuthSave.
    (a0/a1 already set; use `teerAuthLoopPrep` first.) -/
theorem teerWalkInitAuthShortSuccess
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (listOff : Nat) (old1 v21 v22 : Word)
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
    cpsTripleWithin (1 + 15 + 1 + 2) AtWalkInitAuth AfterWalkInitAuthSave teerLinkedCount
      ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        teerWalkInitAuthPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInitAuth) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
  intro cur endW
  have hcall := teerWalkInitAuthCall_short listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old
    t5Old t6Old bs listOff old1 hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  have hcallF := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22)) (by pcf) hcall
  have hbne := teerWalkInitAuthBneOk
  have hbneF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkWalkInitAuth) **
      (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
      (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      bytesRegion listBase bs) (by pcf) hbne
  have hcall' : cpsTripleWithin (1 + 15) AtWalkInitAuth LinkWalkInitAuth teerLinkedCount
      ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        teerWalkInitAuthPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInitAuth) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkInitAuthShortPost, cur, endW] at hq ⊢
      xperm_hyp hq) hcallF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcall' hbneF
  have hsave := teerWalkInitAuthSaveCursors cur endW v21 v22
  have hsaveF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkWalkInitAuth) ** (.x12 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) (by pcf) hsave
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hsaveF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

#print axioms teerAuthLoopPrep
#print axioms teerWalkInitAuthCall_short
#print axioms teerWalkInitAuthBneOk
#print axioms teerWalkInitAuthSaveCursors
#print axioms teerAuthLoopLiS8
#print axioms teerWalkInitAuthShortSuccess

/-- Step count: Prep(2) + ShortSuccess(19) + LI s8(1) = 22. -/
def nAuthLoopStartShort : Nat := 2 + (1 + 15 + 1 + 2) + 1

set_option maxRecDepth 8000 in
/-- Auth-loop start short path: AfterAuthCountLoad → AfterAuthLoopLi.
    Requires `s5 = listBase + listOff`, `s6 = listLen` (content setup when listOff=0).
    Prest owns raw a0/a1 (v10/v11); Prep overwrites them from s5/s6. -/
theorem teerAuthLoopStartShort
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (listOff : Nat)
    (old1 v10 v11 v21 v22 v24 : Word)
    (hs5 : v21 = listBase + BitVec.ofNat 64 listOff)
    (hs6 : v22 = listLen)
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
    cpsTripleWithin nAuthLoopStartShort AfterAuthCountLoad AfterAuthLoopLi teerLinkedCount
      ((.x1 ↦ᵣ old1) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x24 ↦ᵣ v24) **
        (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      ((.x1 ↦ᵣ LinkWalkInitAuth) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
        (.x24 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
  intro cur endW
  have hprep := teerAuthLoopPrep v21 v22 v10 v11
  have hprepF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) **
      (.x12 ↦ᵣ a2Old) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) (by pcf) hprep
  -- After Prep: a0=v21, a1=v22 → rewrite to listBase+listOff / listLen for WI prest
  have hprepW : cpsTripleWithin 2 AfterAuthCountLoad AtWalkInitAuth teerLinkedCount
      ((.x1 ↦ᵣ old1) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x24 ↦ᵣ v24) **
        (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x24 ↦ᵣ v24) **
        teerWalkInitAuthPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old
          t5Old t6Old bs listOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkInitAuthPrest, teerWalkInitPrest, hs5, hs6] at hq ⊢
      xperm_hyp hq) hprepF
  have hwi := teerWalkInitAuthShortSuccess listBase listLen a2Old t0Old t1Old t2Old t3Old
    t4Old t5Old t6Old bs listOff old1 v21 v22 hsalign hoff hover hvalid hlen h_ge h_hi
    h_exact
  have hwiF := cpsTripleWithin_frameR ((.x24 ↦ᵣ v24)) (by pcf) hwi
  have hwiW : cpsTripleWithin (1 + 15 + 1 + 2) AtWalkInitAuth AfterWalkInitAuthSave
      teerLinkedCount
      ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x24 ↦ᵣ v24) **
        teerWalkInitAuthPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old
          t5Old t6Old bs listOff)
      ((.x1 ↦ᵣ LinkWalkInitAuth) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
        (.x24 ↦ᵣ v24) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
      xperm_hyp hq) hwiF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hprepW hwiW
  have hli := teerAuthLoopLiS8 v24
  have hliF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkWalkInitAuth) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
      (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) (by pcf) hli
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hliF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

#print axioms teerAuthLoopStartShort

/-- AuthLoopStart prest core (value-carrying x5/x10; temps lifted separately). -/
def teerAuthLoopStartBodyCore
    (listBase : Word) (_listLen : Word) (bs : List (BitVec 8)) (_listOff : Nat)
    (old1 v10 t0Old v21 v22 v24 : Word) : Assertion :=
  (.x1 ↦ᵣ old1) ** (.x10 ↦ᵣ v10) **
    (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x24 ↦ᵣ v24) **
    (.x5 ↦ᵣ t0Old) **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs

/-- AuthLoopStart post with all temps `regOwn`. -/
def teerAuthLoopStartBodyPost
    (listBase listLen : Word) (bs : List (BitVec 8)) (listOff : Nat) : Assertion :=
  let cur := (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12)
  let endW := (listBase + BitVec.ofNat 64 listOff) + listLen
  (.x1 ↦ᵣ LinkWalkInitAuth) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
    (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
    (.x24 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs

set_option maxRecDepth 8000 in
/-- Lift AuthLoopStartShort temps to `regOwn` (post also all-temps `regOwn`). -/
theorem teerAuthLoopStartShort_ownTemps
    (listBase listLen t0Old v10 : Word)
    (bs : List (BitVec 8)) (listOff : Nat)
    (old1 v21 v22 v24 : Word)
    (hs5 : v21 = listBase + BitVec.ofNat 64 listOff)
    (hs6 : v22 = listLen)
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
    cpsTripleWithin nAuthLoopStartShort AfterAuthCountLoad AfterAuthLoopLi teerLinkedCount
      (teerAuthLoopStartBodyCore listBase listLen bs listOff old1 v10 t0Old v21 v22 v24 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (teerAuthLoopStartBodyPost listBase listLen bs listOff) := by
  have hcore (a2 t1 t2 t3 t4 t5 t6 v11 : Word) :
      cpsTripleWithin nAuthLoopStartShort AfterAuthCountLoad AfterAuthLoopLi
        teerLinkedCount
        (teerAuthLoopStartBodyCore listBase listLen bs listOff old1 v10 t0Old
          v21 v22 v24 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ a2) **
          (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) ** (.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6))
        (teerAuthLoopStartBodyPost listBase listLen bs listOff) := by
    have h0 := teerAuthLoopStartShort listBase listLen a2 t0Old t1 t2 t3 t4 t5 t6
      bs listOff old1 v10 v11 v21 v22 v24 hs5 hs6 hsalign hoff hover hvalid hlen
      h_ge h_hi h_exact
    refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) h0
    · unfold teerAuthLoopStartBodyCore at hp
      xperm_hyp hp
    · unfold teerAuthLoopStartBodyPost
      have hq1 :
          ((.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6) **
            ((.x1 ↦ᵣ LinkWalkInitAuth) **
              (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + signExtend12 1)) **
              (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + listLen)) **
              (.x12 ↦ᵣ (0 : Word)) **
              (.x21 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + signExtend12 1)) **
              (.x22 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + listLen)) **
              (.x24 ↦ᵣ (0 : Word)) **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
              regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) s := by
        xperm_hyp hq
      have hq2 :=
        (sepConj_mono (regIs_implies_regOwn .x30)
          (sepConj_mono (regIs_implies_regOwn .x31) (fun _ h => h))) s hq1
      xperm_hyp hq2
  have h3031 (a2 t1 t2 t3 t4 v11 : Word) :
      cpsTripleWithin nAuthLoopStartShort AfterAuthCountLoad AfterAuthLoopLi
        teerLinkedCount
        (teerAuthLoopStartBodyCore listBase listLen bs listOff old1 v10 t0Old
          v21 v22 v24 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ a2) **
          (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) **
          regOwn .x30 ** regOwn .x31)
        (teerAuthLoopStartBodyPost listBase listLen bs listOff) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x30) (r2 := .x31)
      (P := teerAuthLoopStartBodyCore listBase listLen bs listOff old1 v10 t0Old
        v21 v22 v24 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ a2) **
        (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4))
      (fun t5 t6 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (hcore a2 t1 t2 t3 t4 t5 t6 v11))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  have h2829 (a2 t1 t2 v11 : Word) :
      cpsTripleWithin nAuthLoopStartShort AfterAuthCountLoad AfterAuthLoopLi
        teerLinkedCount
        (teerAuthLoopStartBodyCore listBase listLen bs listOff old1 v10 t0Old
          v21 v22 v24 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ a2) **
          (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        (teerAuthLoopStartBodyPost listBase listLen bs listOff) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x28) (r2 := .x29)
      (P := teerAuthLoopStartBodyCore listBase listLen bs listOff old1 v10 t0Old
        v21 v22 v24 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ a2) **
        (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        regOwn .x30 ** regOwn .x31)
      (fun t3 t4 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h3031 a2 t1 t2 t3 t4 v11))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  have h67 (a2 v11 : Word) :
      cpsTripleWithin nAuthLoopStartShort AfterAuthCountLoad AfterAuthLoopLi
        teerLinkedCount
        (teerAuthLoopStartBodyCore listBase listLen bs listOff old1 v10 t0Old
          v21 v22 v24 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ a2) **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        (teerAuthLoopStartBodyPost listBase listLen bs listOff) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x6) (r2 := .x7)
      (P := teerAuthLoopStartBodyCore listBase listLen bs listOff old1 v10 t0Old
        v21 v22 v24 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ a2) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun t1 t2 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h2829 a2 t1 t2 v11))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  have h1112 :
      cpsTripleWithin nAuthLoopStartShort AfterAuthCountLoad AfterAuthLoopLi
        teerLinkedCount
        (teerAuthLoopStartBodyCore listBase listLen bs listOff old1 v10 t0Old
          v21 v22 v24 **
          regOwn .x11 ** regOwn .x12 **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        (teerAuthLoopStartBodyPost listBase listLen bs listOff) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x11) (r2 := .x12)
      (P := teerAuthLoopStartBodyCore listBase listLen bs listOff old1 v10 t0Old
        v21 v22 v24 **
        regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun v11 a2 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h67 a2 v11))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) h1112

#print axioms teerAuthLoopStartShort_ownTemps

end EvmAsm.Codegen.TxEip7702TeerSpec
