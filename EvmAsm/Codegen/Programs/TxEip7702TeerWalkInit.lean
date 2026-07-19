/-
  Teer first walk_init call + success BNE + cursor save (instr 54–57).
  PC AtWalkInit (E+216) → AfterWalkInitSave (E+232).
  Short-success path (a2=0); ambient regionBase/listOff.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerType4
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

abbrev WI : Word := BitVec.ofNat 64 GuestAddrs.rlp_walk_init

/-- PC after walk_init JAL link (E+220). -/
abbrev LinkWalkInit : Word := E + 220
/-- PC after success BNE not-taken (E+224). -/
abbrev AfterWalkInitOk : Word := E + 224
/-- PC after mv s8,a0; mv s9,a1 (E+232). -/
abbrev AfterWalkInitSave : Word := E + 232

abbrev walkInitJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_init
    (GuestAddrs.tx_eip7702_existing_authority_refund + 216)

abbrev teerWalkInitBneOff : BitVec 13 := (2636 : BitVec 13)

private theorem teer_type_disjoint' : teerCode.Disjoint typeCode := by
  unfold teerCode typeCode E
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [teer_length]; decide
  · rw [type_length']; decide
  · rw [teer_length, type_length']; decide

private theorem teer_type_walkInit_disjoint' :
    (teerCode.union typeCode).Disjoint walkInitCode := by
  apply CodeReq.Disjoint.union_left
  · unfold teerCode walkInitCode E
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [teer_length]; decide
    · rw [rlp_walk_init_prog_length]; decide
    · rw [teer_length, rlp_walk_init_prog_length]; decide
  · unfold typeCode walkInitCode
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [type_length']; decide
    · rw [rlp_walk_init_prog_length]; decide
    · rw [type_length', rlp_walk_init_prog_length]; decide

/-- walkInitCode ⊆ teerLinkedEarly. -/
theorem teerEarly_mono_walkInit :
    ∀ a i, walkInitCode a = some i → teerLinkedEarly a = some i := by
  intro a i hi
  unfold teerLinkedEarly
  have h1 := CodeReq.mono_union_right teer_type_walkInit_disjoint'
    (fun _ _ h => h) a i hi
  exact CodeReq.union_mono_left
    (cr1 := (teerCode.union typeCode).union walkInitCode) (cr2 := walkNextCode) a i h1

theorem walkInitJalOff_resolves :
    AtWalkInit + signExtend21 walkInitJalOff = WI := by
  simp only [AtWalkInit, WI, walkInitJalOff, E]; decide

def teerWalkInitPrest (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (listOff : Nat) : Assertion :=
  (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
    (.x12 ↦ᵣ a2Old) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
    (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs

def teerWalkInitShortPost (listBase listLen : Word) (bs : List (BitVec 8))
    (listOff : Nat) (t5Old t6Old : Word) : Assertion :=
  (.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
    (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
    (.x12 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkInit) **
    bytesRegion listBase bs

theorem teerWalkInitPrest_pcFree
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (listOff : Nat) :
    (teerWalkInitPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      bs listOff).pcFree := by
  unfold teerWalkInitPrest; pcf

set_option maxRecDepth 8000 in
/-- JAL walk_init short-success under teerLinkedEarly (15-step leaf). -/
theorem teerWalkInitCall_short
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
    cpsTripleWithin (1 + 15) AtWalkInit LinkWalkInit teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkInitPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      (teerWalkInitShortPost listBase listLen bs listOff t5Old t6Old) := by
  have hret : (LinkWalkInit &&& ~~~(1 : Word)) = LinkWalkInit := by
    simp only [LinkWalkInit, E]; decide
  have hleaf0 := rlp_walk_init_short_spec_within WI listBase LinkWalkInit listLen
    a2Old t0Old t1Old t2Old t3Old t4Old bs listOff
    hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  rw [hret] at hleaf0
  have hleafF := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
    (by
      apply pcFree_sepConj
      · exact pcFree_regIs
      · exact pcFree_regIs) hleaf0
  have hleafP : cpsTripleWithin 15 WI LinkWalkInit walkInitCode
      ((.x1 ↦ᵣ LinkWalkInit) **
        teerWalkInitPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      (teerWalkInitShortPost listBase listLen bs listOff t5Old t6Old) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkInitPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkInitShortPost] at hq ⊢
      xperm_hyp hq) hleafF
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkInit hleafP
  have hcallee' : cpsTripleWithin 15 WI LinkWalkInit teerLinkedEarly
      ((.x1 ↦ᵣ LinkWalkInit) **
        teerWalkInitPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInit) **
        ((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
          (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
          (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [teerWalkInitShortPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec AtWalkInit WI old1 walkInitJalOff 15
    walkInitJalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AtWalkInit teerProg 54
        (.JAL .x1 walkInitJalOff) (by simp only [AtWalkInit]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkInitPrest_pcFree listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      bs listOff)
    hcallee'
  rw [show (AtWalkInit + 4 : Word) = LinkWalkInit from by
    simp only [AtWalkInit, LinkWalkInit]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkInitShortPost]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- BNE a2,x0 fail: not-taken when a2=0 → AfterWalkInitOk. -/
theorem teerWalkInitBneOk :
    cpsTripleWithin 1 LinkWalkInit AfterWalkInitOk teerLinkedEarly
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x12 .x0 teerWalkInitBneOff
    (0 : Word) (0 : Word) LinkWalkInit
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkWalkInit teerProg 55
        (.BNE .x12 .x0 teerWalkInitBneOff)
        (by simp only [LinkWalkInit]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkInit + 4 = AfterWalkInitOk := by
    simp only [LinkWalkInit, AfterWalkInitOk]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `mv s8, a0` (instr 56): x24 ← cursor. -/
theorem teerMvS8A0 (cur v24 : Word) :
    cpsTripleWithin 1 AfterWalkInitOk (E + 228) teerLinkedEarly
      ((.x10 ↦ᵣ cur) ** (.x24 ↦ᵣ v24))
      ((.x10 ↦ᵣ cur) ** (.x24 ↦ᵣ cur)) := by
  have h0 := mv_spec_gen_within .x24 .x10 cur v24 AfterWalkInitOk (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkInitOk teerProg 56
        (.MV .x24 .x10) (by simp only [AfterWalkInitOk]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkInitOk + 4 : Word) = E + 228 := by
    simp only [AfterWalkInitOk]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv s9, a1` (instr 57): x25 ← end. -/
theorem teerMvS9A1 (endW v25 : Word) :
    cpsTripleWithin 1 (E + 228) AfterWalkInitSave teerLinkedEarly
      ((.x11 ↦ᵣ endW) ** (.x25 ↦ᵣ v25))
      ((.x11 ↦ᵣ endW) ** (.x25 ↦ᵣ endW)) := by
  have h0 := mv_spec_gen_within .x25 .x11 endW v25 (E + 228) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 228) teerProg 57
        (.MV .x25 .x11) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 228 : Word) + 4 = AfterWalkInitSave := by
    simp only [AfterWalkInitSave]; bv_omega
  rw [hpc] at e0
  exact e0

set_option maxRecDepth 8000 in
/-- Save cursors: AfterWalkInitOk → AfterWalkInitSave. -/
theorem teerWalkInitSaveCursors (cur endW v24 v25 : Word) :
    cpsTripleWithin 2 AfterWalkInitOk AfterWalkInitSave teerLinkedEarly
      ((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25))
      ((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) ** (.x24 ↦ᵣ cur) ** (.x25 ↦ᵣ endW)) := by
  have h0 := teerMvS8A0 cur v24
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endW) ** (.x25 ↦ᵣ v25)) (by pcf) h0
  have h1 := teerMvS9A1 endW v25
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ cur) ** (.x24 ↦ᵣ cur)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- Short walk_init call + BNE ok + save s8/s9: AtWalkInit → AfterWalkInitSave. -/
theorem teerWalkInitShortSuccess
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (listOff : Nat) (old1 v24 v25 : Word)
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
    cpsTripleWithin (1 + 15 + 1 + 2) AtWalkInit AfterWalkInitSave teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        teerWalkInitPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInit) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ cur) ** (.x25 ↦ᵣ endW) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
  intro cur endW
  have hcall := teerWalkInitCall_short listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old
    t5Old t6Old bs listOff old1 hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  have hcallF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25)) (by pcf) hcall
  have hbne := teerWalkInitBneOk
  have hbneF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkWalkInit) **
      (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
      (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      bytesRegion listBase bs) (by pcf) hbne
  have hcall' : cpsTripleWithin (1 + 15) AtWalkInit LinkWalkInit teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        teerWalkInitPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInit) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkInitShortPost, cur, endW] at hq ⊢
      xperm_hyp hq) hcallF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcall' hbneF
  have hsave := teerWalkInitSaveCursors cur endW v24 v25
  have hsaveF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkWalkInit) ** (.x12 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) (by pcf) hsave
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hsaveF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

#print axioms teerWalkInitCall_short
#print axioms teerWalkInitBneOk
#print axioms teerWalkInitSaveCursors
#print axioms teerWalkInitShortSuccess

end EvmAsm.Codegen.TxEip7702TeerSpec
