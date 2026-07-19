/-
  Teer second walk_init (auth list): reload inner_off + setup s5/s6 +
  short Call+BNE+save s5/s6. PC AfterValueNonzero (E+412) → AfterWalkInit2Save (E+460).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerValueNonzero
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkInit
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

/-- PC after second walk_init JAL link (E+444). -/
abbrev LinkWalkInit2 : Word := E + 444
/-- PC after success BNE not-taken (E+448). -/
abbrev AfterWalkInit2Ok : Word := E + 448
/-- PC after mv s5,a0; mv s6,a1 (E+456). -/
abbrev AfterWalkInit2Save : Word := E + 456
/-- PC of second walk_init JAL (E+440). -/
abbrev AtWalkInit2 : Word := E + 440

abbrev walkInit2JalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_init
    (GuestAddrs.tx_eip7702_existing_authority_refund + 440)

abbrev teerWalkInit2BneOff : BitVec 13 := (2412 : BitVec 13)

theorem walkInit2JalOff_resolves :
    AtWalkInit2 + signExtend21 walkInit2JalOff = WI := by
  simp only [AtWalkInit2, WI, walkInit2JalOff, E]; decide

/-- `la x5, teer_inner_off` at AfterValueNonzero → E+420. -/
theorem teerLaInner2 (v : Word) :
    cpsTripleWithin 2 AfterValueNonzero (E + 420) teerLinkedEarly
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ InnerOffAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterValueNonzero
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_inner_off
        (GuestAddrs.tx_eip7702_existing_authority_refund + 412)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterValueNonzero teerProg 103
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_inner_off
          (GuestAddrs.tx_eip7702_existing_authority_refund + 412)))
        (by simp only [AfterValueNonzero]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 416)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_inner_off
        (GuestAddrs.tx_eip7702_existing_authority_refund + 412)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 416) teerProg 104
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_inner_off
          (GuestAddrs.tx_eip7702_existing_authority_refund + 412)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterValueNonzero InnerOffAddr
    (by decide) (by decide) hau had
  rw [show (AfterValueNonzero : Word) + 8 = E + 420 from by
    simp only [AfterValueNonzero]; bv_omega] at h
  exact h

private theorem se12_zero2 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- `ld x6, 0(x5)` teer_inner_off (instr 105). -/
theorem teerLdInner2 (innerVal v6 : Word) :
    cpsTripleWithin 1 (E + 420) (E + 424) teerLinkedEarly
      ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ v6) ** (InnerOffAddr ↦ₘ innerVal))
      ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) **
        (InnerOffAddr ↦ₘ innerVal)) := by
  have h0 := ld_spec_gen_within .x6 .x5 InnerOffAddr v6 innerVal
    (0 : BitVec 12) (E + 420) (by decide)
  rw [show InnerOffAddr + signExtend12 (0 : BitVec 12) = InnerOffAddr from by
    rw [se12_zero2]; exact BitVec.add_zero InnerOffAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 420) teerProg 105
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 420 : Word) + 4 = E + 424 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- `add s5, s0, t1` (instr 106): x21 = loadPtr + inner. -/
theorem teerAddS5_2 (loadPtr innerVal v21 : Word) :
    cpsTripleWithin 1 (E + 424) (E + 428) teerLinkedEarly
      ((.x8 ↦ᵣ loadPtr) ** (.x6 ↦ᵣ innerVal) ** (.x21 ↦ᵣ v21))
      ((.x8 ↦ᵣ loadPtr) ** (.x6 ↦ᵣ innerVal) **
        (.x21 ↦ᵣ loadPtr + innerVal)) := by
  have h0 := add_spec_gen_within .x21 .x8 .x6 loadPtr innerVal v21
    (E + 424) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 424) teerProg 106
        (.ADD .x21 .x8 .x6) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 424 : Word) + 4 = E + 428 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- `sub s6, s1, t1` (instr 107): x22 = lenW - inner. -/
theorem teerSubS6_2 (lenW innerVal v22 : Word) :
    cpsTripleWithin 1 (E + 428) (E + 432) teerLinkedEarly
      ((.x9 ↦ᵣ lenW) ** (.x6 ↦ᵣ innerVal) ** (.x22 ↦ᵣ v22))
      ((.x9 ↦ᵣ lenW) ** (.x6 ↦ᵣ innerVal) **
        (.x22 ↦ᵣ lenW - innerVal)) := by
  have h0 := sub_spec_gen_within .x22 .x9 .x6 lenW innerVal v22
    (E + 428) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 428) teerProg 107
        (.SUB .x22 .x9 .x6) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 428 : Word) + 4 = E + 432 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv a0, s5` (instr 108). -/
theorem teerMvA0S5_2 (s5 v10 : Word) :
    cpsTripleWithin 1 (E + 432) (E + 436) teerLinkedEarly
      ((.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ v10))
      ((.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ s5)) := by
  have h0 := mv_spec_gen_within .x10 .x21 s5 v10 (E + 432) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 432) teerProg 108
        (.MV .x10 .x21) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 432 : Word) + 4 = E + 436 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv a1, s6` (instr 109). -/
theorem teerMvA1S6_2 (s6 v11 : Word) :
    cpsTripleWithin 1 (E + 436) AtWalkInit2 teerLinkedEarly
      ((.x22 ↦ᵣ s6) ** (.x11 ↦ᵣ v11))
      ((.x22 ↦ᵣ s6) ** (.x11 ↦ᵣ s6)) := by
  have h0 := mv_spec_gen_within .x11 .x22 s6 v11 (E + 436) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 436) teerProg 109
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 436 : Word) + 4 = AtWalkInit2 := by
    simp only [AtWalkInit2]; bv_omega
  rw [hpc] at e0
  exact e0

set_option maxRecDepth 8000 in
/-- Inner reload + s5/s6 + a0/a1: AfterValueNonzero → AtWalkInit2. -/
theorem teerInnerSetup2
    (loadPtr lenW innerVal v5 v6 v10 v11 v21 v22 : Word) :
    cpsTripleWithin 7 AfterValueNonzero AtWalkInit2 teerLinkedEarly
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        (InnerOffAddr ↦ₘ innerVal))
      ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ loadPtr + innerVal) ** (.x11 ↦ᵣ lenW - innerVal) **
        (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
        (InnerOffAddr ↦ₘ innerVal)) := by
  have hla := teerLaInner2 v5
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      (InnerOffAddr ↦ₘ innerVal)) (by pcf) hla
  have hld := teerLdInner2 innerVal v6
  have hldF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22))
    (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hadd := teerAddS5_2 loadPtr innerVal v21
  have haddF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ InnerOffAddr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x22 ↦ᵣ v22) **
      (InnerOffAddr ↦ₘ innerVal)) (by pcf) hadd
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 haddF
  have hsub := teerSubS6_2 lenW innerVal v22
  have hsubF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ InnerOffAddr) ** (.x8 ↦ᵣ loadPtr) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x21 ↦ᵣ loadPtr + innerVal) ** (InnerOffAddr ↦ₘ innerVal)) (by pcf) hsub
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hsubF
  have hm0 := teerMvA0S5_2 (loadPtr + innerVal) v10
  have hm0F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) **
      (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x11 ↦ᵣ v11) **
      (.x22 ↦ᵣ lenW - innerVal) ** (InnerOffAddr ↦ₘ innerVal)) (by pcf) hm0
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 hm0F
  have hm1 := teerMvA1S6_2 (lenW - innerVal) v11
  have hm1F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) **
      (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ loadPtr + innerVal) ** (.x21 ↦ᵣ loadPtr + innerVal) **
      (InnerOffAddr ↦ₘ innerVal)) (by pcf) hm1
  have c45 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c34 hm1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c45

/-- Prest for second walk_init (a0/a1 already set to listBase+listOff / listLen). -/
def teerWalkInit2Prest (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (listOff : Nat) : Assertion :=
  teerWalkInitPrest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    bs listOff

def teerWalkInit2ShortPost (listBase listLen : Word) (bs : List (BitVec 8))
    (listOff : Nat) (t5Old t6Old : Word) : Assertion :=
  (.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
    (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
    (.x12 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkInit2) **
    bytesRegion listBase bs

set_option maxRecDepth 8000 in
/-- JAL second walk_init short-success under teerLinkedEarly. -/
theorem teerWalkInit2Call_short
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
    cpsTripleWithin (1 + 15) AtWalkInit2 LinkWalkInit2 teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkInit2Prest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      (teerWalkInit2ShortPost listBase listLen bs listOff t5Old t6Old) := by
  have hret : (LinkWalkInit2 &&& ~~~(1 : Word)) = LinkWalkInit2 := by
    simp only [LinkWalkInit2, E]; decide
  have hleaf0 := rlp_walk_init_short_spec_within WI listBase LinkWalkInit2 listLen
    a2Old t0Old t1Old t2Old t3Old t4Old bs listOff
    hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  rw [hret] at hleaf0
  have hleafF := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
    (by
      apply pcFree_sepConj
      · exact pcFree_regIs
      · exact pcFree_regIs) hleaf0
  have hleafP : cpsTripleWithin 15 WI LinkWalkInit2 walkInitCode
      ((.x1 ↦ᵣ LinkWalkInit2) **
        teerWalkInit2Prest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      (teerWalkInit2ShortPost listBase listLen bs listOff t5Old t6Old) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkInit2Prest, teerWalkInitPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkInit2ShortPost] at hq ⊢
      xperm_hyp hq) hleafF
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkInit hleafP
  have hcallee' : cpsTripleWithin 15 WI LinkWalkInit2 teerLinkedEarly
      ((.x1 ↦ᵣ LinkWalkInit2) **
        teerWalkInit2Prest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInit2) **
        ((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
          (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
          (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [teerWalkInit2ShortPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec AtWalkInit2 WI old1 walkInit2JalOff 15
    walkInit2JalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AtWalkInit2 teerProg 110
        (.JAL .x1 walkInit2JalOff) (by simp only [AtWalkInit2]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (by
      unfold teerWalkInit2Prest
      exact teerWalkInitPrest_pcFree listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old
        t5Old t6Old bs listOff)
    hcallee'
  rw [show (AtWalkInit2 + 4 : Word) = LinkWalkInit2 from by
    simp only [AtWalkInit2, LinkWalkInit2]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkInit2ShortPost]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- BNE a2,x0 fail: not-taken when a2=0 → AfterWalkInit2Ok. -/
theorem teerWalkInit2BneOk :
    cpsTripleWithin 1 LinkWalkInit2 AfterWalkInit2Ok teerLinkedEarly
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x12 .x0 teerWalkInit2BneOff
    (0 : Word) (0 : Word) LinkWalkInit2
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkWalkInit2 teerProg 111
        (.BNE .x12 .x0 teerWalkInit2BneOff)
        (by simp only [LinkWalkInit2]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkInit2 + 4 = AfterWalkInit2Ok := by
    simp only [LinkWalkInit2, AfterWalkInit2Ok]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `mv s5, a0` (instr 112): x21 ← cursor. -/
theorem teerMvS5A0_2 (cur v21 : Word) :
    cpsTripleWithin 1 AfterWalkInit2Ok (E + 452) teerLinkedEarly
      ((.x10 ↦ᵣ cur) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ cur) ** (.x21 ↦ᵣ cur)) := by
  have h0 := mv_spec_gen_within .x21 .x10 cur v21 AfterWalkInit2Ok (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkInit2Ok teerProg 112
        (.MV .x21 .x10) (by simp only [AfterWalkInit2Ok]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterWalkInit2Ok + 4 : Word) = E + 452 := by
    simp only [AfterWalkInit2Ok]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv s6, a1` (instr 113): x22 ← end. -/
theorem teerMvS6A1_2 (endW v22 : Word) :
    cpsTripleWithin 1 (E + 452) AfterWalkInit2Save teerLinkedEarly
      ((.x11 ↦ᵣ endW) ** (.x22 ↦ᵣ v22))
      ((.x11 ↦ᵣ endW) ** (.x22 ↦ᵣ endW)) := by
  have h0 := mv_spec_gen_within .x22 .x11 endW v22 (E + 452) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 452) teerProg 113
        (.MV .x22 .x11) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 452 : Word) + 4 = AfterWalkInit2Save := by
    simp only [AfterWalkInit2Save]; bv_omega
  rw [hpc] at e0
  exact e0

set_option maxRecDepth 8000 in
/-- Save auth cursors s5/s6: AfterWalkInit2Ok → AfterWalkInit2Save. -/
theorem teerWalkInit2SaveCursors (cur endW v21 v22 : Word) :
    cpsTripleWithin 2 AfterWalkInit2Ok AfterWalkInit2Save teerLinkedEarly
      ((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW)) := by
  have h0 := teerMvS5A0_2 cur v21
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endW) ** (.x22 ↦ᵣ v22)) (by pcf) h0
  have h1 := teerMvS6A1_2 endW v22
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ cur) ** (.x21 ↦ᵣ cur)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- Short walk_init2 call + BNE ok + save s5/s6: AtWalkInit2 → AfterWalkInit2Save. -/
theorem teerWalkInit2ShortSuccess
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
    cpsTripleWithin (1 + 15 + 1 + 2) AtWalkInit2 AfterWalkInit2Save teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        teerWalkInit2Prest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
  intro cur endW
  have hcall := teerWalkInit2Call_short listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old
    t5Old t6Old bs listOff old1 hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  have hcallF := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22)) (by pcf) hcall
  have hbne := teerWalkInit2BneOk
  have hbneF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkWalkInit2) **
      (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
      (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      bytesRegion listBase bs) (by pcf) hbne
  have hcall' : cpsTripleWithin (1 + 15) AtWalkInit2 LinkWalkInit2 teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        teerWalkInit2Prest listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          bs listOff)
      ((.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkInit2ShortPost, cur, endW] at hq ⊢
      xperm_hyp hq) hcallF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcall' hbneF
  have hsave := teerWalkInit2SaveCursors cur endW v21 v22
  have hsaveF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkWalkInit2) ** (.x12 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) (by pcf) hsave
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hsaveF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

#print axioms teerInnerSetup2
#print axioms teerWalkInit2Call_short
#print axioms teerWalkInit2BneOk
#print axioms teerWalkInit2SaveCursors
#print axioms teerWalkInit2ShortSuccess

end EvmAsm.Codegen.TxEip7702TeerSpec
