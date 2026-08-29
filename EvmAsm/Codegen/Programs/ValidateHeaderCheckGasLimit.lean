/-
  EvmAsm.Codegen.Programs.ValidateHeaderCheckGasLimit

  Caller composition for `check_gas_limit` (12346 item 5).

  The call at `validate_header + 108` is followed by a BNE at `+112`.
  A nonzero check-gas status reaches the shared status-4 tail at `+284`;
  zero falls through to the base-fee setup at `+116`.  This file proves
  those two routes without assuming any particular base-fee contract.

  The fall-through post carries the check-gas result and its SpecRef
  correspondence into the continuation at `H + 116`, where the base-fee
  checks begin.  The shared status-4 post also carries the same correspondence
  together with `cglStatus ≠ 0`; those facts independently attribute that exit
  to the gas-limit check, so this composition needs no base-fee contract.
-/

import EvmAsm.Codegen.Programs.CheckGasLimitBridge
import EvmAsm.Codegen.Programs.ValidateHeaderCompose
import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.ValidateHeaderCheckGasLimit

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.CheckGasLimitSAsm
open EvmAsm.Codegen.ValidateHeaderCompose
open EvmAsm.Codegen.ValidateHeaderCorrespondence

abbrev H : Word := EvmAsm.Codegen.ValidateHeaderCorrespondence.H
abbrev A : Word := H + 108
abbrev Ret : Word := H + 112
abbrev Callee : Word := (GuestAddrs.check_gas_limit : Word)

/-! ## Facts available at the continuation -/

/-- The check-gas result available to the continuation.  It is intentionally a
    pure fact: later checks may use it without inheriting the caller's scratch
    registers. -/
def checkGasLimitAccepted (nl pl : Word) : Prop :=
  cglStatus nl pl = 0 ∧
    EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true

theorem checkGasLimitAccepted_of_bridge
    (nl pl : Word)
    (hzero : cglStatus nl pl = 0)
    (hbridge : cglStatus nl pl = 0 ↔
      EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true) :
    checkGasLimitAccepted nl pl := by
  exact ⟨hzero, hbridge.mp hzero⟩

/-! ## Caller frame at the check-gas call -/

/-- Caller-owned state other than `a0`, `a1`, and the link register.  The
    three scratch registers are kept outside this frame because the callee's
    own pre/post owns them. -/
def callerFrame
    (spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
  (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
  (spC ↦ₘ raSlot) ** ((spC + BitVec.ofNat 64 8) ↦ₘ cs0) **
  ((spC + BitVec.ofNat 64 16) ↦ₘ cs1) **
  ((spC + BitVec.ofNat 64 24) ↦ₘ cs2) **
  ((spC + BitVec.ofNat 64 32) ↦ₘ cs3) **
  ((spC + BitVec.ofNat 64 40) ↦ₘ cs4) **
  ((spC + BitVec.ofNat 64 48) ↦ₘ cs5) ** F

theorem callerFrame_pcFree
    (spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (F : Assertion) (hF : F.pcFree) :
    (callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F).pcFree := by
  unfold callerFrame
  pcf
  exact hF

/-! ## Linked call -/

theorem checkGasLimit_jal_mem :
    ∀ a i, CodeReq.singleton A
      (.JAL .x1 (jalOff GuestAddrs.check_gas_limit
        (GuestAddrs.validate_header + 108))) a = some i → callerCode a = some i := by
  exact CodeReq.ofProg_mem_at
    (GuestAddrs.validate_header : Word) A EvmAsm.Codegen.validateHeader_prog 27 _
    (by bv_omega) (by rw [validateHeader_length]; decide) rfl
    (by rw [validateHeader_length]; decide)

theorem checkGasLimit_target :
    A + signExtend21 (jalOff GuestAddrs.check_gas_limit
      (GuestAddrs.validate_header + 108)) = Callee := by
  change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 108 + _ =
    BitVec.ofNat 64 GuestAddrs.check_gas_limit
  exact jalOff_correct_add GuestAddrs.check_gas_limit
    GuestAddrs.validate_header 108 (by decide) (by decide) (by decide) (by decide)

theorem checkGasLimit_branch_mem :
    ∀ a i, CodeReq.singleton Ret (.BNE .x10 .x0 (172 : BitVec 13)) a = some i →
      callerCode a = some i := by
  exact CodeReq.ofProg_mem_at
    (GuestAddrs.validate_header : Word) Ret EvmAsm.Codegen.validateHeader_prog 28 _
    (by bv_omega) (by rw [validateHeader_length]; decide) rfl
    (by rw [validateHeader_length]; decide)

set_option maxRecDepth 8000 in
theorem check_gas_limit_branch_spec_within
    (spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (nl pl : Word) (F : Assertion) (hF : F.pcFree) :
    cpsBranchWithin 1 Ret callerCode
      ((.x10 ↦ᵣ cglStatus nl pl) ** (.x11 ↦ᵣ pl) ** (.x1 ↦ᵣ Ret) **
        regOwns [.x5, .x6, .x7] ** (.x0 ↦ᵣ (0 : Word)) **
        callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F)
      (H + 284)
        (((.x10 ↦ᵣ cglStatus nl pl) ** (.x11 ↦ᵣ pl) ** (.x1 ↦ᵣ Ret) **
          regOwns [.x5, .x6, .x7] ** (.x0 ↦ᵣ (0 : Word)) **
          callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F) **
          ⌜cglStatus nl pl ≠ 0⌝)
      (H + 116)
        (((.x10 ↦ᵣ cglStatus nl pl) ** (.x11 ↦ᵣ pl) ** (.x1 ↦ᵣ Ret) **
          regOwns [.x5, .x6, .x7] ** (.x0 ↦ᵣ (0 : Word)) **
          callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F) **
          ⌜cglStatus nl pl = 0⌝) := by
  have hraw := bne_spec_gen_within .x10 .x0 (172 : BitVec 13)
    (cglStatus nl pl) (0 : Word) Ret
  rw [show Ret + signExtend13 (172 : BitVec 13) = H + 284 by decide,
    show Ret + 4 = H + 116 by decide] at hraw
  have hbranch := cpsBranchWithin_extend_code checkGasLimit_branch_mem hraw
  have hframe :
      ((.x11 ↦ᵣ pl) ** (.x1 ↦ᵣ Ret) ** regOwns [.x5, .x6, .x7] **
        callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F).pcFree := by
    pcf
    exact hF
  have hframed := cpsBranchWithin_frameR
    ((.x11 ↦ᵣ pl) ** (.x1 ↦ᵣ Ret) ** regOwns [.x5, .x6, .x7] **
      callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F)
    hframe hbranch
  simp only [regOwns_cons, regOwns_nil, sepConj_emp_right'] at hframed ⊢
  exact cpsBranchWithin_weaken
    (fun _ hp => by unfold callerFrame at hp ⊢; xperm_hyp hp)
    (fun _ hq => by unfold callerFrame at hq ⊢; xperm_hyp hq)
    (fun _ hq => by unfold callerFrame at hq ⊢; xperm_hyp hq)
    hframed

set_option maxRecDepth 8000 in
theorem validate_header_check_gas_limit_call_spec_within
    {cr calleeCode : CodeReq}
    (spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (nl pl oldRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hcallerDisj : callerCode.Disjoint calleeCode)
    (hcalleeCode : ∀ a i,
      CodeReq.ofProg Callee checkGasLimit_prog a = some i → calleeCode a = some i)
    (hcode : ∀ a i, (callerCode.union calleeCode) a = some i → cr a = some i) :
    cpsTripleWithin 11 A Ret cr
      ((.x10 ↦ᵣ nl) ** (.x11 ↦ᵣ pl) ** (.x1 ↦ᵣ oldRa) **
        regOwns [.x5, .x6, .x7] **
        (.x0 ↦ᵣ (0 : Word)) **
        callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F)
      (((.x10 ↦ᵣ cglStatus nl pl) ** (.x11 ↦ᵣ pl) ** (.x1 ↦ᵣ Ret) **
        regOwns [.x5, .x6, .x7] **
        (.x0 ↦ᵣ (0 : Word)) **
        callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F) **
        ⌜cglStatus nl pl = 0 ↔
          EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true⌝) := by
  have hret : A + 4 = Ret := by decide
  have hmem : ∀ a i,
      CodeReq.singleton A
        (.JAL .x1 (jalOff GuestAddrs.check_gas_limit
          (GuestAddrs.validate_header + 108))) a = some i →
      (callerCode.union calleeCode) a = some i := by
    intro a i hi
    exact CodeReq.union_mono_left a i (checkGasLimit_jal_mem a i hi)
  have hcalleeU : cpsTripleWithin 10 Callee Ret (callerCode.union calleeCode)
      ((.x1 ↦ᵣ Ret) **
        ((.x10 ↦ᵣ nl) ** (.x11 ↦ᵣ pl) ** regOwns [.x5, .x6, .x7] **
          (.x0 ↦ᵣ (0 : Word)) **
          callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F))
      ((.x1 ↦ᵣ Ret) **
        (((.x10 ↦ᵣ cglStatus nl pl) ** (.x11 ↦ᵣ pl) **
          regOwns [.x5, .x6, .x7] **
          (.x0 ↦ᵣ (0 : Word)) **
          callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F) **
          ⌜cglStatus nl pl = 0 ↔
            EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true⌝)) := by
    have h0 := checkGasLimit_ref_spec nl pl Ret (by decide)
    have h1 := cpsTripleWithin_extend_code hcalleeCode h0
    have h2 := cpsTripleWithin_extend_code
      (CodeReq.mono_union_right hcallerDisj (fun _ _ h => h)) h1
    have h2F := cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) **
        callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F)
      (by pcf; exact hF) h2
    simp only [regOwns_cons, regOwns_nil, sepConj_emp_right'] at h2F ⊢
    exact cpsTripleWithin_weaken
      (fun _ hp => by unfold callerFrame at hp ⊢; xperm_hyp hp)
      (fun _ hq => by unfold callerFrame at hq ⊢; xperm_hyp hq) h2F
  have hP :
      ((.x10 ↦ᵣ nl) ** (.x11 ↦ᵣ pl) ** regOwns [.x5, .x6, .x7] **
        (.x0 ↦ᵣ (0 : Word)) **
        callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F).pcFree := by
    pcf
    exact hF
  rw [← hret] at hcalleeU
  have hcall := callWithin_spec (cr := callerCode.union calleeCode)
    A Callee oldRa
    (jalOff GuestAddrs.check_gas_limit (GuestAddrs.validate_header + 108)) 10
    checkGasLimit_target hmem hP hcalleeU
  have hcallCr := cpsTripleWithin_extend_code hcode hcall
  rw [hret] at hcallCr
  simp only [regOwns_cons, regOwns_nil, sepConj_emp_right'] at hcallCr ⊢
  exact cpsTripleWithin_weaken
    (fun _ hp => by unfold callerFrame at hp ⊢; xperm_hyp hp)
    (fun _ hq => by unfold callerFrame at hq ⊢; xperm_hyp hq)
    hcallCr

/-! ## The two caller exits after the check -/

def checkGasLimitTakenPost
    (spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (nl pl : Word) (F : Assertion) : Assertion :=
  (((.x10 ↦ᵣ cglStatus nl pl) ** (.x11 ↦ᵣ pl) ** (.x1 ↦ᵣ Ret) **
      regOwns [.x5, .x6, .x7] ** (.x0 ↦ᵣ (0 : Word)) **
      callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F) **
    ⌜cglStatus nl pl ≠ 0⌝) **
    ⌜cglStatus nl pl = 0 ↔
      EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true⌝

def checkGasLimitFallPost
    (spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (nl pl : Word) (F : Assertion) : Assertion :=
  (((.x10 ↦ᵣ cglStatus nl pl) ** (.x11 ↦ᵣ pl) ** (.x1 ↦ᵣ Ret) **
      regOwns [.x5, .x6, .x7] ** (.x0 ↦ᵣ (0 : Word)) **
      callerFrame spC raSlot o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F) **
    ⌜cglStatus nl pl = 0⌝) **
    ⌜cglStatus nl pl = 0 ↔
      EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true⌝

def checkGasLimitStatus4Post
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 pl nl : Word)
    (F : Assertion) : Assertion :=
  (((.x10 ↦ᵣ (4 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
      (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
      (spC ↦ₘ raIn) ** ((spC + BitVec.ofNat 64 8) ↦ₘ cs0) **
      ((spC + BitVec.ofNat 64 16) ↦ₘ cs1) **
      ((spC + BitVec.ofNat 64 24) ↦ₘ cs2) **
      ((spC + BitVec.ofNat 64 32) ↦ₘ cs3) **
      ((spC + BitVec.ofNat 64 40) ↦ₘ cs4) **
      ((spC + BitVec.ofNat 64 48) ↦ₘ cs5) **
      (.x11 ↦ᵣ pl) ** regOwns [.x5, .x6, .x7] ** (.x0 ↦ᵣ (0 : Word)) ** F) **
    ⌜cglStatus nl pl ≠ 0⌝) **
    ⌜cglStatus nl pl = 0 ↔
      EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true⌝

set_option maxRecDepth 8000 in
theorem validate_header_check_gas_limit_routes_spec_within
    {cr calleeCode : CodeReq}
    (sp0 spC raIn o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (nl pl oldRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hcallerDisj : callerCode.Disjoint calleeCode)
    (hcalleeCode : ∀ a i,
      CodeReq.ofProg Callee checkGasLimit_prog a = some i → calleeCode a = some i)
    (hcode : ∀ a i, (callerCode.union calleeCode) a = some i → cr a = some i)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsNBranchWithin 23 A cr
      ((.x10 ↦ᵣ nl) ** (.x11 ↦ᵣ pl) ** (.x1 ↦ᵣ oldRa) **
        regOwns [.x5, .x6, .x7] ** (.x0 ↦ᵣ (0 : Word)) **
        callerFrame spC raIn o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F)
      [(raIn, checkGasLimitStatus4Post sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 pl nl F),
       (H + 116, checkGasLimitFallPost spC raIn o8 o9 o18 o19 o20 o21
         cs0 cs1 cs2 cs3 cs4 cs5 nl pl F)] := by
  have hcall := validate_header_check_gas_limit_call_spec_within
    (cr := cr) (calleeCode := calleeCode)
    spC raIn o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 nl pl oldRa F hF
    hcallerDisj hcalleeCode hcode
  have hbranch := check_gas_limit_branch_spec_within
    spC raIn o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 nl pl F hF
  have hiffFree :
      (⌜cglStatus nl pl = 0 ↔
        EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true⌝).pcFree := by
    pcf
  have hbranchF := cpsBranchWithin_frameR
    (⌜cglStatus nl pl = 0 ↔
      EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true⌝)
    hiffFree hbranch
  let G : Assertion :=
    (.x11 ↦ᵣ pl) ** regOwns [.x5, .x6, .x7] ** (.x0 ↦ᵣ (0 : Word)) **
      ⌜cglStatus nl pl ≠ 0⌝ **
      ⌜cglStatus nl pl = 0 ↔
        EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true⌝ ** F
  have hG : G.pcFree := by
    dsimp [G]
    pcf
    exact hF
  have hstatus := status4_tail sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    Ret o8 o9 o18 o19 o20 o21 (cglStatus nl pl) G hG hspC hret
  have hstatus' :
      cpsTripleWithin 11 (H + 284) raIn callerCode
        (checkGasLimitTakenPost spC raIn o8 o9 o18 o19 o20 o21
          cs0 cs1 cs2 cs3 cs4 cs5 nl pl F)
        (checkGasLimitStatus4Post sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 pl nl F) := by
    unfold checkGasLimitTakenPost checkGasLimitStatus4Post
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp [G] at hp ⊢
        simp only [callerFrame, sepConj_emp_right'] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by dsimp [G] at hq ⊢; xperm_hyp hq)
      hstatus
  have hbranch' :
      cpsBranchWithin 1 Ret callerCode
        (((.x10 ↦ᵣ cglStatus nl pl) ** (.x11 ↦ᵣ pl) ** (.x1 ↦ᵣ Ret) **
          regOwns [.x5, .x6, .x7] ** (.x0 ↦ᵣ (0 : Word)) **
          callerFrame spC raIn o8 o9 o18 o19 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F) **
          ⌜cglStatus nl pl = 0 ↔
            EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true⌝)
        (H + 284) (checkGasLimitTakenPost spC raIn o8 o9 o18 o19 o20 o21
          cs0 cs1 cs2 cs3 cs4 cs5 nl pl F)
        (H + 116) (checkGasLimitFallPost spC raIn o8 o9 o18 o19 o20 o21
          cs0 cs1 cs2 cs3 cs4 cs5 nl pl F) := by
    unfold checkGasLimitTakenPost checkGasLimitFallPost
    exact cpsBranchWithin_weaken
      (fun _ hp => by unfold callerFrame at hp ⊢; xperm_hyp hp)
      (fun _ hq => by unfold callerFrame at hq ⊢; xperm_hyp hq)
      (fun _ hq => by unfold callerFrame at hq ⊢; xperm_hyp hq)
      hbranchF
  have hbranchN := cpsBranchWithin_as_cpsNBranchWithin hbranch'
  have hroute := cpsNBranchWithin_extend_head hbranchN hstatus'
  have hcallerCr : ∀ a i, callerCode a = some i → cr a = some i := by
    intro a i hi
    exact hcode a i (CodeReq.union_mono_left a i hi)
  have hrouteCr := cpsNBranchWithin_extend_code hcallerCr hroute
  exact cpsTripleWithin_seq_cpsNBranchWithin_perm_same_cr
    (fun _ hp => by unfold callerFrame at hp ⊢; xperm_hyp hp)
    hcall hrouteCr

end EvmAsm.Codegen.ValidateHeaderCheckGasLimit
