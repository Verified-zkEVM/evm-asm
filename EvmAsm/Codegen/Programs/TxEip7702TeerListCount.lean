/-
  Teer: rlp_list_count_items call + BNE success + LD s7 ← teer_auth_count.
  AtListCount (E+676) → AfterAuthCountLoad (E+696).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthCount
import EvmAsm.Codegen.Programs.RlpListCountItemsFlatSAsm
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpListCountItemsSAsm

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
      | exact pcFree_stackFree _ _
      | exact bytesRegion_pcFree _ _)

abbrev AfterAuthCountLoad : Word := E + 696

/-- Step bound for list_count body (matches flat_spec). -/
def nListCountSteps (listLen : Nat) : Nat :=
  8 + (85 + (93 * (listLen + 1) + 3) + 7)

/-- Callee pre without ra (callWithin owns x1). Needs nested `stackFree spC 6`. -/
def teerListCountCalleeP (spC listBase listLenW outPtr oldCount s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** stackFree spC 6 **
    (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) **
    entryRest listBase listLenW outPtr oldCount bytes

theorem teerListCountCalleeP_pcFree
    (spC listBase listLenW outPtr oldCount s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8)) :
    (teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
      bytes).pcFree := by
  unfold teerListCountCalleeP entryRest; pcf

/-- Flat post with ra peeled (callWithin shape). -/
def teerListCountCalleeQ (spC listBase outPtr s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ status result v11 v12 : Word,
    ((((.x2 ↦ᵣ spC) **
        ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
        stackFree spC 6) **
      ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
       regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (outPtr ↦ₘ result))) **
     ⌜Result bytes listBase listLen status result⌝) h

/-- Peel `ra` out of `flatResult` for `callWithin_spec`. -/
theorem flatResult_to_teerListCountCalleeQ
    (spC listBase outPtr : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) (h : PartialState) :
    flatResult spC listBase outPtr saved bytes listLen h →
      ((.x1 ↦ᵣ saved.ra) **
        teerListCountCalleeQ spC listBase outPtr saved.s0 saved.s1 saved.s2
          saved.s3 bytes listLen) h := by
  intro hp
  unfold flatResult at hp
  obtain ⟨status, result, v11, v12, hcore⟩ := hp
  unfold teerListCountCalleeQ
  have hintro4 : ∀ {A : Assertion}
      {B : Word → Word → Word → Word → Assertion},
      (∃ status result v11 v12, (A ** B status result v11 v12) h) →
      (A ** (fun h' => ∃ status result v11 v12,
        B status result v11 v12 h')) h := by
    intro A B hx
    obtain ⟨status, result, v11, v12, hx⟩ := hx
    rcases hx with ⟨h1, h2, hd, hu, hA, hB⟩
    exact ⟨h1, h2, hd, hu, hA, ⟨status, result, v11, v12, hB⟩⟩
  refine hintro4 ⟨status, result, v11, v12, ?_⟩
  rw [regsAt_countFrame] at hcore
  xperm_hyp hcore

set_option maxRecDepth 8000 in
/-- JAL list_count under teerLinkedCount (flat contract). -/
theorem teerListCountCall
    (spC newSp listBase listLenW outPtr oldCount s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat) (old1 : Word)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spC + signExtend12 (-48 : BitVec 12))
    (hret : (LinkListCount &&& ~~~(1 : Word)) = LinkListCount) :
    cpsTripleWithin (1 + nListCountSteps listLen) AtListCount LinkListCount
      teerLinkedCount
      ((.x1 ↦ᵣ old1) **
        teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
          bytes)
      ((.x1 ↦ᵣ LinkListCount) **
        teerListCountCalleeQ spC listBase outPtr s0 s1 s2 s3 bytes listLen) := by
  let saved : Saved :=
    { ra := LinkListCount, s0 := s0, s1 := s1, s2 := s2, s3 := s3 }
  have hleaf0 := rlpListCountItems_flat_spec_within
    spC newSp listBase listLenW outPtr oldCount saved bytes listLen
    hlistLenW hsalign hslack hover hvalid hnewSp hret
  have hleaf := cpsTripleWithin_extend_code teerCount_mono_count
    (by simpa [nListCountSteps, listCountCode, code, B, LC, saved] using hleaf0)
  have hleafP : cpsTripleWithin (nListCountSteps listLen) LC LinkListCount
      teerLinkedCount
      ((.x1 ↦ᵣ LinkListCount) **
        teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
          bytes)
      (flatResult spC listBase outPtr saved bytes listLen) := by
    refine cpsTripleWithin_weaken
      (P := ((.x2 ↦ᵣ spC) ** regsAt countFrame (savedVals saved) **
        stackFree spC 6 **
        entryRest listBase listLenW outPtr oldCount bytes))
      (P' := ((.x1 ↦ᵣ LinkListCount) **
        teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
          bytes))
      (Q := flatResult spC listBase outPtr saved bytes listLen)
      (Q' := flatResult spC listBase outPtr saved bytes listLen)
      (fun _ hp => by
        unfold teerListCountCalleeP at hp
        rw [regsAt_countFrame]
        simp only [saved]
        xperm_hyp hp)
      (fun _ hq => hq) hleaf
  have hleafQ : cpsTripleWithin (nListCountSteps listLen) LC LinkListCount
      teerLinkedCount
      ((.x1 ↦ᵣ LinkListCount) **
        teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
          bytes)
      ((.x1 ↦ᵣ LinkListCount) **
        teerListCountCalleeQ spC listBase outPtr s0 s1 s2 s3 bytes listLen) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => by
        have hq' := flatResult_to_teerListCountCalleeQ
          spC listBase outPtr saved bytes listLen h hq
        simpa [saved] using hq')
      hleafP
  have hcall := callWithin_spec AtListCount LC old1 listCountJalOff
    (nListCountSteps listLen) listCountJalOff_resolves
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AtListCount teerProg 169
        (.JAL .x1 listCountJalOff) (by simp only [AtListCount]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi))
    (teerListCountCalleeP_pcFree spC listBase listLenW outPtr oldCount
      s0 s1 s2 s3 bytes)
    hleafQ
  rw [show (AtListCount + 4 : Word) = LinkListCount from by
    simp only [AtListCount, LinkListCount]; bv_omega] at hcall
  exact hcall

/-- BNE a0,x0 fail: not-taken when a0=0 → AfterListCountBne. -/
theorem teerListCountBneOk :
    cpsTripleWithin 1 LinkListCount AfterListCountBne teerLinkedCount
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 teerListCountBneOff
    (0 : Word) (0 : Word) LinkListCount
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkListCount teerProg 170
        (.BNE .x10 .x0 teerListCountBneOff)
        (by simp only [LinkListCount]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkListCount + 4 = AfterListCountBne := by
    simp only [LinkListCount, AfterListCountBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

private theorem se12_zero_lc : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- `la t0, teer_auth_count` at AfterListCountBne → E+692. -/
theorem teerLaAuthCountLoad (v : Word) :
    cpsTripleWithin 2 AfterListCountBne (E + 692) teerLinkedCount
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ AuthCountAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterListCountBne
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_auth_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 684)))
        a = some i → teerLinkedCount a = some i := fun a i hi =>
    teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterListCountBne teerProg 171
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_auth_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 684)))
        (by simp only [AfterListCountBne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 688)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_auth_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 684)))
        a = some i → teerLinkedCount a = some i := fun a i hi =>
    teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 688) teerProg 172
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_auth_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 684)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterListCountBne AuthCountAddr
    (by decide) (by decide) hau had
  rw [show (AfterListCountBne : Word) + 8 = E + 692 from by
    simp only [AfterListCountBne]; bv_omega] at h
  exact h

/-- `ld s7, 0(t0)` teer_auth_count at E+692. -/
theorem teerLdAuthCount (countW s7Old : Word) :
    cpsTripleWithin 1 (E + 692) AfterAuthCountLoad teerLinkedCount
      ((.x5 ↦ᵣ AuthCountAddr) ** (.x23 ↦ᵣ s7Old) ** (AuthCountAddr ↦ₘ countW))
      ((.x5 ↦ᵣ AuthCountAddr) ** (.x23 ↦ᵣ countW) ** (AuthCountAddr ↦ₘ countW)) := by
  have h0 := ld_spec_gen_within .x23 .x5 AuthCountAddr s7Old countW
    (0 : BitVec 12) (E + 692) (by decide)
  rw [show AuthCountAddr + signExtend12 (0 : BitVec 12) = AuthCountAddr from by
    rw [se12_zero_lc]; exact BitVec.add_zero AuthCountAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 692) teerProg 173
        (.LD .x23 .x5 (0 : BitVec 12)) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 692 : Word) + 4 = AfterAuthCountLoad := by
    simp only [AfterAuthCountLoad]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `la t0, teer_auth_count; ld s7, 0(t0)` → AfterAuthCountLoad. -/
theorem teerLdAuthCountS7 (countW s7Old t0Old : Word) :
    cpsTripleWithin 3 AfterListCountBne AfterAuthCountLoad teerLinkedCount
      ((.x5 ↦ᵣ t0Old) ** (.x23 ↦ᵣ s7Old) ** (AuthCountAddr ↦ₘ countW))
      ((.x5 ↦ᵣ AuthCountAddr) ** (.x23 ↦ᵣ countW) **
        (AuthCountAddr ↦ₘ countW)) := by
  have hla := teerLaAuthCountLoad t0Old
  have hlaF := cpsTripleWithin_frameR
    ((.x23 ↦ᵣ s7Old) ** (AuthCountAddr ↦ₘ countW)) (by pcf) hla
  have hld := teerLdAuthCount countW s7Old
  -- ld already has x5 in pre/post; frame only needs identity on x5 after la
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlaF hld
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq


/-- Success-path callee post after Call: status 0, out cell holds countW. -/
def teerListCountCalleeQOk (spC listBase outPtr s0 s1 s2 s3 countW : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  ((.x2 ↦ᵣ spC) **
      ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
      stackFree spC 6) **
    ((.x10 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** (outPtr ↦ₘ countW))

/-- After Call+BNE+LD success: s7=countW, out↦countW. -/
def teerListCountLoadPost (spC listBase outPtr s0 s1 s2 s3 countW : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  ((.x2 ↦ᵣ spC) **
      ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
      stackFree spC 6) **
    ((.x1 ↦ᵣ LinkListCount) **
     (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ AuthCountAddr) **
     (.x23 ↦ᵣ countW) ** regOwn .x6 ** regOwn .x7 **
     regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** (outPtr ↦ₘ countW))

/-- Call + BNE + la/ld s7 step bound. -/
def nListCountOkToLoad (listLen : Nat) : Nat :=
  (1 + nListCountSteps listLen) + 1 + 3

/-- Residual pure bridge: under Success, flat Result is status-0 with that count.
    `Failure.walk` requires still-inside (`ult`). Empty-short specialize is free:
    `teerListCountResultSpecialize_empty_short` (listLen=1). -/
def ListCountResultSpecialize (bytes : List (BitVec 8)) (listBase : Word)
    (listLen count : Nat) (countW : Word) : Prop :=
  countW = BitVec.ofNat 64 count →
  count < 2 ^ 64 →
  Success bytes listBase listLen count →
    ∀ status result : Word,
      Result bytes listBase listLen status result →
        status = (0 : Word) ∧ result = countW

/-- Success yields an outer StrictListPayload (rules out Failure.init). -/
theorem Success_implies_payload
    {bytes : List (BitVec 8)} {base : Word} {listLen count : Nat}
    (hS : Success bytes base listLen count) :
    ∃ cursorOff endPtr,
      EvmAsm.Codegen.RlpListNthItemSAsm.StrictListPayload
        bytes base listLen cursorOff endPtr := by
  obtain ⟨cursorOff, endPtr, hlist, _⟩ := hS
  exact ⟨cursorOff, endPtr, hlist⟩

/-- Call post → ok post under Result specialization. -/
theorem teerListCountCalleeQ_to_ok
    (spC listBase outPtr s0 s1 s2 s3 countW : Word)
    (bytes : List (BitVec 8)) (listLen count : Nat)
    (hcountW : countW = BitVec.ofNat 64 count)
    (hcount : count < 2 ^ 64)
    (hsuccess : Success bytes listBase listLen count)
    (hspe : ListCountResultSpecialize bytes listBase listLen count countW) :
    ∀ h, teerListCountCalleeQ spC listBase outPtr s0 s1 s2 s3 bytes listLen h →
      teerListCountCalleeQOk spC listBase outPtr s0 s1 s2 s3 countW bytes h := by
  intro h hq
  unfold teerListCountCalleeQ at hq
  obtain ⟨status, result, v11, v12, hcore⟩ := hq
  have hR : Result bytes listBase listLen status result :=
    ((sepConj_pure_right _).1 hcore).2
  obtain ⟨hst, hres⟩ := hspe hcountW hcount hsuccess status result hR
  -- rewrite status/result without subst (keeps countW binder)
  have hbody0 := ((sepConj_pure_right _).1 hcore).1
  -- hbody0 still has result; rewrite to countW via hres
  have hbody : ((((.x2 ↦ᵣ spC) **
        ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
        stackFree spC 6) **
      ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
       regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (outPtr ↦ₘ countW)))) h := by
    simpa [hres] using hbody0
  unfold teerListCountCalleeQOk
  -- status → 0
  have hbody1 : ((((.x2 ↦ᵣ spC) **
        ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
        stackFree spC 6) **
      ((.x10 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
       regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (outPtr ↦ₘ countW)))) h := by
    simpa [hst] using hbody
  refine sepConj_mono_right ?_ _ hbody1
  intro h' hp'
  -- lift x11 then x12 regIs → regOwn
  have hx11 :=
    sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn (r := .x11) (v := v11))))))
      _ hp'
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (regIs_implies_regOwn (r := .x12) (v := v12)))))))
    _ hx11

set_option maxRecDepth 8000 in
/-- Call under specialization → status-0 QOk post. -/
theorem teerListCountCall_ok
    (spC newSp listBase listLenW outPtr oldCount s0 s1 s2 s3 countW : Word)
    (bytes : List (BitVec 8)) (listLen count : Nat) (old1 : Word)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spC + signExtend12 (-48 : BitVec 12))
    (hret : (LinkListCount &&& ~~~(1 : Word)) = LinkListCount)
    (hcountW : countW = BitVec.ofNat 64 count)
    (hcount : count < 2 ^ 64)
    (hsuccess : Success bytes listBase listLen count)
    (hspe : ListCountResultSpecialize bytes listBase listLen count countW) :
    cpsTripleWithin (1 + nListCountSteps listLen) AtListCount LinkListCount
      teerLinkedCount
      ((.x1 ↦ᵣ old1) **
        teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
          bytes)
      ((.x1 ↦ᵣ LinkListCount) **
        teerListCountCalleeQOk spC listBase outPtr s0 s1 s2 s3 countW bytes) := by
  have hcall := teerListCountCall spC newSp listBase listLenW outPtr oldCount
    s0 s1 s2 s3 bytes listLen old1 hlistLenW hsalign hslack hover hvalid hnewSp hret
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hra, hQ⟩ := hq
      exact ⟨h1, h2, hd, hu, hra,
        teerListCountCalleeQ_to_ok spC listBase outPtr s0 s1 s2 s3 countW bytes
          listLen count hcountW hcount hsuccess hspe h2 hQ⟩) hcall

/-- Mid assertion after Call_ok framed with s7: ra + QOk + s7. -/
def teerListCountAfterCallOk (spC listBase outPtr s0 s1 s2 s3 countW s7Old : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  ((.x1 ↦ᵣ LinkListCount) **
      teerListCountCalleeQOk spC listBase outPtr s0 s1 s2 s3 countW bytes) **
    (.x23 ↦ᵣ s7Old)

private theorem teerListCountAfterCallOk_pcFree
    (spC listBase outPtr s0 s1 s2 s3 countW s7Old : Word)
    (bytes : List (BitVec 8)) :
    (teerListCountAfterCallOk spC listBase outPtr s0 s1 s2 s3 countW s7Old
      bytes).pcFree := by
  unfold teerListCountAfterCallOk teerListCountCalleeQOk; pcf

/-- BNE focus atoms pulled left for frameR. -/
def teerListCountBneFrame (spC listBase outPtr s0 s1 s2 s3 countW s7Old : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  ((.x1 ↦ᵣ LinkListCount) **
      ((.x2 ↦ᵣ spC) **
          ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
          stackFree spC 6) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
         regOwn .x30 ** regOwn .x31 **
         bytesRegion listBase bytes ** (outPtr ↦ₘ countW))) **
    (.x23 ↦ᵣ s7Old)

private theorem teerListCountBneFrame_pcFree
    (spC listBase outPtr s0 s1 s2 s3 countW s7Old : Word)
    (bytes : List (BitVec 8)) :
    (teerListCountBneFrame spC listBase outPtr s0 s1 s2 s3 countW s7Old
      bytes).pcFree := by
  unfold teerListCountBneFrame; pcf

private theorem teerListCountAfterCallOk_to_bnePre
    (spC listBase outPtr s0 s1 s2 s3 countW s7Old : Word)
    (bytes : List (BitVec 8)) (h : PartialState) :
    teerListCountAfterCallOk spC listBase outPtr s0 s1 s2 s3 countW s7Old bytes h →
      (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        teerListCountBneFrame spC listBase outPtr s0 s1 s2 s3 countW s7Old
          bytes) h := by
  intro hp
  unfold teerListCountAfterCallOk teerListCountCalleeQOk at hp
  unfold teerListCountBneFrame
  xperm_hyp hp

private theorem teerListCountBnePost_to_afterCallOk
    (spC listBase outPtr s0 s1 s2 s3 countW s7Old : Word)
    (bytes : List (BitVec 8)) (h : PartialState) :
    (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
      teerListCountBneFrame spC listBase outPtr s0 s1 s2 s3 countW s7Old
        bytes) h →
      teerListCountAfterCallOk spC listBase outPtr s0 s1 s2 s3 countW s7Old
        bytes h := by
  intro hp
  unfold teerListCountAfterCallOk teerListCountCalleeQOk
  unfold teerListCountBneFrame at hp
  xperm_hyp hp

/-- BNE framed under AfterCallOk. -/
theorem teerListCountBneOk_framed
    (spC listBase outPtr s0 s1 s2 s3 countW s7Old : Word)
    (bytes : List (BitVec 8)) :
    cpsTripleWithin 1 LinkListCount AfterListCountBne teerLinkedCount
      (teerListCountAfterCallOk spC listBase outPtr s0 s1 s2 s3 countW s7Old bytes)
      (teerListCountAfterCallOk spC listBase outPtr s0 s1 s2 s3 countW s7Old
        bytes) := by
  have hbneF := cpsTripleWithin_frameR
    (teerListCountBneFrame spC listBase outPtr s0 s1 s2 s3 countW s7Old bytes)
    (teerListCountBneFrame_pcFree spC listBase outPtr s0 s1 s2 s3 countW s7Old
      bytes)
    teerListCountBneOk
  exact cpsTripleWithin_weaken
    (teerListCountAfterCallOk_to_bnePre spC listBase outPtr s0 s1 s2 s3 countW
      s7Old bytes)
    (teerListCountBnePost_to_afterCallOk spC listBase outPtr s0 s1 s2 s3 countW
      s7Old bytes)
    hbneF

/-- LD frame: AfterCallOk without regOwn x5 (supplied as x5↦t0). -/
def teerListCountLdFrame (spC listBase s0 s1 s2 s3 s7Old : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  ((.x1 ↦ᵣ LinkListCount) **
      ((.x2 ↦ᵣ spC) **
          ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
          stackFree spC 6) **
        ((.x10 ↦ᵣ (0 : Word)) ** regOwn .x6 ** regOwn .x7 **
         regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
         regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes)) **
    (.x23 ↦ᵣ s7Old)

private theorem teerListCountLdFrame_pcFree
    (spC listBase s0 s1 s2 s3 s7Old : Word)
    (bytes : List (BitVec 8)) :
    (teerListCountLdFrame spC listBase s0 s1 s2 s3 s7Old bytes).pcFree := by
  unfold teerListCountLdFrame; pcf

/-- ∀ t0, LD under x5↦t0 + out↦count framed. -/
theorem teerListCountLd_forall
    (spC listBase s0 s1 s2 s3 countW s7Old : Word)
    (bytes : List (BitVec 8)) (t0 : Word) :
    cpsTripleWithin 3 AfterListCountBne AfterAuthCountLoad teerLinkedCount
      (((.x5 ↦ᵣ t0) ** (AuthCountAddr ↦ₘ countW)) **
        teerListCountLdFrame spC listBase s0 s1 s2 s3 s7Old bytes)
      (teerListCountLoadPost spC listBase AuthCountAddr s0 s1 s2 s3 countW
        bytes) := by
  have hld := teerLdAuthCountS7 countW s7Old t0
  -- Frame: everything in LdFrame except x23 (owned by hld prest)
  have hldF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkListCount) **
        ((.x2 ↦ᵣ spC) **
            ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
            stackFree spC 6) **
          ((.x10 ↦ᵣ (0 : Word)) ** regOwn .x6 ** regOwn .x7 **
           regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
           regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
           bytesRegion listBase bytes))
    (by pcf) hld
  -- weaken: desired prest P' → hldF prest P; hldF post Q → desired Q'
  refine cpsTripleWithin_weaken ?_ ?_ hldF
  · intro h hp
    -- hp : ((x5 ** Auth) ** LdFrame) h
    -- goal: ((x5 ** x23 ** Auth) ** frame) h
    unfold teerListCountLdFrame at hp
    xperm_hyp hp
  · intro h hq
    -- hq : ((x5=Auth ** x23=count ** Auth↦count) ** frame) h
    -- goal: LoadPost h
    unfold teerListCountLoadPost
    xperm_hyp hq

/-- AfterCallOk → (regOwn x5 ** Auth↦count) ** LdFrame (out=Auth). -/
private theorem teerListCountAfterCallOk_to_ldOwnPre
    (spC listBase s0 s1 s2 s3 countW s7Old : Word)
    (bytes : List (BitVec 8)) (h : PartialState) :
    teerListCountAfterCallOk spC listBase AuthCountAddr s0 s1 s2 s3 countW s7Old
        bytes h →
      ((regOwn .x5 ** (AuthCountAddr ↦ₘ countW)) **
        teerListCountLdFrame spC listBase s0 s1 s2 s3 s7Old bytes) h := by
  intro hp
  unfold teerListCountAfterCallOk teerListCountCalleeQOk at hp
  unfold teerListCountLdFrame
  xperm_hyp hp

/-- LD framed under AfterCallOk via of_forall on x5. -/
theorem teerListCountLd_framed
    (spC listBase s0 s1 s2 s3 countW s7Old : Word)
    (bytes : List (BitVec 8)) :
    cpsTripleWithin 3 AfterListCountBne AfterAuthCountLoad teerLinkedCount
      (teerListCountAfterCallOk spC listBase AuthCountAddr s0 s1 s2 s3 countW s7Old
        bytes)
      (teerListCountLoadPost spC listBase AuthCountAddr s0 s1 s2 s3 countW
        bytes) := by
  have hld_forall : ∀ t0,
      cpsTripleWithin 3 AfterListCountBne AfterAuthCountLoad teerLinkedCount
        (((.x5 ↦ᵣ t0) ** (AuthCountAddr ↦ₘ countW)) **
          teerListCountLdFrame spC listBase s0 s1 s2 s3 s7Old bytes)
        (teerListCountLoadPost spC listBase AuthCountAddr s0 s1 s2 s3 countW
          bytes) :=
    fun t0 => teerListCountLd_forall spC listBase s0 s1 s2 s3 countW s7Old bytes t0
  have hld_forall' : ∀ t0,
      cpsTripleWithin 3 AfterListCountBne AfterAuthCountLoad teerLinkedCount
        (((AuthCountAddr ↦ₘ countW) **
            teerListCountLdFrame spC listBase s0 s1 s2 s3 s7Old bytes) **
          (.x5 ↦ᵣ t0))
        (teerListCountLoadPost spC listBase AuthCountAddr s0 s1 s2 s3 countW
          bytes) := by
    intro t0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (hld_forall t0)
  have hld_own :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (AuthCountAddr ↦ₘ countW) **
        teerListCountLdFrame spC listBase s0 s1 s2 s3 s7Old bytes)
      hld_forall'
  exact cpsTripleWithin_weaken
    (fun h hp => by
      have hp' := teerListCountAfterCallOk_to_ldOwnPre spC listBase s0 s1 s2 s3
        countW s7Old bytes h hp
      xperm_hyp hp')
    (fun _ hq => hq) hld_own

set_option maxRecDepth 8000 in
/-- Call_ok + BNE + la/ld s7 under Result specialize. -/
theorem teerListCountOkToLoad
    (spC newSp listBase listLenW outPtr oldCount s0 s1 s2 s3 countW : Word)
    (bytes : List (BitVec 8)) (listLen count : Nat) (old1 s7Old : Word)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spC + signExtend12 (-48 : BitVec 12))
    (hret : (LinkListCount &&& ~~~(1 : Word)) = LinkListCount)
    (hcountW : countW = BitVec.ofNat 64 count)
    (hcount : count < 2 ^ 64)
    (hsuccess : Success bytes listBase listLen count)
    (hspe : ListCountResultSpecialize bytes listBase listLen count countW)
    (hout : outPtr = AuthCountAddr) :
    cpsTripleWithin (nListCountOkToLoad listLen) AtListCount AfterAuthCountLoad
      teerLinkedCount
      ((.x1 ↦ᵣ old1) ** (.x23 ↦ᵣ s7Old) **
        teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
          bytes)
      (teerListCountLoadPost spC listBase outPtr s0 s1 s2 s3 countW bytes) := by
  subst hout
  have hcall := teerListCountCall_ok spC newSp listBase listLenW AuthCountAddr
    oldCount s0 s1 s2 s3 countW bytes listLen count old1 hlistLenW hsalign hslack
    hover hvalid hnewSp hret hcountW hcount hsuccess hspe
  have hcallF := cpsTripleWithin_frameR (.x23 ↦ᵣ s7Old) (by pcf) hcall
  -- post hcallF: (x1 ** QOk) ** x23 = AfterCallOk (defeq after unfold)
  have hcallF' : cpsTripleWithin (1 + nListCountSteps listLen) AtListCount
      LinkListCount teerLinkedCount
      ((.x1 ↦ᵣ old1) ** (.x23 ↦ᵣ s7Old) **
        teerListCountCalleeP spC listBase listLenW AuthCountAddr oldCount
          s0 s1 s2 s3 bytes)
      (teerListCountAfterCallOk spC listBase AuthCountAddr s0 s1 s2 s3 countW
        s7Old bytes) := by
    refine cpsTripleWithin_weaken ?_ ?_ hcallF
    · intro h hp; xperm_hyp hp
    · intro h hq
      show (teerListCountAfterCallOk spC listBase AuthCountAddr s0 s1 s2 s3
          countW s7Old bytes) h
      unfold teerListCountAfterCallOk
      xperm_hyp hq
  have hbne := teerListCountBneOk_framed spC listBase AuthCountAddr s0 s1 s2 s3
    countW s7Old bytes
  have hmid := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hcallF' hbne
  have hld := teerListCountLd_framed spC listBase s0 s1 s2 s3 countW s7Old bytes
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hmid hld

/-- list_count Call+BNE+LD success under nested `stackFree spC 6`.
    Requires `ListCountResultSpecialize` (walk-fail uniqueness residual pure). -/
structure TeerListCountAssumed (cr : CodeReq) where
  run :
    ∀ (spC newSp listBase listLenW outPtr oldCount s0 s1 s2 s3 countW : Word)
      (bytes : List (BitVec 8)) (listLen count : Nat) (old1 s7Old : Word),
      listLenW = BitVec.ofNat 64 listLen →
      listBase.toNat % 8 = 0 →
      listLen + 9 ≤ bytes.length →
      listBase.toNat + bytes.length < 2 ^ 64 →
      (∀ k, k < bytes.length →
        isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) →
      newSp = spC + signExtend12 (-48 : BitVec 12) →
      (LinkListCount &&& ~~~(1 : Word)) = LinkListCount →
      countW = BitVec.ofNat 64 count →
      count < 2 ^ 64 →
      Success bytes listBase listLen count →
      ListCountResultSpecialize bytes listBase listLen count countW →
      outPtr = AuthCountAddr →
      cpsTripleWithin (nListCountOkToLoad listLen) AtListCount AfterAuthCountLoad cr
        ((.x1 ↦ᵣ old1) ** (.x23 ↦ᵣ s7Old) **
          teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
            bytes)
        (teerListCountLoadPost spC listBase outPtr s0 s1 s2 s3 countW bytes)

def teerListCountAssumed_teerLinked : TeerListCountAssumed teerLinkedCount where
  run := fun spC newSp listBase listLenW outPtr oldCount s0 s1 s2 s3 countW
      bytes listLen count old1 s7Old
      hlistLenW hsalign hslack hover hvalid hnewSp hret hcountW hcount
      hsuccess hspe hout =>
    teerListCountOkToLoad spC newSp listBase listLenW outPtr oldCount
      s0 s1 s2 s3 countW bytes listLen count old1 s7Old hlistLenW hsalign hslack
      hover hvalid hnewSp hret hcountW hcount hsuccess hspe hout

#print axioms teerListCountCall
#print axioms teerListCountBneOk
#print axioms teerLdAuthCountS7
#print axioms teerListCountCall_ok
#print axioms teerListCountCalleeQ_to_ok
#print axioms Success_implies_payload
#print axioms teerListCountOkToLoad
#print axioms teerListCountAssumed_teerLinked

end EvmAsm.Codegen.TxEip7702TeerSpec
