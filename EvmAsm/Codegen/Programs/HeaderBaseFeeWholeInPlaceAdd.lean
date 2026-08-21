/-
  EvmAsm.Codegen.Programs.HeaderBaseFeeWholeInPlaceAdd

  K73's in-place `u256_add_be` call and the tail that follows it.  Split out
  of `HeaderBaseFeeWholeBranches` (which sat exactly at the per-file size cap)
  when the v4.33 toolchain bump added tactic lines to the branch proofs there.
  The two clusters are independent: nothing here is referenced by the branch
  compositions, and nothing there is referenced from here.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeSpec

namespace EvmAsm.Codegen.HeaderBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256BeFlat
open EvmAsm.Codegen.U256AddBeBInPlaceSAsm
open EvmAsm.Codegen.U256AddBeSAsm
private theorem add_target188 :
    (K73 + 188) + signExtend21
        (jalOff GuestAddrs.u256_add_be
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 188)) =
      (GuestAddrs.u256_add_be : Word) := by
  change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 188 + _ = BitVec.ofNat 64 GuestAddrs.u256_add_be
  exact jalOff_correct_add GuestAddrs.u256_add_be
    GuestAddrs.eip1559_calc_base_fee_per_gas 188
    (by decide) (by decide) (by decide) (by decide)
private theorem add_mem188 :
    ∀ a i, CodeReq.singleton (K73 + 188)
      (.JAL .x1 (jalOff GuestAddrs.u256_add_be
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 188))) a = some i →
      wholeCode a = some i := by
  intro a i hi
  exact k73_whole_mono a i (k73_mem 47 _ (K73 + 188) (by decide)
    (by rw [k73_length]; decide) (by rfl) a i hi)
@[irreducible] def k73AddBCallSteps
    (srcPtr outPtr : Word) (srcBytes orig : List (BitVec 8)) : Nat :=
  5 + (u256AddBeBInPlaceFn srcPtr outPtr srcBytes orig).body.steps
@[irreducible] def k73AddBBranchSteps
    (srcPtr outPtr : Word) (srcBytes orig : List (BitVec 8)) : Nat :=
  6 + (u256AddBeBInPlaceFn srcPtr outPtr srcBytes orig).body.steps
@[irreducible] def k73AddBSize
    (srcPtr outPtr : Word) (srcBytes orig : List (BitVec 8)) : Nat :=
  4 * ((u256AddBeBInPlaceFn srcPtr outPtr srcBytes orig).body.size + 1)
private theorem k73_in_place_add_b_move_spec_within
    (rDst rSrc : Reg) (src dstOld A : Word) (idx : Nat)
    (Rest : Assertion) (hRest : Rest.pcFree)
    (hrDst : rDst ≠ .x0)
    (hA : A = K73 + BitVec.ofNat 64 (4 * idx))
    (hk : idx < prog.length)
    (hins : prog[idx]'hk = .MV rDst rSrc) :
    cpsTripleWithin 1 A (A + 4) wholeCode
      ((rSrc ↦ᵣ src) ** (rDst ↦ᵣ dstOld) ** Rest)
      ((rSrc ↦ᵣ src) ** (rDst ↦ᵣ src) ** Rest) := by
  have hmv := mv_spec_gen_within rDst rSrc src dstOld A hrDst
  have hmem : ∀ a i, CodeReq.singleton A (.MV rDst rSrc) a = some i →
      fullCode a = some i := by
    intro a i hi
    exact k73_mono a i (k73_mem idx (.MV rDst rSrc) A hA hk hins a i hi)
  have hmvc := cpsTripleWithin_extend_code full_whole_mono
    (cpsTripleWithin_extend_code
      hmem hmv)
  have hmvf := cpsTripleWithin_frameR Rest hRest hmvc
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hmvf
private theorem k73_in_place_add_b_setup_spec_within_v2
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) :
    cpsTripleWithin 3 (K73 + 176) (K73 + 188) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes) ** F)
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) ** (.x10 ↦ᵣ srcPtr) **
        (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes) ** F) := by
  let G : Assertion :=
    regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
      bytesRegion srcPtr srcBytes
  let R10 : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
      (.x9 ↦ᵣ outPtr) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** G
  let R11 : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
      (.x8 ↦ᵣ srcPtr) ** (.x10 ↦ᵣ srcPtr) ** (.x12 ↦ᵣ v12) ** G
  let R12 : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
      (.x8 ↦ᵣ srcPtr) ** (.x10 ↦ᵣ srcPtr) ** (.x11 ↦ᵣ outPtr) ** G
  have hR10 : R10.pcFree := by dsimp [R10, G]; pcf
  have hR11 : R11.pcFree := by dsimp [R11, G]; pcf
  have hR12 : R12.pcFree := by dsimp [R12, G]; pcf
  have h10 := k73_in_place_add_b_move_spec_within
    .x10 .x8 srcPtr v10 (K73 + 176) 44 R10 hR10 (by decide)
    (by decide) (by rw [k73_length]; decide) (by rfl)
  have h11 := k73_in_place_add_b_move_spec_within
    .x11 .x9 outPtr v11 (K73 + 180) 45 R11 hR11 (by decide)
    (by decide) (by rw [k73_length]; decide) (by rfl)
  have h12 := k73_in_place_add_b_move_spec_within
    .x12 .x9 outPtr v12 (K73 + 184) 46 R12 hR12 (by decide)
    (by decide) (by rw [k73_length]; decide) (by rfl)
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h10 h11
  have h012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h01 h12
  have h012F := cpsTripleWithin_frameR F hF h012
  rw [show (K73 + 184) + 4 = K73 + 188 from by bv_omega] at h012F
  dsimp [R10, R11, R12, G] at h012F ⊢
  simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using h012F
theorem k73_in_place_add_b_spec_within
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroSrc : Region.wf ⟨srcPtr, srcBytes⟩)
    (hlenSrc : srcBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovSrc : srcPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : srcPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ srcPtr.toNat)
    (hsz : k73AddBSize srcPtr outPtr srcBytes orig ≤ 2 ^ 64)
    (hret : ((K73 + 188) + 4) &&& ~~~(1 : Word) = (K73 + 188) + 4) :
    cpsTripleWithin
      (k73AddBCallSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) (K73 + 192) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ (K73 + 192)) **
        (.x10 ↦ᵣ u256AddBeCarry srcBytes orig orig) **
        (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) ** F) := by
  have hsetup := k73_in_place_add_b_setup_spec_within_v2
    srcPtr outPtr oldRa v10 v11 v12 srcBytes orig F hF
  have hadd := u256AddBeBInPlaceFlat_spec
    (K73 + 192) srcPtr outPtr srcBytes orig hrw hroSrc hlenSrc hlenOrig
    hovSrc hovOut hdisj (by
      simpa only [k73AddBSize] using hsz) hret
  have haddc := cpsTripleWithin_extend_code add_whole_mono hadd
  have hcall := callWithin_spec
    (cr := wholeCode)
    (P := ((.x10 ↦ᵣ srcPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
      bytesRegion srcPtr srcBytes))
    (Q := ((.x10 ↦ᵣ u256AddBeCarry srcBytes orig orig) **
      (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
      bytesRegion srcPtr srcBytes))
    (K73 + 188) (GuestAddrs.u256_add_be : Word) oldRa
    (jalOff GuestAddrs.u256_add_be
      (GuestAddrs.eip1559_calc_base_fee_per_gas + 188))
    ((u256AddBeBInPlaceFn srcPtr outPtr srcBytes orig).body.steps + 1)
    add_target188 add_mem188
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (pcFree_regOwns _)
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (bytesRegion_pcFree _ _))))))
    (by simpa only [show (K73 + 188) + 4 = K73 + 192 by bv_omega] using haddc)
  have hcallf := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ srcPtr) **
      (.x9 ↦ᵣ outPtr) ** F)
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hF))) hcall
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsetup hcallf
  have hseq' := cpsTripleWithin_mono_nSteps
    (nSteps' := k73AddBCallSteps srcPtr outPtr srcBytes orig)
    (by unfold k73AddBCallSteps; omega) hseq
  refine cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      simp only [show (K73 + 188) + 4 = K73 + 192 by bv_omega] at hq
      xperm_chunked hq) hseq'
theorem k73_in_place_add_b_branch_spec_within
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroSrc : Region.wf ⟨srcPtr, srcBytes⟩)
    (hlenSrc : srcBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovSrc : srcPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : srcPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ srcPtr.toNat)
    (hsz : k73AddBSize srcPtr outPtr srcBytes orig ≤ 2 ^ 64)
    (hret : ((K73 + 188) + 4) &&& ~~~(1 : Word) = (K73 + 188) + 4) :
    cpsBranchWithin
      (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** F)
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
          (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
          regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
          bytesRegion srcPtr srcBytes ** regOwn .x10 ** F)
      (K73 + 196)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
          (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
          regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
          bytesRegion srcPtr srcBytes ** regOwn .x10 ** F) := by
  let AddRest : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
      (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
      bytesRegion srcPtr srcBytes ** F
  let BranchRest : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** AddRest
  have hAddRest : AddRest.pcFree := by
    dsimp [AddRest]
    pcf
    exact hF
  have hadd := k73_in_place_add_b_spec_within
    srcPtr outPtr oldRa v10 v11 v12 srcBytes orig F hF hrw hroSrc
      hlenSrc hlenOrig hovSrc hovOut hdisj hsz hret
  have hadd0 : cpsTripleWithin
      (k73AddBCallSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) (K73 + 192) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ oldRa) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** F)
      (BranchRest ** ((.x10 : Reg) ↦ᵣ u256AddBeCarry
        srcBytes orig orig)) := by
    refine cpsTripleWithin_weaken
      (P' :=
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ oldRa) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
          (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
          bytesRegion srcPtr srcBytes ** F))
      (Q' := BranchRest ** ((.x10 : Reg) ↦ᵣ u256AddBeCarry
        srcBytes orig orig))
      (fun _ hp => by exact hp)
      (fun _ hq => by
        dsimp [BranchRest, AddRest] at hq ⊢
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        xperm_hyp hq)
      hadd
  have hraw : ∀ old10, cpsBranchWithin 1 (K73 + 192) wholeCode
      (BranchRest ** ((.x10 : Reg) ↦ᵣ old10))
      (K73 + 272) (BranchRest ** regOwn .x10)
      (K73 + 196) (BranchRest ** regOwn .x10) := by
    intro old10
    have hbne := bne_spec_gen_within .x10 .x0 (80 : BitVec 13)
      old10 (0 : Word) (K73 + 192)
    have hbneC := cpsBranchWithin_extend_code
      (k73_whole_mem 48 _ (K73 + 192) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hbne
    rw [show signExtend13 (80 : BitVec 13) = (80 : Word) by decide,
      show (K73 + 192) + (80 : Word) = K73 + 272 by bv_omega,
      show (K73 + 192) + 4 = K73 + 196 by bv_omega] at hbneC
    have hbneF := cpsBranchWithin_frameR AddRest hAddRest hbneC
    refine cpsBranchWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun s hq => by
        have hq' :
            (((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              AddRest ** (⌜old10 ≠ (0 : Word)⌝)) s := by
          xperm_hyp hq
        have hq'' :
            ((((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              AddRest) ** (⌜old10 ≠ (0 : Word)⌝)) s := by
          xperm_hyp hq'
        obtain ⟨hq0, _hne⟩ := (sepConj_pure_right _).1 hq''
        have hq1 := sepConj_mono_left (regIs_implies_regOwn .x10) s hq0
        xperm_hyp hq1
      )
      (fun s hq => by
        have hq' :
            (((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              AddRest ** (⌜old10 = (0 : Word)⌝)) s := by
          xperm_hyp hq
        have hq'' :
            ((((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              AddRest) ** (⌜old10 = (0 : Word)⌝)) s := by
          xperm_hyp hq'
        obtain ⟨hq0, _eq⟩ := (sepConj_pure_right _).1 hq''
        have hq1 := sepConj_mono_left (regIs_implies_regOwn .x10) s hq0
        xperm_hyp hq1
      ) hbneF
  have hbr := hraw (u256AddBeCarry srcBytes orig orig)
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_same_cr hadd0 hbr
  have hsteps :
      k73AddBCallSteps srcPtr outPtr srcBytes orig + 1 =
        k73AddBBranchSteps srcPtr outPtr srcBytes orig := by
    simp only [k73AddBCallSteps, k73AddBBranchSteps]
    omega
  have hseq' := cpsBranchWithin_mono_nSteps
    (by rw [hsteps]) hseq
  refine cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      dsimp [BranchRest, AddRest] at hq ⊢
      xperm_hyp hq)
    (fun _ hq => by
      dsimp [BranchRest, AddRest] at hq ⊢
      xperm_hyp hq)
    hseq'
@[irreducible] def k73AddBTailSteps
    (srcPtr outPtr : Word) (srcBytes orig : List (BitVec 8)) : Nat :=
  16 + (u256AddBeBInPlaceFn srcPtr outPtr srcBytes orig).body.steps
@[irreducible] def k73AddBBranchPost
    (srcPtr outPtr : Word) (srcBytes orig : List (BitVec 8))
    (F : Assertion) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 192)) **
    (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
    (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
    regOwns u256AddBeBInPlaceScratch **
    bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
    bytesRegion srcPtr srcBytes ** regOwn .x10 ** F
@[irreducible] def k73AddBTailPost
    (spH : Word) (saved : Reg → Word)
    (TailP : Assertion) : Assertion :=
  ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
    frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** TailP
private theorem k73_regsOwnAt_split :
    regsOwnAt k73Frame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regsOwnAt k73FrameRest3) := by
  simp [k73Frame, k73FrameRest3, regsOwnAt]
private theorem k73_in_place_add_tail_post_weaken
    (spH : Word) (saved : Reg → Word)
    (srcPtr outPtr : Word)
    (srcBytes orig : List (BitVec 8)) (F Fadd TailP : Assertion)
    (hFaddShape : Fadd =
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH saved ** F))
    (hTailPShape : TailP =
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** F)) :
    ∀ h,
      (k73AddBBranchPost srcPtr outPtr srcBytes orig Fadd) h →
      (k73AddBTailPost spH saved TailP) h := by
  intro s hq
  simp only [k73AddBBranchPost] at hq
  have hq1 :
      (((.x1 : Reg) ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) **
        (.x9 ↦ᵣ outPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
        regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** Fadd) s := by
    simpa [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq
  have hq2 := sepConj_mono_left (regIs_implies_regOwn .x1) _ hq1
  have hq2' :
      (((.x8 : Reg) ↦ᵣ srcPtr) ** regOwn .x1 **
        (.x9 ↦ᵣ outPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
        regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** Fadd) s := by
    xperm_hyp hq2
  have hq3 := sepConj_mono_left (regIs_implies_regOwn .x8) _ hq2'
  have hq3' :
      (((.x9 : Reg) ↦ᵣ outPtr) ** regOwn .x8 ** regOwn .x1 **
        (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
        regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** Fadd) s := by
    xperm_hyp hq3
  have hq4 := sepConj_mono_left (regIs_implies_regOwn .x9) _ hq3'
  rw [hFaddShape] at hq4
  simp only [k73AddBTailPost]
  rw [hTailPShape]
  rw [k73_regsOwnAt_split]
  simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq4 ⊢
  xperm_hyp hq4
private theorem k73_in_place_add_tail_branch_weaken
    (spH : Word) (saved : Reg → Word)
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F Fadd TailP : Assertion)
    (hFaddShape : Fadd =
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH saved ** F))
    (hTailPShape : TailP =
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** F))
    (hbranch :
      cpsBranchWithin
        (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
        (K73 + 176) wholeCode
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
          (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
          (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
          bytesRegion srcPtr srcBytes ** Fadd)
        (K73 + 272)
          (((.x0 : Reg) ↦ᵣ (0 : Word)) **
            (.x1 ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) **
            (.x9 ↦ᵣ outPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
            regOwns u256AddBeBInPlaceScratch **
            bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
            bytesRegion srcPtr srcBytes ** regOwn .x10 ** Fadd)
        (K73 + 196)
          (((.x0 : Reg) ↦ᵣ (0 : Word)) **
            (.x1 ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) **
            (.x9 ↦ᵣ outPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
            regOwns u256AddBeBInPlaceScratch **
            bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
            bytesRegion srcPtr srcBytes ** regOwn .x10 ** Fadd)) :
    cpsBranchWithin
      (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** Fadd)
      (K73 + 272)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** TailP)
      (K73 + 196)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** TailP) := by
  have hpost := k73_in_place_add_tail_post_weaken
    spH saved srcPtr outPtr srcBytes orig F Fadd TailP
      hFaddShape hTailPShape
  have hbranchNamed :
      cpsBranchWithin
        (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
        (K73 + 176) wholeCode
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
          (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) ** (.x10 ↦ᵣ v10) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
          bytesRegion srcPtr srcBytes ** Fadd)
        (K73 + 272) (k73AddBBranchPost srcPtr outPtr srcBytes orig Fadd)
        (K73 + 196) (k73AddBBranchPost srcPtr outPtr srcBytes orig Fadd) := by
    simpa only [k73AddBBranchPost] using hbranch
  have hbranch' := cpsBranchWithin_weaken
    (Q_t' := k73AddBTailPost spH saved TailP)
    (Q_f' := k73AddBTailPost spH saved TailP)
    (fun _ hp => by exact hp) hpost hpost hbranchNamed
  simpa only [k73AddBTailPost] using hbranch'
theorem k73_in_place_add_tail_branch_spec_within
    (spH : Word) (saved : Reg → Word)
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F Fadd TailP : Assertion)
    (hFaddShape : Fadd =
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH saved ** F))
    (hTailPShape : TailP =
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** F))
    (hFadd : Fadd.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroSrc : Region.wf ⟨srcPtr, srcBytes⟩)
    (hlenSrc : srcBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovSrc : srcPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : srcPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ srcPtr.toNat)
    (hsz : k73AddBSize srcPtr outPtr srcBytes orig ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = (K73 + 188) + 4) :
    cpsBranchWithin
      (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** Fadd)
      (K73 + 272)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** TailP)
      (K73 + 196)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** TailP) := by
  have hbranch := k73_in_place_add_b_branch_spec_within
    srcPtr outPtr oldRa v10 v11 v12 srcBytes orig Fadd hFadd hrw hroSrc
      hlenSrc hlenOrig hovSrc hovOut hdisj hsz hcallRet
  exact k73_in_place_add_tail_branch_weaken
    spH saved srcPtr outPtr oldRa v10 v11 v12 srcBytes orig F Fadd TailP
      hFaddShape hTailPShape hbranch
private theorem k73_holdsFor_sepConj_mono_left
    {P P' Q : Assertion} {s : MachineState}
    (himpl : ∀ h, P h → P' h)
    (h : (P ** Q).holdsFor s) : (P' ** Q).holdsFor s := by
  rcases h with ⟨hmem, hcompat, hpq⟩
  exact ⟨hmem, hcompat,
    sepConj_mono_left (P := P) (P' := P') (Q := Q) himpl hmem hpq⟩
theorem k73_in_place_add_tail_spec_within
    (sp0 spH raIn : Word) (saved : Reg → Word)
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F : Assertion)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : saved .x1 = raIn)
    (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroSrc : Region.wf ⟨srcPtr, srcBytes⟩)
    (hlenSrc : srcBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovSrc : srcPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : srcPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ srcPtr.toNat)
    (hsz : k73AddBSize srcPtr outPtr srcBytes orig ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = (K73 + 188) + 4) :
    cpsTripleWithin
      (k73AddBTailSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) raIn wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes **
        ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH saved ** F)
      (fun s =>
        (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame saved **
          frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ (1 : Word)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
          (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
          bytesRegion srcPtr srcBytes ** F) s ∨
        (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame saved **
          frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ (0 : Word)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
          (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
      bytesRegion srcPtr srcBytes ** F) s) := by
  let FrameRest : Assertion :=
    ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
      frameSlotsSaved k73Frame spH saved
  let Fadd : Assertion := FrameRest ** F
  have hFrameRest : FrameRest.pcFree := by
    dsimp [FrameRest]
    pcf
  have hFadd : Fadd.pcFree := by
    dsimp [Fadd]
    exact pcFree_sepConj hFrameRest hF
  let TailP : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
      bytesRegion srcPtr srcBytes ** F
  have hTailP : TailP.pcFree := by
    dsimp [TailP]
    pcf
    exact hF
  have hbranch' := k73_in_place_add_tail_branch_spec_within
    spH saved srcPtr outPtr oldRa v10 v11 v12 srcBytes orig F Fadd TailP
      (by simp [Fadd, FrameRest, sepConj_assoc']) (by simp [TailP]) hFadd hrw hroSrc
      hlenSrc hlenOrig hovSrc hovOut
      hdisj hsz hcallRet
  have hfail := k73_failure_tail_spec_within
    sp0 spH raIn saved TailP hsp hret hsaved hTailP
  have hsucc := k73_success_tail_spec_within
    sp0 spH raIn saved TailP hsp hret hsaved hTailP
  have hbudget :
      k73AddBBranchSteps srcPtr outPtr srcBytes orig + 10 ≤
        k73AddBTailSteps srcPtr outPtr srcBytes orig := by
    simp only [k73AddBBranchSteps, k73AddBTailSteps]
    omega
  intro R hR s hcr hP hpc
  obtain ⟨k1, hk1, s1, hs1, hcase⟩ := hbranch' R hR s hcr
    (by simpa [Fadd, FrameRest, sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hP)
    hpc
  rcases hcase with ⟨hpcFail, hFailPre⟩ | ⟨hpcSucc, hSuccPre⟩
  · obtain ⟨k2, hk2, s2, hs2, hFailPost⟩ :=
      hfail R hR s1 (CodeReq.SatisfiedBy_preserved hs1 hcr)
        hFailPre hpcFail
    refine ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2, ?_⟩
    refine ⟨hFailPost.1, ?_⟩
    apply k73_holdsFor_sepConj_mono_left (Q := R) (fun _ h => Or.inl h)
    exact hFailPost.2
  · obtain ⟨k2, hk2, s2, hs2, hSuccPost⟩ :=
      hsucc R hR s1 (CodeReq.SatisfiedBy_preserved hs1 hcr)
        hSuccPre hpcSucc
    refine ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2, ?_⟩
    refine ⟨hSuccPost.1, ?_⟩
    apply k73_holdsFor_sepConj_mono_left (Q := R) (fun _ h => Or.inr h)
    exact hSuccPost.2
end EvmAsm.Codegen.HeaderBaseFeeSpec
