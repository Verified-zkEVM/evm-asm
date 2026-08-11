/-
  EvmAsm.Codegen.Programs.ExecutionRequestsHashMono

  Offset-monotone accept chain for `execution_requests_hash` validation
  (GH #11578 rescope), idx 33–39 @ B+132 → B+160:

    LI  x5, 20
    BNE x19, x5, fail      -- deposit offset must be 20
    BLTU x20, x19, fail    -- wdr ≥ dep
    BLTU x21, x20, fail
    BLTU x22, x21, fail
    BLTU x23, x22, fail
    BLTU x9,  x23, fail    -- end ≥ bexit

  Accept fallthrough under `erhOffsetsMonoW`. Fail join @ B+480 residual.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.ExecutionRequestsHashGates
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.ExecutionRequestsHashMono

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashGates

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash
private abbrev erhProgL : List Instr := executionRequestsHash_prog

private theorem erhProgL_len : erhProgL.length = 135 := by
  simp only [erhProgL, executionRequestsHash_prog]; decide

private theorem erhProgL_bound : 4 * erhProgL.length < 2 ^ 64 := by
  rw [erhProgL_len]; norm_num

private abbrev erhCr : CodeReq := CodeReq.ofProg B erhProgL

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < erhProgL.length)
    (hins : erhProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → erhCr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at B A erhProgL k ins hA hk hins erhProgL_bound a i h

private def bneOffAt (branchByte : Nat) : BitVec 13 :=
  brOff (GuestAddrs.execution_requests_hash + 480)
    (GuestAddrs.execution_requests_hash + branchByte)

private def bltuOffAt (branchByte : Nat) : BitVec 13 :=
  brOff (GuestAddrs.execution_requests_hash + 480)
    (GuestAddrs.execution_requests_hash + branchByte)

private theorem bne_taken_136 :
    (B + 136) + signExtend13 (bneOffAt 136) = B + 480 := by
  unfold B bneOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 136 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 136)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 136 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bltu_taken_140 :
    (B + 140) + signExtend13 (bltuOffAt 140) = B + 480 := by
  unfold B bltuOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 140 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 140)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 140 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bltu_taken_144 :
    (B + 144) + signExtend13 (bltuOffAt 144) = B + 480 := by
  unfold B bltuOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 144 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 144)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 144 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bltu_taken_148 :
    (B + 148) + signExtend13 (bltuOffAt 148) = B + 480 := by
  unfold B bltuOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 148 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 148)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 148 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bltu_taken_152 :
    (B + 152) + signExtend13 (bltuOffAt 152) = B + 480 := by
  unfold B bltuOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 152 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 152)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 152 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bltu_taken_156 :
    (B + 156) + signExtend13 (bltuOffAt 156) = B + 480 := by
  unfold B bltuOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 156 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 156)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 156 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Word-level offset monotone + deposit offset = 20. -/
def erhOffsetsMonoW (o : ErhOffsets) : Prop :=
  o.dep = (20 : Word) ∧
  ¬ BitVec.ult o.wdr o.dep ∧
  ¬ BitVec.ult o.con o.wdr ∧
  ¬ BitVec.ult o.bdep o.con ∧
  ¬ BitVec.ult o.bexit o.bdep ∧
  ¬ BitVec.ult o.end_ o.bexit

/-- 7-step mono accept: B+132 → B+160 under erhOffsetsMonoW. -/
theorem erh_mono_accept
    (o : ErhOffsets)
    (v5 : Word)
    (hok : erhOffsetsMonoW o)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 7 (B + 132) (B + 160) erhCr
      (erhOffsetRegs o ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      (erhOffsetRegs o ** (.x5 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A) := by
  obtain ⟨hdep, hw, hc, hbd, hbe, hen⟩ := hok
  -- LI x5, 20 @ B+132
  have h0 := li_spec_gen_within .x5 v5 (20 : Word) (B + 132) (by decide)
  rw [show (B + 132 : Word) + 4 = B + 136 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (mem_at 33 (.LI .x5 (20 : Word)) (B + 132) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h0
  -- BNE x19, x5 @ B+136 ntaken (dep = 20)
  have h1br := bne_spec_gen_within .x19 .x5 (bneOffAt 136)
    o.dep (20 : Word) (B + 136)
  rw [bne_taken_136, show (B + 136 : Word) + 4 = B + 140 from by decide] at h1br
  have l1 := cpsBranchWithin_extend_code
    (mem_at 34 (.BNE .x19 .x5 (bneOffAt 136)) (B + 136) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h1br
  have h1nt := cpsBranchWithin_ntakenStripPure2 l1 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    have hne : o.dep ≠ (20 : Word) := ((sepConj_pure_right _).1 hQ).2
    exact hne hdep)
  -- BLTU x20, x19 @ B+140
  have h2br := bltu_spec_gen_within .x20 .x19 (bltuOffAt 140)
    o.wdr o.dep (B + 140)
  rw [bltu_taken_140, show (B + 140 : Word) + 4 = B + 144 from by decide] at h2br
  have l2 := cpsBranchWithin_extend_code
    (mem_at 35 (.BLTU .x20 .x19 (bltuOffAt 140)) (B + 140) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h2br
  have h2nt := cpsBranchWithin_ntakenStripPure2 l2 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hw ((sepConj_pure_right _).1 hQ).2)
  -- BLTU x21, x20 @ B+144
  have h3br := bltu_spec_gen_within .x21 .x20 (bltuOffAt 144)
    o.con o.wdr (B + 144)
  rw [bltu_taken_144, show (B + 144 : Word) + 4 = B + 148 from by decide] at h3br
  have l3 := cpsBranchWithin_extend_code
    (mem_at 36 (.BLTU .x21 .x20 (bltuOffAt 144)) (B + 144) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h3br
  have h3nt := cpsBranchWithin_ntakenStripPure2 l3 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hc ((sepConj_pure_right _).1 hQ).2)
  -- BLTU x22, x21 @ B+148
  have h4br := bltu_spec_gen_within .x22 .x21 (bltuOffAt 148)
    o.bdep o.con (B + 148)
  rw [bltu_taken_148, show (B + 148 : Word) + 4 = B + 152 from by decide] at h4br
  have l4 := cpsBranchWithin_extend_code
    (mem_at 37 (.BLTU .x22 .x21 (bltuOffAt 148)) (B + 148) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h4br
  have h4nt := cpsBranchWithin_ntakenStripPure2 l4 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hbd ((sepConj_pure_right _).1 hQ).2)
  -- BLTU x23, x22 @ B+152
  have h5br := bltu_spec_gen_within .x23 .x22 (bltuOffAt 152)
    o.bexit o.bdep (B + 152)
  rw [bltu_taken_152, show (B + 152 : Word) + 4 = B + 156 from by decide] at h5br
  have l5 := cpsBranchWithin_extend_code
    (mem_at 38 (.BLTU .x23 .x22 (bltuOffAt 152)) (B + 152) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h5br
  have h5nt := cpsBranchWithin_ntakenStripPure2 l5 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hbe ((sepConj_pure_right _).1 hQ).2)
  -- BLTU x9, x23 @ B+156
  have h6br := bltu_spec_gen_within .x9 .x23 (bltuOffAt 156)
    o.end_ o.bexit (B + 156)
  rw [bltu_taken_156, show (B + 156 : Word) + 4 = B + 160 from by decide] at h6br
  have l6 := cpsBranchWithin_extend_code
    (mem_at 39 (.BLTU .x9 .x23 (bltuOffAt 156)) (B + 156) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h6br
  have h6nt := cpsBranchWithin_ntakenStripPure2 l6 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hen ((sepConj_pure_right _).1 hQ).2)
  -- Frame + compose with flat Pre/Post shapes
  let Pre : Assertion :=
    erhOffsetRegs o ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** A
  let PostLi : Assertion :=
    erhOffsetRegs o ** (.x5 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A
  let Post : Assertion := PostLi
  have s0 := cpsTripleWithin_frameR
    (erhOffsetRegs o ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      simp only [erhOffsetRegs]
      repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l0
  have s0w : cpsTripleWithin 1 (B + 132) (B + 136) erhCr Pre PostLi := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp only [Pre, erhOffsetRegs] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [PostLi, erhOffsetRegs] at hq ⊢; xperm_chunked hq) s0
  -- BNE focuses x19+x5; frame the rest of offsets + x0 + A
  have s1 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ o.wdr) ** (.x21 ↦ᵣ o.con) ** (.x22 ↦ᵣ o.bdep) **
      (.x23 ↦ᵣ o.bexit) ** (.x9 ↦ᵣ o.end_) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h1nt
  have s1w : cpsTripleWithin 1 (B + 136) (B + 140) erhCr PostLi PostLi := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp only [PostLi, erhOffsetRegs] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [PostLi, erhOffsetRegs] at hq ⊢; xperm_chunked hq) s1
  have s01 := cpsTripleWithin_seq_same_cr s0w s1w
  -- BLTU x20,x19 focuses those two
  have s2 := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ o.con) ** (.x22 ↦ᵣ o.bdep) ** (.x23 ↦ᵣ o.bexit) **
      (.x9 ↦ᵣ o.end_) ** (.x5 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h2nt
  have s2w : cpsTripleWithin 1 (B + 140) (B + 144) erhCr PostLi PostLi := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp only [PostLi, erhOffsetRegs] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [PostLi, erhOffsetRegs] at hq ⊢; xperm_chunked hq) s2
  have s012 := cpsTripleWithin_seq_same_cr s01 s2w
  have s3 := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ o.dep) ** (.x22 ↦ᵣ o.bdep) ** (.x23 ↦ᵣ o.bexit) **
      (.x9 ↦ᵣ o.end_) ** (.x5 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h3nt
  have s3w : cpsTripleWithin 1 (B + 144) (B + 148) erhCr PostLi PostLi := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp only [PostLi, erhOffsetRegs] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [PostLi, erhOffsetRegs] at hq ⊢; xperm_chunked hq) s3
  have s0123 := cpsTripleWithin_seq_same_cr s012 s3w
  have s4 := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ o.dep) ** (.x20 ↦ᵣ o.wdr) ** (.x23 ↦ᵣ o.bexit) **
      (.x9 ↦ᵣ o.end_) ** (.x5 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h4nt
  have s4w : cpsTripleWithin 1 (B + 148) (B + 152) erhCr PostLi PostLi := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp only [PostLi, erhOffsetRegs] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [PostLi, erhOffsetRegs] at hq ⊢; xperm_chunked hq) s4
  have s01234 := cpsTripleWithin_seq_same_cr s0123 s4w
  have s5 := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ o.dep) ** (.x20 ↦ᵣ o.wdr) ** (.x21 ↦ᵣ o.con) **
      (.x9 ↦ᵣ o.end_) ** (.x5 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h5nt
  have s5w : cpsTripleWithin 1 (B + 152) (B + 156) erhCr PostLi PostLi := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp only [PostLi, erhOffsetRegs] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [PostLi, erhOffsetRegs] at hq ⊢; xperm_chunked hq) s5
  have s012345 := cpsTripleWithin_seq_same_cr s01234 s5w
  have s6 := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ o.dep) ** (.x20 ↦ᵣ o.wdr) ** (.x21 ↦ᵣ o.con) **
      (.x22 ↦ᵣ o.bdep) ** (.x5 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h6nt
  have s6w : cpsTripleWithin 1 (B + 156) (B + 160) erhCr PostLi Post := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp only [PostLi, erhOffsetRegs] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [Post, PostLi, erhOffsetRegs] at hq ⊢; xperm_chunked hq) s6
  have sAll := cpsTripleWithin_seq_same_cr s012345 s6w
  have hn' : ((((((1 + 1) + 1) + 1) + 1) + 1) + 1) = 7 := rfl
  rw [hn'] at sAll
  exact sAll

end EvmAsm.Codegen.ExecutionRequestsHashMono
