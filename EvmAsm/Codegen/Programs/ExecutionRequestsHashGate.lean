/-
  EvmAsm.Codegen.Programs.ExecutionRequestsHashGate

  One reusable 7-instruction fixed-list gate from `execution_requests_hash`
  validation prefix (GH #11578 rescope):

    SUB rdLen, hi, lo
    LI  rdStr, stride
    REMU rdR, rdLen, rdStr
    BNE rdR, x0, fail
    DIVU rdC, rdLen, rdStr
    LI/LUI rdCap, cap
    BLTU rdCap, rdC, fail

  Accept fallthrough iff `fixedListOkW bodyLen stride cap`.
  Deposit gate is the first of five (idx 40–46, LUI-cap 8192).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.RemuNat
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.ExecutionRequestsHashVal
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Evm64.EvmWordArith.MultiLimb

namespace EvmAsm.Codegen.ExecutionRequestsHashGate

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashVal
open EvmAsm.Evm64.EvmWord

set_option maxRecDepth 8000

/-- Concrete guest entry. -/
private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash

/-- Unfold `Program` so `GetElem` / length facts reduce. -/
private abbrev erhProgL : List Instr := executionRequestsHash_prog

private theorem erhProgL_len : erhProgL.length = 135 := by
  simp only [erhProgL, executionRequestsHash_prog]
  decide

private theorem erhProgL_bound : 4 * erhProgL.length < 2 ^ 64 := by
  rw [erhProgL_len]; norm_num

private abbrev erhCr : CodeReq := CodeReq.ofProg B erhProgL

/-- Singleton at index `k` ⊆ ofProg. -/
private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < erhProgL.length)
    (hins : erhProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → erhCr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at B A erhProgL k ins hA hk hins erhProgL_bound a i h

private def bneOffDeposit : BitVec 13 :=
  brOff (GuestAddrs.execution_requests_hash + 480)
    (GuestAddrs.execution_requests_hash + 172)

private def bltuOffDeposit : BitVec 13 :=
  brOff (GuestAddrs.execution_requests_hash + 480)
    (GuestAddrs.execution_requests_hash + 184)

private theorem bne_deposit_taken :
    (B + 172) + signExtend13 bneOffDeposit = B + 480 := by
  unfold B bneOffDeposit
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 172 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 172)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 172 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem bltu_deposit_taken :
    (B + 184) + signExtend13 bltuOffDeposit = B + 480 := by
  unfold B bltuOffDeposit
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 184 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 184)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 184 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- LUI imm=2 result equals 8192. -/
private theorem lui_imm2_eq_8192 :
    (((2 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 =
      (8192 : Word) := by decide

private theorem stride192_toNat : (192 : Word).toNat = 192 := by decide
private theorem cap8192_toNat : (8192 : Word).toNat = 8192 := by decide

/-! ## Accept path (fixedListOkW)

    Fuel 7; start B+160 (idx 40); exit B+188 (idx 47). -/

theorem deposit_gate_accept
    (hi lo v5old v6old v7old v28old : Word)
    (hok : fixedListOkW (hi - lo) (192 : Word) (8192 : Word))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 7 (B + 160) (B + 188) erhCr
      ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
        (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
        (.x6 ↦ᵣ (192 : Word)) **
        (.x7 ↦ᵣ rv64_divu (hi - lo) (192 : Word)) **
        (.x28 ↦ᵣ (8192 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A) := by
  have hstride : (192 : Word) ≠ 0 := by decide
  have hbody : (hi - lo).toNat % 192 = 0 := by
    simpa [fixedListOkW, stride192_toNat] using hok.1
  have hrem0 : rv64_remu (hi - lo) (192 : Word) = 0 :=
    (remu_eq_zero_iff_mod_eq_zero (hi - lo) (192 : Word) hstride).2 hbody
  have hcount_le : (hi - lo).toNat / 192 ≤ 8192 := by
    simpa [fixedListOkW, stride192_toNat, cap8192_toNat] using hok.2
  have hdiv := rv64_divu_toNat (hi - lo) (192 : Word) hstride
  have hnult : ¬ BitVec.ult (8192 : Word) (rv64_divu (hi - lo) (192 : Word)) := by
    intro hult
    have hlt : 8192 < (rv64_divu (hi - lo) (192 : Word)).toNat := by
      simpa [BitVec.ult] using hult
    have hdiv' : (rv64_divu (hi - lo) (192 : Word)).toNat =
        (hi - lo).toNat / 192 := by
      simpa [stride192_toNat] using hdiv
    rw [hdiv'] at hlt
    omega
  -- 0: SUB x5, x20, x19 @ B+160
  have h0 := sub_spec_gen_within .x5 .x20 .x19 hi lo v5old (B + 160) (by decide)
  rw [show (B + 160 : Word) + 4 = B + 164 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (mem_at 40 (.SUB .x5 .x20 .x19) (B + 160) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h0
  -- 1: LI x6, 192 @ B+164
  have h1 := li_spec_gen_within .x6 v6old (192 : Word) (B + 164) (by decide)
  rw [show (B + 164 : Word) + 4 = B + 168 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (mem_at 41 (.LI .x6 (192 : Word)) (B + 164) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h1
  -- 2: REMU x7, x5, x6 @ B+168
  have h2 := remu_spec_gen_within .x7 .x5 .x6 v7old (hi - lo) (192 : Word)
    (B + 168) (by decide)
  rw [show (B + 168 : Word) + 4 = B + 172 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (mem_at 42 (.REMU .x7 .x5 .x6) (B + 168) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h2
  -- 3: BNE x7, x0 → fail @ B+172 (ntaken)
  have h3br := bne_spec_gen_within .x7 .x0 bneOffDeposit
    (rv64_remu (hi - lo) (192 : Word)) (0 : Word) (B + 172)
  rw [bne_deposit_taken, show (B + 172 : Word) + 4 = B + 176 from by decide] at h3br
  have l3 := cpsBranchWithin_extend_code
    (mem_at 43 (.BNE .x7 .x0 bneOffDeposit) (B + 172) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h3br
  have h3nt := cpsBranchWithin_ntakenStripPure2 l3 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    have hne : rv64_remu (hi - lo) (192 : Word) ≠ 0 :=
      ((sepConj_pure_right _).1 hQ).2
    exact hne hrem0)
  -- 4: DIVU x7, x5, x6 @ B+176 — pre x7 = remu = 0
  have h4 := divu_spec_gen_within .x7 .x5 .x6
    (0 : Word) (hi - lo) (192 : Word) (B + 176) (by decide)
  rw [show (B + 176 : Word) + 4 = B + 180 from by decide] at h4
  have l4 := cpsTripleWithin_extend_code
    (mem_at 44 (.DIVU .x7 .x5 .x6) (B + 176) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h4
  -- 5: LUI x28, 2 → 8192 @ B+180
  have h5 := lui_spec_gen_within .x28 v28old (2 : BitVec 20) (B + 180) (by decide)
  rw [show (B + 180 : Word) + 4 = B + 184 from by decide] at h5
  have l5 := cpsTripleWithin_extend_code
    (mem_at 45 (.LUI .x28 (2 : BitVec 20)) (B + 180) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h5
  -- rewrite LUI post to 8192
  have l5' : cpsTripleWithin 1 (B + 180) (B + 184) erhCr
      (.x28 ↦ᵣ v28old) (.x28 ↦ᵣ (8192 : Word)) := by
    simpa [lui_imm2_eq_8192] using l5
  -- 6: BLTU x28, x7 → fail @ B+184 (ntaken)
  have h6br := bltu_spec_gen_within .x28 .x7 bltuOffDeposit
    (8192 : Word) (rv64_divu (hi - lo) (192 : Word)) (B + 184)
  rw [bltu_deposit_taken, show (B + 184 : Word) + 4 = B + 188 from by decide] at h6br
  have l6 := cpsBranchWithin_extend_code
    (mem_at 46 (.BLTU .x28 .x7 bltuOffDeposit) (B + 184) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h6br
  have h6nt := cpsBranchWithin_ntakenStripPure2 l6 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    have hult : BitVec.ult (8192 : Word) (rv64_divu (hi - lo) (192 : Word)) :=
      ((sepConj_pure_right _).1 hQ).2
    exact hnult hult)
  -- step 0 framed
  have s0 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l0
  -- Canonical full-state shape (right-assoc flat).
  let Pre0 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post0 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) ** (.x6 ↦ᵣ v6old) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post1 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post2 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) **
      (.x7 ↦ᵣ rv64_remu (hi - lo) (192 : Word)) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post3 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post4 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) **
      (.x7 ↦ᵣ rv64_divu (hi - lo) (192 : Word)) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post5 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) **
      (.x7 ↦ᵣ rv64_divu (hi - lo) (192 : Word)) **
      (.x28 ↦ᵣ (8192 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post6 : Assertion := Post5
  have s0w : cpsTripleWithin 1 (B + 160) (B + 164) erhCr Pre0 Post0 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Pre0] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post0] at hq ⊢; xperm_chunked hq) s0
  have s1 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l1
  have s1w : cpsTripleWithin 1 (B + 164) (B + 168) erhCr Post0 Post1 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post0] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post1] at hq ⊢; xperm_chunked hq) s1
  have s01 : cpsTripleWithin 2 (B + 160) (B + 168) erhCr Pre0 Post1 :=
    cpsTripleWithin_seq_same_cr s0w s1w
  have s2 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l2
  have s2w : cpsTripleWithin 1 (B + 168) (B + 172) erhCr Post1 Post2 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post1] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post2] at hq ⊢; xperm_chunked hq) s2
  have s012 : cpsTripleWithin 3 (B + 160) (B + 172) erhCr Pre0 Post2 :=
    cpsTripleWithin_seq_same_cr s01 s2w
  have s3 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) ** (.x28 ↦ᵣ v28old) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h3nt
  have s3w : cpsTripleWithin 1 (B + 172) (B + 176) erhCr Post2 Post3 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post2] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        -- remu = 0 after accept
        have : rv64_remu (hi - lo) (192 : Word) = 0 := hrem0
        simp only [Post3, this] at hq ⊢
        xperm_chunked hq) s3
  have s0123 : cpsTripleWithin 4 (B + 160) (B + 176) erhCr Pre0 Post3 :=
    cpsTripleWithin_seq_same_cr s012 s3w
  have s4 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l4
  have s4w : cpsTripleWithin 1 (B + 176) (B + 180) erhCr Post3 Post4 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post3] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post4] at hq ⊢; xperm_chunked hq) s4
  have s01234 : cpsTripleWithin 5 (B + 160) (B + 180) erhCr Pre0 Post4 :=
    cpsTripleWithin_seq_same_cr s0123 s4w
  have s5 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) **
      (.x7 ↦ᵣ rv64_divu (hi - lo) (192 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l5'
  have s5w : cpsTripleWithin 1 (B + 180) (B + 184) erhCr Post4 Post5 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post4] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post5] at hq ⊢; xperm_chunked hq) s5
  have s012345 : cpsTripleWithin 6 (B + 160) (B + 184) erhCr Pre0 Post5 :=
    cpsTripleWithin_seq_same_cr s01234 s5w
  have s6 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h6nt
  have s6w : cpsTripleWithin 1 (B + 184) (B + 188) erhCr Post5 Post6 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post5] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post6, Post5] at hq ⊢; xperm_chunked hq) s6
  exact cpsTripleWithin_seq_same_cr s012345 s6w

/-! ## Reject: REMU ≠ 0 → BNE taken to fail (fuel 4) -/

theorem deposit_gate_reject_remu
    (hi lo v5old v6old v7old v28old : Word)
    (hrem : rv64_remu (hi - lo) (192 : Word) ≠ 0)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 4 (B + 160) (B + 480) erhCr
      ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
        (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
        (.x6 ↦ᵣ (192 : Word)) **
        (.x7 ↦ᵣ rv64_remu (hi - lo) (192 : Word)) ** (.x28 ↦ᵣ v28old) **
        (.x0 ↦ᵣ (0 : Word)) ** A) := by
  -- 0 SUB
  have h0 := sub_spec_gen_within .x5 .x20 .x19 hi lo v5old (B + 160) (by decide)
  rw [show (B + 160 : Word) + 4 = B + 164 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (mem_at 40 (.SUB .x5 .x20 .x19) (B + 160) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h0
  -- 1 LI
  have h1 := li_spec_gen_within .x6 v6old (192 : Word) (B + 164) (by decide)
  rw [show (B + 164 : Word) + 4 = B + 168 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (mem_at 41 (.LI .x6 (192 : Word)) (B + 164) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h1
  -- 2 REMU
  have h2 := remu_spec_gen_within .x7 .x5 .x6 v7old (hi - lo) (192 : Word)
    (B + 168) (by decide)
  rw [show (B + 168 : Word) + 4 = B + 172 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (mem_at 42 (.REMU .x7 .x5 .x6) (B + 168) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h2
  -- 3 BNE taken
  have h3br := bne_spec_gen_within .x7 .x0 bneOffDeposit
    (rv64_remu (hi - lo) (192 : Word)) (0 : Word) (B + 172)
  rw [bne_deposit_taken, show (B + 172 : Word) + 4 = B + 176 from by decide] at h3br
  have l3 := cpsBranchWithin_extend_code
    (mem_at 43 (.BNE .x7 .x0 bneOffDeposit) (B + 172) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h3br
  have h3t := cpsBranchWithin_takenStripPure2 l3 (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    have heq : rv64_remu (hi - lo) (192 : Word) = 0 :=
      ((sepConj_pure_right _).1 hQ).2
    exact hrem heq)
  -- compose
  let Pre0 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
  let P1 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) ** (.x6 ↦ᵣ v6old) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
  let P2 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let P3 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) **
      (.x7 ↦ᵣ rv64_remu (hi - lo) (192 : Word)) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  have s0 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l0
  have s0w : cpsTripleWithin 1 (B + 160) (B + 164) erhCr Pre0 P1 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Pre0] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [P1] at hq ⊢; xperm_chunked hq) s0
  have s1 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l1
  have s1w : cpsTripleWithin 1 (B + 164) (B + 168) erhCr P1 P2 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [P1] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [P2] at hq ⊢; xperm_chunked hq) s1
  have s2 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l2
  have s2w : cpsTripleWithin 1 (B + 168) (B + 172) erhCr P2 P3 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [P2] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [P3] at hq ⊢; xperm_chunked hq) s2
  have s3 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) ** (.x28 ↦ᵣ v28old) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h3t
  have s3w : cpsTripleWithin 1 (B + 172) (B + 480) erhCr P3 P3 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [P3] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [P3] at hq ⊢; xperm_chunked hq) s3
  exact cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_seq_same_cr s0w s1w) s2w) s3w

/-! ## Reject: remu=0 but cap < count → BLTU taken to fail (fuel 7) -/

theorem deposit_gate_reject_cap
    (hi lo v5old v6old v7old v28old : Word)
    (hrem : rv64_remu (hi - lo) (192 : Word) = 0)
    (hcap : BitVec.ult (8192 : Word) (rv64_divu (hi - lo) (192 : Word)))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 7 (B + 160) (B + 480) erhCr
      ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
        (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
        (.x6 ↦ᵣ (192 : Word)) **
        (.x7 ↦ᵣ rv64_divu (hi - lo) (192 : Word)) **
        (.x28 ↦ᵣ (8192 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A) := by
  -- reuse accept path setup through BLTU, then taken
  have h0 := sub_spec_gen_within .x5 .x20 .x19 hi lo v5old (B + 160) (by decide)
  rw [show (B + 160 : Word) + 4 = B + 164 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (mem_at 40 (.SUB .x5 .x20 .x19) (B + 160) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h0
  have h1 := li_spec_gen_within .x6 v6old (192 : Word) (B + 164) (by decide)
  rw [show (B + 164 : Word) + 4 = B + 168 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (mem_at 41 (.LI .x6 (192 : Word)) (B + 164) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h1
  have h2 := remu_spec_gen_within .x7 .x5 .x6 v7old (hi - lo) (192 : Word)
    (B + 168) (by decide)
  rw [show (B + 168 : Word) + 4 = B + 172 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (mem_at 42 (.REMU .x7 .x5 .x6) (B + 168) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h2
  have h3br := bne_spec_gen_within .x7 .x0 bneOffDeposit
    (rv64_remu (hi - lo) (192 : Word)) (0 : Word) (B + 172)
  rw [bne_deposit_taken, show (B + 172 : Word) + 4 = B + 176 from by decide] at h3br
  have l3 := cpsBranchWithin_extend_code
    (mem_at 43 (.BNE .x7 .x0 bneOffDeposit) (B + 172) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h3br
  have h3nt := cpsBranchWithin_ntakenStripPure2 l3 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    have hne : rv64_remu (hi - lo) (192 : Word) ≠ 0 :=
      ((sepConj_pure_right _).1 hQ).2
    exact hne hrem)
  have h4 := divu_spec_gen_within .x7 .x5 .x6
    (0 : Word) (hi - lo) (192 : Word) (B + 176) (by decide)
  rw [show (B + 176 : Word) + 4 = B + 180 from by decide] at h4
  have l4 := cpsTripleWithin_extend_code
    (mem_at 44 (.DIVU .x7 .x5 .x6) (B + 176) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h4
  have h5 := lui_spec_gen_within .x28 v28old (2 : BitVec 20) (B + 180) (by decide)
  rw [show (B + 180 : Word) + 4 = B + 184 from by decide] at h5
  have l5 := cpsTripleWithin_extend_code
    (mem_at 45 (.LUI .x28 (2 : BitVec 20)) (B + 180) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h5
  have l5' : cpsTripleWithin 1 (B + 180) (B + 184) erhCr
      (.x28 ↦ᵣ v28old) (.x28 ↦ᵣ (8192 : Word)) := by
    simpa [lui_imm2_eq_8192] using l5
  have h6br := bltu_spec_gen_within .x28 .x7 bltuOffDeposit
    (8192 : Word) (rv64_divu (hi - lo) (192 : Word)) (B + 184)
  rw [bltu_deposit_taken, show (B + 184 : Word) + 4 = B + 188 from by decide] at h6br
  have l6 := cpsBranchWithin_extend_code
    (mem_at 46 (.BLTU .x28 .x7 bltuOffDeposit) (B + 184) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h6br
  have h6t := cpsBranchWithin_takenStripPure2 l6 (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    have hnult : ¬ BitVec.ult (8192 : Word) (rv64_divu (hi - lo) (192 : Word)) :=
      ((sepConj_pure_right _).1 hQ).2
    exact hnult hcap)
  -- compose (same Post shapes as accept through Post5, then taken to fail)
  let Pre0 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post0 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) ** (.x6 ↦ᵣ v6old) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post1 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post2 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) **
      (.x7 ↦ᵣ rv64_remu (hi - lo) (192 : Word)) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post3 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post4 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) **
      (.x7 ↦ᵣ rv64_divu (hi - lo) (192 : Word)) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let Post5 : Assertion :=
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) **
      (.x7 ↦ᵣ rv64_divu (hi - lo) (192 : Word)) **
      (.x28 ↦ᵣ (8192 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A)
  have s0 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l0
  have s0w : cpsTripleWithin 1 (B + 160) (B + 164) erhCr Pre0 Post0 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Pre0] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post0] at hq ⊢; xperm_chunked hq) s0
  have s1 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l1
  have s1w : cpsTripleWithin 1 (B + 164) (B + 168) erhCr Post0 Post1 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post0] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post1] at hq ⊢; xperm_chunked hq) s1
  have s2 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l2
  have s2w : cpsTripleWithin 1 (B + 168) (B + 172) erhCr Post1 Post2 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post1] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post2] at hq ⊢; xperm_chunked hq) s2
  have s3 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) ** (.x28 ↦ᵣ v28old) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h3nt
  have s3w : cpsTripleWithin 1 (B + 172) (B + 176) erhCr Post2 Post3 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post2] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post3, hrem] at hq ⊢; xperm_chunked hq) s3
  have s4 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l4
  have s4w : cpsTripleWithin 1 (B + 176) (B + 180) erhCr Post3 Post4 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post3] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post4] at hq ⊢; xperm_chunked hq) s4
  have s5 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) **
      (.x7 ↦ᵣ rv64_divu (hi - lo) (192 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l5'
  have s5w : cpsTripleWithin 1 (B + 180) (B + 184) erhCr Post4 Post5 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post4] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post5] at hq ⊢; xperm_chunked hq) s5
  have s6 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ hi) ** (.x19 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ (192 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by
      repeat' first
        | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h6t
  have s6w : cpsTripleWithin 1 (B + 184) (B + 480) erhCr Post5 Post5 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Post5] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Post5] at hq ⊢; xperm_chunked hq) s6
  exact cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_seq_same_cr
        (cpsTripleWithin_seq_same_cr
          (cpsTripleWithin_seq_same_cr
            (cpsTripleWithin_seq_same_cr s0w s1w) s2w) s3w) s4w) s5w) s6w

end EvmAsm.Codegen.ExecutionRequestsHashGate
