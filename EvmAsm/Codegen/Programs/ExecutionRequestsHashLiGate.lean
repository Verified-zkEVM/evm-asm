/-
  EvmAsm.Codegen.Programs.ExecutionRequestsHashLiGate

  LI-cap 7-insn fixed-list gates for `execution_requests_hash` validation
  (GH #11578). Deposit is LUI-cap in Gate.lean; four LI-cap kinds here:

    withdrawal     idx 47  stride 76   cap 16   hi=x21 lo=x20
    consolidation  idx 54  stride 116  cap 2    hi=x22 lo=x21
    builderDeposit idx 61  stride 184  cap 64   hi=x23 lo=x22
    builderExit    idx 68  stride 68   cap 16   hi=x9  lo=x23
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

namespace EvmAsm.Codegen.ExecutionRequestsHashLiGate

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashVal
open EvmAsm.Evm64.EvmWord

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

/-- PC step `B+n → B+(n+4)` for the LI-cap gate window [188,300]. -/
private theorem pc_step (n : Nat) (hn : n ∈ [188, 192, 196, 200, 204, 208, 212,
    216, 220, 224, 228, 232, 236, 240, 244, 248, 252, 256, 260, 264, 268,
    272, 276, 280, 284, 288, 292, 296]) :
    (B + BitVec.ofNat 64 n) + 4 = B + BitVec.ofNat 64 (n + 4) := by
  fin_cases hn <;> (unfold B; decide)

private theorem bne_taken_200 :
    (B + BitVec.ofNat 64 200) + signExtend13 (bneOffAt 200) = B + 480 := by
  unfold B bneOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 200 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 200)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 200 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bltu_taken_212 :
    (B + BitVec.ofNat 64 212) + signExtend13 (bltuOffAt 212) = B + 480 := by
  unfold B bltuOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 212 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 212)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 212 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bne_taken_228 :
    (B + BitVec.ofNat 64 228) + signExtend13 (bneOffAt 228) = B + 480 := by
  unfold B bneOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 228 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 228)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 228 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bltu_taken_240 :
    (B + BitVec.ofNat 64 240) + signExtend13 (bltuOffAt 240) = B + 480 := by
  unfold B bltuOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 240 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 240)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 240 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bne_taken_256 :
    (B + BitVec.ofNat 64 256) + signExtend13 (bneOffAt 256) = B + 480 := by
  unfold B bneOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 256 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 256)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 256 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bltu_taken_268 :
    (B + BitVec.ofNat 64 268) + signExtend13 (bltuOffAt 268) = B + 480 := by
  unfold B bltuOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 268 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 268)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 268 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bne_taken_284 :
    (B + BitVec.ofNat 64 284) + signExtend13 (bneOffAt 284) = B + 480 := by
  unfold B bneOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 284 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 284)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 284 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem bltu_taken_296 :
    (B + BitVec.ofNat 64 296) + signExtend13 (bltuOffAt 296) = B + 480 := by
  unfold B bltuOffAt
  change BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 296 +
      signExtend13 (brOff (GuestAddrs.execution_requests_hash + 480)
        (GuestAddrs.execution_requests_hash + 296)) =
    BitVec.ofNat 64 GuestAddrs.execution_requests_hash + BitVec.ofNat 64 480
  exact brOff_correct_base_off GuestAddrs.execution_requests_hash 296 480
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## Shared accept body for LI-cap gates

    Parameterized by start byte offset `s` (= 4 * idx) and concrete hi/lo regs. -/

private theorem li_cap_accept_at
    (s : Nat)
    (hiR loR : Reg)
    (hi lo stride cap : Word)
    (v5old v6old v7old v28old : Word)
    (hs4 : 4 * (s / 4) = s)
    (hk0 : s / 4 < 135)
    (hk1 : s / 4 + 1 < 135)
    (hk2 : s / 4 + 2 < 135)
    (hk3 : s / 4 + 3 < 135)
    (hk4 : s / 4 + 4 < 135)
    (hk5 : s / 4 + 5 < 135)
    (hk6 : s / 4 + 6 < 135)
    (h0 : erhProgL[s / 4]'hk0 = .SUB .x5 hiR loR)
    (h1 : erhProgL[s / 4 + 1]'hk1 = .LI .x6 stride)
    (h2 : erhProgL[s / 4 + 2]'hk2 = .REMU .x7 .x5 .x6)
    (h3 : erhProgL[s / 4 + 3]'hk3 = .BNE .x7 .x0 (bneOffAt (s + 12)))
    (h4 : erhProgL[s / 4 + 4]'hk4 = .DIVU .x7 .x5 .x6)
    (h5 : erhProgL[s / 4 + 5]'hk5 = .LI .x28 cap)
    (h6 : erhProgL[s / 4 + 6]'hk6 = .BLTU .x28 .x7 (bltuOffAt (s + 24)))
    (p0 : (B + BitVec.ofNat 64 s) + 4 = B + BitVec.ofNat 64 (s + 4))
    (p1 : (B + BitVec.ofNat 64 (s + 4)) + 4 = B + BitVec.ofNat 64 (s + 8))
    (p2 : (B + BitVec.ofNat 64 (s + 8)) + 4 = B + BitVec.ofNat 64 (s + 12))
    (p3 : (B + BitVec.ofNat 64 (s + 12)) + 4 = B + BitVec.ofNat 64 (s + 16))
    (p4 : (B + BitVec.ofNat 64 (s + 16)) + 4 = B + BitVec.ofNat 64 (s + 20))
    (p5 : (B + BitVec.ofNat 64 (s + 20)) + 4 = B + BitVec.ofNat 64 (s + 24))
    (p6 : (B + BitVec.ofNat 64 (s + 24)) + 4 = B + BitVec.ofNat 64 (s + 28))
    (hbne : (B + BitVec.ofNat 64 (s + 12)) + signExtend13 (bneOffAt (s + 12)) =
      B + 480)
    (hbltu : (B + BitVec.ofNat 64 (s + 24)) + signExtend13 (bltuOffAt (s + 24)) =
      B + 480)
    (hok : fixedListOkW (hi - lo) stride cap)
    (hstride : stride ≠ 0)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 7 (B + BitVec.ofNat 64 s) (B + BitVec.ofNat 64 (s + 28)) erhCr
      ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
        (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
        (.x6 ↦ᵣ stride) **
        (.x7 ↦ᵣ rv64_divu (hi - lo) stride) **
        (.x28 ↦ᵣ cap) ** (.x0 ↦ᵣ (0 : Word)) ** A) := by
  have hrem0 : rv64_remu (hi - lo) stride = 0 :=
    (remu_eq_zero_iff_mod_eq_zero (hi - lo) stride hstride).2 hok.1
  have hcap_le : ¬ BitVec.ult cap (rv64_divu (hi - lo) stride) := by
    have hdiv := rv64_divu_toNat (hi - lo) stride hstride
    have hle : (hi - lo).toNat / stride.toNat ≤ cap.toNat := hok.2
    rw [← hdiv] at hle
    intro hult
    have : cap.toNat < (rv64_divu (hi - lo) stride).toNat := by
      simpa [BitVec.ult] using hult
    omega
  -- 0 SUB
  have hsub := sub_spec_gen_within .x5 hiR loR hi lo v5old
    (B + BitVec.ofNat 64 s) (by decide)
  rw [p0] at hsub
  have l0 := cpsTripleWithin_extend_code
    (mem_at (s / 4) (.SUB .x5 hiR loR) (B + BitVec.ofNat 64 s)
      (congrArg (fun n => B + BitVec.ofNat 64 n) hs4.symm) hk0 h0) hsub
  -- 1 LI stride
  have hli1 := li_spec_gen_within .x6 v6old stride
    (B + BitVec.ofNat 64 (s + 4)) (by decide)
  rw [p1] at hli1
  have l1 := cpsTripleWithin_extend_code
    (mem_at (s / 4 + 1) (.LI .x6 stride) (B + BitVec.ofNat 64 (s + 4))
      (congrArg (fun n => B + BitVec.ofNat 64 n) (by omega : s + 4 = 4 * (s / 4 + 1)))
      hk1 h1) hli1
  -- 2 REMU
  have hrem := remu_spec_gen_within .x7 .x5 .x6 v7old (hi - lo) stride
    (B + BitVec.ofNat 64 (s + 8)) (by decide)
  rw [p2] at hrem
  have l2 := cpsTripleWithin_extend_code
    (mem_at (s / 4 + 2) (.REMU .x7 .x5 .x6) (B + BitVec.ofNat 64 (s + 8))
      (congrArg (fun n => B + BitVec.ofNat 64 n) (by omega : s + 8 = 4 * (s / 4 + 2)))
      hk2 h2) hrem
  -- 3 BNE ntaken
  have h3br := bne_spec_gen_within .x7 .x0 (bneOffAt (s + 12))
    (rv64_remu (hi - lo) stride) (0 : Word) (B + BitVec.ofNat 64 (s + 12))
  rw [hbne, p3] at h3br
  have l3 := cpsBranchWithin_extend_code
    (mem_at (s / 4 + 3) (.BNE .x7 .x0 (bneOffAt (s + 12)))
      (B + BitVec.ofNat 64 (s + 12))
      (congrArg (fun n => B + BitVec.ofNat 64 n) (by omega : s + 12 = 4 * (s / 4 + 3)))
      hk3 h3) h3br
  have h3nt := cpsBranchWithin_ntakenStripPure2 l3 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    have hne : rv64_remu (hi - lo) stride ≠ 0 :=
      ((sepConj_pure_right _).1 hQ).2
    exact hne hrem0)
  -- 4 DIVU
  have hdiv := divu_spec_gen_within .x7 .x5 .x6
    (0 : Word) (hi - lo) stride (B + BitVec.ofNat 64 (s + 16)) (by decide)
  rw [p4] at hdiv
  have l4 := cpsTripleWithin_extend_code
    (mem_at (s / 4 + 4) (.DIVU .x7 .x5 .x6) (B + BitVec.ofNat 64 (s + 16))
      (congrArg (fun n => B + BitVec.ofNat 64 n) (by omega : s + 16 = 4 * (s / 4 + 4)))
      hk4 h4) hdiv
  -- 5 LI cap
  have hli5 := li_spec_gen_within .x28 v28old cap
    (B + BitVec.ofNat 64 (s + 20)) (by decide)
  rw [p5] at hli5
  have l5 := cpsTripleWithin_extend_code
    (mem_at (s / 4 + 5) (.LI .x28 cap) (B + BitVec.ofNat 64 (s + 20))
      (congrArg (fun n => B + BitVec.ofNat 64 n) (by omega : s + 20 = 4 * (s / 4 + 5)))
      hk5 h5) hli5
  -- 6 BLTU ntaken
  have h6br := bltu_spec_gen_within .x28 .x7 (bltuOffAt (s + 24))
    cap (rv64_divu (hi - lo) stride) (B + BitVec.ofNat 64 (s + 24))
  rw [hbltu, p6] at h6br
  have l6 := cpsBranchWithin_extend_code
    (mem_at (s / 4 + 6) (.BLTU .x28 .x7 (bltuOffAt (s + 24)))
      (B + BitVec.ofNat 64 (s + 24))
      (congrArg (fun n => B + BitVec.ofNat 64 n) (by omega : s + 24 = 4 * (s / 4 + 6)))
      hk6 h6) h6br
  have h6nt := cpsBranchWithin_ntakenStripPure2 l6 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    have hult : BitVec.ult cap (rv64_divu (hi - lo) stride) :=
      ((sepConj_pure_right _).1 hQ).2
    exact hcap_le hult)
  -- compose
  let Pre0 : Assertion :=
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
  let P1 : Assertion :=
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) ** (.x6 ↦ᵣ v6old) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
  let P2 : Assertion :=
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ stride) ** (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let P3 : Assertion :=
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ stride) **
      (.x7 ↦ᵣ rv64_remu (hi - lo) stride) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let P4 : Assertion :=
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ stride) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let P5 : Assertion :=
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ stride) **
      (.x7 ↦ᵣ rv64_divu (hi - lo) stride) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
  let P6 : Assertion :=
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ stride) **
      (.x7 ↦ᵣ rv64_divu (hi - lo) stride) **
      (.x28 ↦ᵣ cap) ** (.x0 ↦ᵣ (0 : Word)) ** A)
  have s0 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l0
  have s0w : cpsTripleWithin 1 (B + BitVec.ofNat 64 s)
      (B + BitVec.ofNat 64 (s + 4)) erhCr Pre0 P1 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Pre0] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [P1] at hq ⊢; xperm_chunked hq) s0
  have s1 := cpsTripleWithin_frameR
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l1
  have s1w : cpsTripleWithin 1 (B + BitVec.ofNat 64 (s + 4))
      (B + BitVec.ofNat 64 (s + 8)) erhCr P1 P2 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [P1] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [P2] at hq ⊢; xperm_chunked hq) s1
  have s2 := cpsTripleWithin_frameR
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l2
  have s2w : cpsTripleWithin 1 (B + BitVec.ofNat 64 (s + 8))
      (B + BitVec.ofNat 64 (s + 12)) erhCr P2 P3 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [P2] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [P3] at hq ⊢; xperm_chunked hq) s2
  have s3 := cpsTripleWithin_frameR
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ stride) ** (.x28 ↦ᵣ v28old) ** A)
    (by repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h3nt
  have s3w : cpsTripleWithin 1 (B + BitVec.ofNat 64 (s + 12))
      (B + BitVec.ofNat 64 (s + 16)) erhCr P3 P4 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [P3] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [P4, hrem0] at hq ⊢; xperm_chunked hq) s3
  have s4 := cpsTripleWithin_frameR
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x28 ↦ᵣ v28old) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l4
  have s4w : cpsTripleWithin 1 (B + BitVec.ofNat 64 (s + 16))
      (B + BitVec.ofNat 64 (s + 20)) erhCr P4 P5 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [P4] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [P5] at hq ⊢; xperm_chunked hq) s4
  have s5 := cpsTripleWithin_frameR
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ stride) **
      (.x7 ↦ᵣ rv64_divu (hi - lo) stride) **
      (.x0 ↦ᵣ (0 : Word)) ** A)
    (by repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) l5
  have s5w : cpsTripleWithin 1 (B + BitVec.ofNat 64 (s + 20))
      (B + BitVec.ofNat 64 (s + 24)) erhCr P5 P6 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [P5] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [P6] at hq ⊢; xperm_chunked hq) s5
  have s6 := cpsTripleWithin_frameR
    ((hiR ↦ᵣ hi) ** (loR ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
      (.x6 ↦ᵣ stride) ** (.x0 ↦ᵣ (0 : Word)) ** A)
    (by repeat' first | exact hA | exact pcFree_regIs | apply pcFree_sepConj) h6nt
  have s6w : cpsTripleWithin 1 (B + BitVec.ofNat 64 (s + 24))
      (B + BitVec.ofNat 64 (s + 28)) erhCr P6 P6 := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [P6] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [P6] at hq ⊢; xperm_chunked hq) s6
  exact cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_seq_same_cr
        (cpsTripleWithin_seq_same_cr
          (cpsTripleWithin_seq_same_cr
            (cpsTripleWithin_seq_same_cr s0w s1w) s2w) s3w) s4w) s5w) s6w

/-! ## Public wrappers — four LI-cap kinds -/

/-- State the public triples with `BitVec.ofNat` PCs so they match `li_cap_accept_at`. -/
theorem withdrawal_gate_accept
    (hi lo v5old v6old v7old v28old : Word)
    (hok : fixedListOkW (hi - lo) (76 : Word) (16 : Word))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 7 (B + BitVec.ofNat 64 188) (B + BitVec.ofNat 64 216) erhCr
      ((.x21 ↦ᵣ hi) ** (.x20 ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
        (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x21 ↦ᵣ hi) ** (.x20 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
        (.x6 ↦ᵣ (76 : Word)) **
        (.x7 ↦ᵣ rv64_divu (hi - lo) (76 : Word)) **
        (.x28 ↦ᵣ (16 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A) :=
  li_cap_accept_at 188 .x21 .x20 hi lo (76 : Word) (16 : Word)
    v5old v6old v7old v28old
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (pc_step 188 (by decide)) (pc_step 192 (by decide)) (pc_step 196 (by decide))
    (pc_step 200 (by decide)) (pc_step 204 (by decide)) (pc_step 208 (by decide))
    (pc_step 212 (by decide))
    bne_taken_200 bltu_taken_212
    hok (by decide) A hA

theorem consolidation_gate_accept
    (hi lo v5old v6old v7old v28old : Word)
    (hok : fixedListOkW (hi - lo) (116 : Word) (2 : Word))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 7 (B + BitVec.ofNat 64 216) (B + BitVec.ofNat 64 244) erhCr
      ((.x22 ↦ᵣ hi) ** (.x21 ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
        (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x22 ↦ᵣ hi) ** (.x21 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
        (.x6 ↦ᵣ (116 : Word)) **
        (.x7 ↦ᵣ rv64_divu (hi - lo) (116 : Word)) **
        (.x28 ↦ᵣ (2 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A) :=
  li_cap_accept_at 216 .x22 .x21 hi lo (116 : Word) (2 : Word)
    v5old v6old v7old v28old
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (pc_step 216 (by decide)) (pc_step 220 (by decide)) (pc_step 224 (by decide))
    (pc_step 228 (by decide)) (pc_step 232 (by decide)) (pc_step 236 (by decide))
    (pc_step 240 (by decide))
    bne_taken_228 bltu_taken_240
    hok (by decide) A hA

theorem builder_deposit_gate_accept
    (hi lo v5old v6old v7old v28old : Word)
    (hok : fixedListOkW (hi - lo) (184 : Word) (64 : Word))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 7 (B + BitVec.ofNat 64 244) (B + BitVec.ofNat 64 272) erhCr
      ((.x23 ↦ᵣ hi) ** (.x22 ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
        (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x23 ↦ᵣ hi) ** (.x22 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
        (.x6 ↦ᵣ (184 : Word)) **
        (.x7 ↦ᵣ rv64_divu (hi - lo) (184 : Word)) **
        (.x28 ↦ᵣ (64 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A) :=
  li_cap_accept_at 244 .x23 .x22 hi lo (184 : Word) (64 : Word)
    v5old v6old v7old v28old
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (pc_step 244 (by decide)) (pc_step 248 (by decide)) (pc_step 252 (by decide))
    (pc_step 256 (by decide)) (pc_step 260 (by decide)) (pc_step 264 (by decide))
    (pc_step 268 (by decide))
    bne_taken_256 bltu_taken_268
    hok (by decide) A hA

theorem builder_exit_gate_accept
    (hi lo v5old v6old v7old v28old : Word)
    (hok : fixedListOkW (hi - lo) (68 : Word) (16 : Word))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 7 (B + BitVec.ofNat 64 272) (B + BitVec.ofNat 64 300) erhCr
      ((.x9 ↦ᵣ hi) ** (.x23 ↦ᵣ lo) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
        (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x9 ↦ᵣ hi) ** (.x23 ↦ᵣ lo) ** (.x5 ↦ᵣ (hi - lo)) **
        (.x6 ↦ᵣ (68 : Word)) **
        (.x7 ↦ᵣ rv64_divu (hi - lo) (68 : Word)) **
        (.x28 ↦ᵣ (16 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A) :=
  li_cap_accept_at 272 .x9 .x23 hi lo (68 : Word) (16 : Word)
    v5old v6old v7old v28old
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (pc_step 272 (by decide)) (pc_step 276 (by decide)) (pc_step 280 (by decide))
    (pc_step 284 (by decide)) (pc_step 288 (by decide)) (pc_step 292 (by decide))
    (pc_step 296 (by decide))
    bne_taken_284 bltu_taken_296
    hok (by decide) A hA

end EvmAsm.Codegen.ExecutionRequestsHashLiGate
