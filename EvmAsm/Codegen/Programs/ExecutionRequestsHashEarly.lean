/-
  ExecutionRequestsHashEarly — setup MVs + len≥20 gate.

  Geometry (executionRequestsHash_prog):
    B+52  MV s0,a0; MV s1,a1; MV s2,a2   -- listBase / len / out
    B+64  LI t0,20
    B+68  BLTU s1,t0,fail                 -- accept when ¬ult len 20

  Parent: #11578 rescope.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.ExecutionRequestsHashBgv
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.ExecutionRequestsHashEarly

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashBgv

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash
private abbrev erhProgL : List Instr := executionRequestsHash_prog

private theorem erhProgL_len : erhProgL.length = 135 := by
  simp only [erhProgL, executionRequestsHash_prog]; decide

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < erhProgL.length)
    (hins : erhProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i :=
  erhMem A k ins hk hA hins

private def bltuOff68 : BitVec 13 :=
  brOff (GuestAddrs.execution_requests_hash + 480)
    (GuestAddrs.execution_requests_hash + 68)

private theorem bltu_taken_68 :
    (B + 68) + signExtend13 bltuOff68 = B + 480 := by
  unfold B bltuOff68 brOff signExtend13; decide

/-- Three ABI MVs: B+52 → B+64. Fuel 3. -/
theorem erh_setup_mvs
    (listBase endW outW v8 v9 v18 : Word)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 3 (B + 52) (B + 64) fullCode
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** A)
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endW) ** (.x18 ↦ᵣ outW) ** A) := by
  -- MV x8,x10 — focus x10+x8
  have h0 := mv_spec_gen_within .x8 .x10 listBase v8 (B + 52) (by decide)
  rw [show (B + 52 : Word) + 4 = B + 56 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (mem_at 13 (.MV .x8 .x10) (B + 52) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h0
  let F0 : Assertion :=
    (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** A
  have f0 : F0.pcFree := by
    simp only [F0]
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hA)
  have s0 := cpsTripleWithin_frameR F0 f0 l0
  have s0w : cpsTripleWithin 1 (B + 52) (B + 56) fullCode
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** A)
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** A) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [F0]; xperm_chunked hp)
      (fun _ hq => by simp only [F0] at hq; xperm_chunked hq) s0
  -- MV x9,x11 — focus x11+x9
  have h1 := mv_spec_gen_within .x9 .x11 endW v9 (B + 56) (by decide)
  rw [show (B + 56 : Word) + 4 = B + 60 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (mem_at 14 (.MV .x9 .x11) (B + 56) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h1
  let F1 : Assertion :=
    (.x10 ↦ᵣ listBase) ** (.x12 ↦ᵣ outW) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ v18) ** A
  have f1 : F1.pcFree := by
    simp only [F1]
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hA)
  have s1 := cpsTripleWithin_frameR F1 f1 l1
  have s1w : cpsTripleWithin 1 (B + 56) (B + 60) fullCode
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** A)
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endW) ** (.x18 ↦ᵣ v18) ** A) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [F1]; xperm_chunked hp)
      (fun _ hq => by simp only [F1] at hq; xperm_chunked hq) s1
  -- MV x18,x12 — focus x12+x18
  have h2 := mv_spec_gen_within .x18 .x12 outW v18 (B + 60) (by decide)
  rw [show (B + 60 : Word) + 4 = B + 64 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (mem_at 15 (.MV .x18 .x12) (B + 60) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h2
  let F2 : Assertion :=
    (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endW) ** A
  have f2 : F2.pcFree := by
    simp only [F2]
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hA)
  have s2 := cpsTripleWithin_frameR F2 f2 l2
  have s2w : cpsTripleWithin 1 (B + 60) (B + 64) fullCode
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endW) ** (.x18 ↦ᵣ v18) ** A)
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endW) ** (.x18 ↦ᵣ outW) ** A) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [F2]; xperm_chunked hp)
      (fun _ hq => by simp only [F2] at hq; xperm_chunked hq) s2
  have c01 := cpsTripleWithin_seq_same_cr s0w s1w
  exact cpsTripleWithin_seq_same_cr c01 s2w

/-- Len≥20 accept: LI+BLTU B+64 → B+72 under ¬ult endW 20. Fuel 2. -/
theorem erh_early_len_accept
    (endW v5 : Word)
    (h_ge : ¬ BitVec.ult endW (20 : Word))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 2 (B + 64) (B + 72) fullCode
      ((.x9 ↦ᵣ endW) ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x9 ↦ᵣ endW) ** (.x5 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A) := by
  -- LI x5, 20 — focus x5
  have h0 := li_spec_gen_within .x5 v5 (20 : Word) (B + 64) (by decide)
  rw [show (B + 64 : Word) + 4 = B + 68 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (mem_at 16 (.LI .x5 (20 : Word)) (B + 64) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h0
  let F0 : Assertion := (.x9 ↦ᵣ endW) ** (.x0 ↦ᵣ (0 : Word)) ** A
  have f0 : F0.pcFree := by
    simp only [F0]
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hA)
  have s0 := cpsTripleWithin_frameR F0 f0 l0
  have s0w : cpsTripleWithin 1 (B + 64) (B + 68) fullCode
      ((.x9 ↦ᵣ endW) ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x9 ↦ᵣ endW) ** (.x5 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [F0]; xperm_chunked hp)
      (fun _ hq => by simp only [F0] at hq; xperm_chunked hq) s0
  -- BLTU x9, x5 ntaken — focus x9+x5
  have h1br := bltu_spec_gen_within .x9 .x5 bltuOff68
    endW (20 : Word) (B + 68)
  rw [bltu_taken_68, show (B + 68 : Word) + 4 = B + 72 from by decide] at h1br
  have l1 := cpsBranchWithin_extend_code
    (mem_at 17 (.BLTU .x9 .x5 bltuOff68) (B + 68) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) h1br
  have h1nt := cpsBranchWithin_ntakenStripPure2 l1 (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact h_ge ((sepConj_pure_right _).1 hQ).2)
  let F1 : Assertion := (.x0 ↦ᵣ (0 : Word)) ** A
  have f1 : F1.pcFree := by
    simp only [F1]
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hA)
  have s1 := cpsTripleWithin_frameR F1 f1 h1nt
  have s1w : cpsTripleWithin 1 (B + 68) (B + 72) fullCode
      ((.x9 ↦ᵣ endW) ** (.x5 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x9 ↦ᵣ endW) ** (.x5 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** A) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [F1]; xperm_chunked hp)
      (fun _ hq => by simp only [F1] at hq; xperm_chunked hq) s1
  exact cpsTripleWithin_seq_same_cr s0w s1w

end EvmAsm.Codegen.ExecutionRequestsHashEarly
