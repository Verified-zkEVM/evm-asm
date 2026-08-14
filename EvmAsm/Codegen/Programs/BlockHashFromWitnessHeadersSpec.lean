/-
  EvmAsm.Codegen.Programs.BlockHashFromWitnessHeadersSpec

  Whole-routine contract for `blockhash_from_witness_headers` on the
  documented empty-section miss domain.  The routine's two external calls are
  already rowed `.proven`: `header_extract_number` and `zkvm_keccak256`.
  The nonempty scan remains outside this first startability tranche.
-/

import EvmAsm.Codegen.Programs.BlockHashPredicates
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Codegen.BlockHashFromWitnessHeadersSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

abbrev B : Word := (GuestAddrs.blockhash_from_witness_headers : Word)
abbrev prog : List Instr := blockhashFromWitnessHeaders_prog
abbrev code : CodeReq := CodeReq.ofProg B prog

abbrev frame : FrameDesc :=
  [ (.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12)),
    (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
    (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)),
    (.x21, (48 : BitVec 12)), (.x22, (56 : BitVec 12)),
    (.x23, (64 : BitVec 12)) ]

abbrev body : List Instr := (prog.drop 10).take 56

theorem prog_length : prog.length = 77 := by decide
theorem frame_length : frame.length = 9 := by decide
theorem body_length : body.length = 56 := by decide

private theorem prog_bound : 4 * prog.length < 2 ^ 64 := by
  rw [prog_length]
  norm_num

private theorem body_decomposition :
    abiFrameProg (-80 : BitVec 12) (80 : BitVec 12) frame body = prog := by
  decide

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < prog.length)
    (hins : prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → code a = some i :=
  fun a i h => CodeReq.ofProg_mem_at B A prog k ins hA hk hins
    prog_bound a i h

local macro "pcf" : tactic =>
  `(tactic| repeat' first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact bytesRegion_pcFree _ _
      | assumption)

private theorem beq_same_absurd {r1 r2 : Reg} {v : Word} :
    ∀ hp, (((r1 : Reg) ↦ᵣ v) ** ((r2 : Reg) ↦ᵣ v) ** ⌜v ≠ v⌝) hp → False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  exact hP.2 rfl

/-! The first six body instructions move the ABI arguments into the saved
    registers used by the scan.  On the empty-section domain the following
    BEQ is taken before any scan instruction or callee is reached. -/

theorem empty_body
    (newSp target sectionPtr outHash outOffset outLength : Word)
    (vals : Reg → Word)
    (hsec : sectionPtr = 0) :
    cpsTripleWithin 8 (B + 40) (B + 264) code
      ((.x2 ↦ᵣ newSp) ** regsAt frame vals **
        ((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ sectionPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x0 ↦ᵣ (0 : Word))))
      ((.x2 ↦ᵣ newSp) ** regsOwnAt frame **
        ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ sectionPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x0 ↦ᵣ (0 : Word)))) := by
  subst hsec
  let vals1 : Reg → Word := fun r => if r = .x23 then target else vals r
  let vals2 : Reg → Word := fun r => if r = .x8 then 0 else vals1 r
  let vals3 : Reg → Word := fun r => if r = .x9 then 0 else vals2 r
  let vals4 : Reg → Word := fun r => if r = .x18 then outHash else vals3 r
  let vals5 : Reg → Word := fun r => if r = .x19 then outOffset else vals4 r
  let vals6 : Reg → Word := fun r => if r = .x20 then outLength else vals5 r
  let f0 : FrameDesc :=
    [ (.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32),
      (.x20, 40), (.x21, 48), (.x22, 56) ]
  let f1 : FrameDesc :=
    [ (.x1, 0), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40),
      (.x21, 48), (.x22, 56), (.x23, 64) ]
  let f2 : FrameDesc :=
    [ (.x1, 0), (.x8, 8), (.x18, 24), (.x19, 32), (.x20, 40),
      (.x21, 48), (.x22, 56), (.x23, 64) ]
  let f3 : FrameDesc :=
    [ (.x1, 0), (.x8, 8), (.x9, 16), (.x19, 32), (.x20, 40),
      (.x21, 48), (.x22, 56), (.x23, 64) ]
  let f4 : FrameDesc :=
    [ (.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x20, 40),
      (.x21, 48), (.x22, 56), (.x23, 64) ]
  let f5 : FrameDesc :=
    [ (.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32),
      (.x21, 48), (.x22, 56), (.x23, 64) ]
  have h0 := mv_spec_gen_within .x23 .x10 target (vals .x23) (B + 40) (by decide)
  have h1 := mv_spec_gen_within .x8 .x11 (0 : Word) (vals .x8) (B + 44) (by decide)
  have h2 := mv_spec_gen_within .x9 .x12 (0 : Word) (vals .x9) (B + 48) (by decide)
  have h3 := mv_spec_gen_within .x18 .x13 outHash (vals .x18) (B + 52) (by decide)
  have h4 := mv_spec_gen_within .x19 .x14 outOffset (vals .x19) (B + 56) (by decide)
  have h5 := mv_spec_gen_within .x20 .x15 outLength (vals .x20) (B + 60) (by decide)
  have h0' := cpsTripleWithin_extend_code
    (mem_at 10 (.MV .x23 .x10) (B + 40) (by decide)
      (by rw [prog_length]; decide) (by rfl)) h0
  have h1' := cpsTripleWithin_extend_code
    (mem_at 11 (.MV .x8 .x11) (B + 44) (by decide)
      (by rw [prog_length]; decide) (by rfl)) h1
  have h2' := cpsTripleWithin_extend_code
    (mem_at 12 (.MV .x9 .x12) (B + 48) (by decide)
      (by rw [prog_length]; decide) (by rfl)) h2
  have h3' := cpsTripleWithin_extend_code
    (mem_at 13 (.MV .x18 .x13) (B + 52) (by decide)
      (by rw [prog_length]; decide) (by rfl)) h3
  have h4' := cpsTripleWithin_extend_code
    (mem_at 14 (.MV .x19 .x14) (B + 56) (by decide)
      (by rw [prog_length]; decide) (by rfl)) h4
  have h5' := cpsTripleWithin_extend_code
    (mem_at 15 (.MV .x20 .x15) (B + 60) (by decide)
      (by rw [prog_length]; decide) (by rfl)) h5
  have c0 := cpsTripleWithin_frameR
    (((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ newSp) ** regsAt f0 vals)) (by pcf) h0'
  have c0' : cpsTripleWithin 1 (B + 40) (B + 44) code
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals))
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals1)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp [regsAt, frame, f0] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by simp [regsAt, frame, f0, vals1] at hq ⊢; xperm_hyp hq) c0
  have c1 := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ target) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ newSp) ** regsAt f1 vals1)) (by pcf) h1'
  have c1' : cpsTripleWithin 1 (B + 44) (B + 48) code
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals1))
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals2)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp [regsAt, frame, f1, vals1] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by simp [regsAt, frame, f1, vals1, vals2] at hq ⊢; xperm_hyp hq) c1
  have c2 := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ newSp) ** regsAt f2 vals2)) (by pcf) h2'
  have c2' : cpsTripleWithin 1 (B + 48) (B + 52) code
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals2))
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals3)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp [regsAt, frame, f2, vals1, vals2] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by simp [regsAt, frame, f2, vals1, vals2, vals3] at hq ⊢; xperm_hyp hq) c2
  have c3 := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ newSp) ** regsAt f3 vals3)) (by pcf) h3'
  have c3' : cpsTripleWithin 1 (B + 52) (B + 56) code
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals3))
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals4)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp [regsAt, frame, f3, vals1, vals2, vals3] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by simp [regsAt, frame, f3, vals1, vals2, vals3, vals4] at hq ⊢; xperm_hyp hq) c3
  have c4 := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ outHash) ** (.x15 ↦ᵣ outLength) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ newSp) ** regsAt f4 vals4)) (by pcf) h4'
  have c4' : cpsTripleWithin 1 (B + 56) (B + 60) code
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals4))
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals5)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp [regsAt, frame, f4, vals1, vals2, vals3, vals4] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by simp [regsAt, frame, f4, vals1, vals2, vals3, vals4, vals5] at hq ⊢; xperm_hyp hq) c4
  have c5 := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ newSp) ** regsAt f5 vals5)) (by pcf) h5'
  have c5' : cpsTripleWithin 1 (B + 60) (B + 64) code
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals5))
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals6)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp [regsAt, frame, f5, vals1, vals2, vals3, vals4, vals5] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by simp [regsAt, frame, f5, vals1, vals2, vals3, vals4, vals5, vals6] at hq ⊢; xperm_hyp hq) c5
  have hmoves01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c0' c1'
  have hmoves012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hmoves01 c2'
  have hmoves0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hmoves012 c3'
  have hmoves01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hmoves0123 c4'
  have hmoves := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hmoves01234 c5'
  /-
  have hmoves' : cpsTripleWithin 6 (B + 40) (B + 64) code
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals))
      (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x2 ↦ᵣ newSp) ** regsAt frame vals6)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h_state hq => by
        simp [regsAt, frame, f2, vals1, vals2, vals3, vals4, vals5, vals6] at hq ⊢
        xperm_hyp hq) hmoves
  -/
  /-
  have hmoves' : cpsTripleWithin 6 (B + 40) (B + 64) code
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals))
      (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x2 ↦ᵣ newSp) ** regsAt f2 vals6)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by
        simp [regsAt, frame, f2, vals1, vals2, vals3, vals4, vals5, vals6] at hq ⊢
        xperm_hyp hq) hmoves
  -/
  have hmoves' : cpsTripleWithin 6 (B + 40) (B + 64) code
      (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) ** regsAt frame vals))
      (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x2 ↦ᵣ newSp) ** regsAt f2 vals6)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by
        simp [regsAt, frame, f2, vals1, vals2, vals3, vals4, vals5, vals6] at hq ⊢
        xperm_hyp hq) hmoves
  have hbeq := beq_spec_gen_within .x9 .x0
    (brOff (GuestAddrs.blockhash_from_witness_headers + 260)
      (GuestAddrs.blockhash_from_witness_headers + 64))
    (0 : Word) (0 : Word) (B + 64)
  have hbeqC := cpsBranchWithin_extend_code
    (mem_at 16 (.BEQ .x9 .x0
      (brOff (GuestAddrs.blockhash_from_witness_headers + 260)
        (GuestAddrs.blockhash_from_witness_headers + 64))) (B + 64) (by decide)
      (by rw [prog_length]; decide) (by rfl)) hbeq
  have hbeqF := cpsBranchWithin_frameR
    (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
      (.x2 ↦ᵣ newSp) ** regsAt f2 vals6)) (by pcf) hbeqC
  have htakenRaw := cpsBranchWithin_takenPath hbeqF (fun _ hq => by
    extract_pure_deep hq
    obtain ⟨hneq, _⟩ := hq
    exact hneq rfl)
  have htaken : cpsTripleWithin 1 (B + 64) (B + 260) code
      (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x2 ↦ᵣ newSp) ** regsAt f2 vals6))
      (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x2 ↦ᵣ newSp) ** regsAt f2 vals6)) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        extract_pure_deep hq
        obtain ⟨heq, hrest⟩ := hq
        xperm_hyp hrest)
      htakenRaw
  have hli := li_spec_gen_within .x10 target (1 : Word) (B + 260) (by decide)
  have hliC := cpsTripleWithin_extend_code
    (mem_at 65 (.LI .x10 (1 : Word)) (B + 260) (by decide)
      (by rw [prog_length]; decide) (by rfl)) hli
  have hliF := cpsTripleWithin_frameR
    (((.x9 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ newSp) ** regsAt f2 vals6) **
      ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
       (.x0 ↦ᵣ (0 : Word)))) (by pcf) hliC
  have hprefix := cpsTripleWithin_seq_perm_same_cr (by xsimp) hmoves' htaken
  have hbody := cpsTripleWithin_seq_perm_same_cr (by xsimp) hprefix hliF
  have hbody' : cpsTripleWithin 8 (B + 40) (B + 264) code
      ((.x2 ↦ᵣ newSp) ** regsAt frame vals **
        ((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x0 ↦ᵣ (0 : Word))))
      ((.x2 ↦ᵣ newSp) ** regsOwnAt frame **
        ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x0 ↦ᵣ (0 : Word)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h_state hq => by
        have hq' := sepConj_mono
          (fun _ hp => hp)
          (sepConj_mono
            (sepConj_mono (regIs_to_regOwn .x9 0)
              (sepConj_mono (fun _ hp => hp)
                (regsAt_implies_regsOwnAt f2 vals6)))
            (fun _ hp => hp)) h_state hq
        simp [regsOwnAt, frame, f2] at hq' ⊢
        xperm_hyp hq') hbody
  exact hbody'

/-! The empty-section whole-routine result.  The nonempty scan and both
    external callees are not reached on this domain. -/

set_option maxRecDepth 8000 in
theorem blockhash_from_witness_headers_spec_within_empty_section
    (sp0 ret target sectionPtr outHash outOffset outLength : Word)
    (vals : Reg → Word)
    (G : Assertion) (hG : G.pcFree)
    (hsec : sectionPtr = 0)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 29 B ret code
      ((.x2 ↦ᵣ sp0) ** regsAt frame vals **
        frameSlotsOwn frame (sp0 + signExtend12 (-80 : BitVec 12)) **
        ((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ sectionPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x0 ↦ᵣ (0 : Word))) ** G)
      ((.x2 ↦ᵣ sp0) ** regsAt frame vals **
        frameSlotsSaved frame (sp0 + signExtend12 (-80 : BitVec 12)) vals **
        ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ sectionPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x0 ↦ᵣ (0 : Word))) ** G) := by
  have hbody := empty_body
    (sp0 + signExtend12 (-80 : BitVec 12)) target sectionPtr outHash outOffset outLength
    vals hsec
  have hsub : ∀ a i,
      CodeReq.ofProg B (abiFrameProg (-80 : BitVec 12) (80 : BitVec 12) frame body) a = some i →
        code a = some i := by
    intro a i h
    rw [body_decomposition] at h
    exact h
  have hbodyF := cpsTripleWithin_frameR
    (frameSlotsSaved frame (sp0 + signExtend12 (-80 : BitVec 12)) vals ** G)
    (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hG) hbody
  have hbody' : cpsTripleWithin 8 (B + 40) (B + 264) code
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-80 : BitVec 12))) ** regsAt frame vals **
        frameSlotsSaved frame (sp0 + signExtend12 (-80 : BitVec 12)) vals **
        (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ sectionPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x0 ↦ᵣ (0 : Word))) ** G))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-80 : BitVec 12))) ** regsOwnAt frame **
        frameSlotsSaved frame (sp0 + signExtend12 (-80 : BitVec 12)) vals **
        (((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ sectionPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
          (.x0 ↦ᵣ (0 : Word))) ** G)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp [regsAt, frame, frameSlotsSaved] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by simp [regsOwnAt, frame, frameSlotsSaved] at hq ⊢; xperm_hyp hq) hbodyF
  have h := abiFrame_spec_own B sp0 ret
    (-80 : BitVec 12) (80 : BitVec 12) frame (0 : BitVec 12)
    [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)),
     (.x18, (24 : BitVec 12)), (.x19, (32 : BitVec 12)),
     (.x20, (40 : BitVec 12)), (.x21, (48 : BitVec 12)),
     (.x22, (56 : BitVec 12)), (.x23, (64 : BitVec 12))]
    vals body 8
    (((.x10 ↦ᵣ target) ** (.x11 ↦ᵣ sectionPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
      (.x0 ↦ᵣ (0 : Word))) ** G)
    (((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ sectionPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ outHash) ** (.x14 ↦ᵣ outOffset) ** (.x15 ↦ᵣ outLength) **
      (.x0 ↦ᵣ (0 : Word))) ** G)
    code
    rfl (by decide) (by decide)
    (by rw [body_decomposition]; exact prog_bound)
    hret halign
    (by
      rw [show signExtend12 (-80 : BitVec 12) = (-80 : Word) from by decide,
        show signExtend12 (80 : BitVec 12) = (80 : Word) from by decide]
      bv_omega)
    (pcFree_sepConj (by pcf) hG)
    (pcFree_sepConj (by pcf) hG)
    hsub hbody'
  rw [frame_length] at h
  norm_num at h
  exact h

end EvmAsm.Codegen.BlockHashFromWitnessHeadersSpec
