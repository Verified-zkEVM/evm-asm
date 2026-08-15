/-
  EvmAsm.Codegen.Proofs.HashBridgeSha256Rem

  Remainder byte-copy loop for zkvm_sha256 pad path (idx 60-66):
    BEQ x7,x0 → B+268 (empty)
    LBU x28,0(x6); SB x5,x28,0; ADDI x5+1; ADDI x6+1; ADDI x7-1; JAL -24

  Also rem≥56 fall-through after BLT (idx 72–82 @ B+288):
    la params + CSRS + 8× SD re-zero → bitlen join B+332.

  Domain: scratchBase % 8 = 0 (BSS); inputCursor % 8 = 0 (LBU framing);
  rem ≤ remaining input length; rem ≤ 64 (scratch window).
  Pattern: ExecutionRequestsHashHashOneCopy / MptWalkLeafValue.leaf_copy_step.
-/

import EvmAsm.Codegen.Proofs.HashBridgeSha256Pad
import EvmAsm.Codegen.Proofs.HashBridgeSha256Block
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256
private abbrev sha256ProgL : List Instr := zkvmSha256_prog
private abbrev sha256Cr : CodeReq := CodeReq.ofProg B sha256ProgL
private abbrev ShaParams : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_params

private theorem sha256ProgL_len : sha256ProgL.length = 121 := by
  simp only [sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of]
  decide

private theorem sha256ProgL_bound : 4 * sha256ProgL.length < 2 ^ 64 := by
  rw [sha256ProgL_len]; norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < sha256ProgL.length)
    (hins : sha256ProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → sha256Cr a = some i :=
  fun a i h => CodeReq.ofProg_mem_at B A sha256ProgL k ins hA hk hins
    sha256ProgL_bound a i h

private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se12_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
private theorem ofNat_zero : BitVec.ofNat 64 0 = (0 : Word) := rfl
private theorem one_plus_neg1 : (1 : Word) + (-1 : Word) = 0 := by decide

theorem ofNat_succ (k : Nat) :
    BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + (1 : Word) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  exact Nat.add_mod k 1 (2 ^ 64)

private theorem word_ofNat_succ_ne_zero (k : Nat) (hk : k + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := by
  intro heq
  have htn := congrArg BitVec.toNat heq
  have hmod : (BitVec.ofNat 64 (k + 1)).toNat = k + 1 := by
    simp only [BitVec.toNat_ofNat]; omega
  have hz : (0 : Word).toNat = 0 := rfl
  omega

private theorem cursor_succ (p : Word) (done : Nat) :
    p + BitVec.ofNat 64 done + (1 : Word) = p + BitVec.ofNat 64 (done + 1) := by
  rw [BitVec.add_assoc, ofNat_succ done]

private theorem cnt_step_down (k : Nat) :
    BitVec.ofNat 64 (k + 1) + (-1 : Word) = BitVec.ofNat 64 k := by
  have e1 : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + (1 : Word) := ofNat_succ k
  calc
    BitVec.ofNat 64 (k + 1) + (-1 : Word)
        = (BitVec.ofNat 64 k + (1 : Word)) + (-1 : Word) := by rw [e1]
    _ = BitVec.ofNat 64 k + ((1 : Word) + (-1 : Word)) := by rw [BitVec.add_assoc]
    _ = BitVec.ofNat 64 k + (0 : Word) := by rw [one_plus_neg1]
    _ = BitVec.ofNat 64 k := BitVec.add_zero _

/-- Inv at BEQ header: k remaining, done bytes copied. -/
def sha256RemInv (scratchBase inputCursor : Word)
    (input scratch : List (BitVec 8)) (k done : Nat) (F : Assertion) : Assertion :=
  (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 done)) **
  (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 done)) **
  (.x7 ↦ᵣ BitVec.ofNat 64 k) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion inputCursor input **
  bytesRegion scratchBase scratch **
  regOwn .x28 ** F

def sha256RemDone (scratchBase inputCursor : Word)
    (input scratch : List (BitVec 8)) (done : Nat) (F : Assertion) : Assertion :=
  (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 done)) **
  (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 done)) **
  (.x7 ↦ᵣ (0 : Word)) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion inputCursor input **
  bytesRegion scratchBase scratch **
  regOwn .x28 ** F

/-- BEQ taken remaining=0. Fuel 1. B+240→B+268. -/
theorem sha256RemCopy_exit_zero
    (scratchBase inputCursor : Word)
    (input scratch : List (BitVec 8)) (done : Nat)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (B + 240) (B + 268) sha256Cr
      (sha256RemInv scratchBase inputCursor input scratch 0 done F)
      (sha256RemDone scratchBase inputCursor input scratch done F) := by
  have hbr := beq_spec_gen_within .x7 .x0 (28 : BitVec 13)
    (0 : Word) (0 : Word) (B + 240)
  have hbrC := cpsBranchWithin_extend_code
    (mem_at 60 (.BEQ .x7 .x0 (28 : BitVec 13)) (B + 240) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hbr
  have hbrT := cpsBranchWithin_takenStripPure2 hbrC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  rw [show (B + 240 : Word) + signExtend13 (28 : BitVec 13) = B + 268 from by decide]
    at hbrT
  have hbrF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 done)) **
     (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 done)) **
     bytesRegion inputCursor input ** bytesRegion scratchBase scratch **
     regOwn .x28 ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact bytesRegion_pcFree _ _
        | exact hF) hbrT
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [sha256RemInv, ofNat_zero] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by
      simp only [sha256RemDone] at hq ⊢; xperm_chunked hq)
    hbrF

/-- One copy iteration: k+1 → k, done → done+1. Fuel 7. Returns to B+240. -/
theorem sha256RemCopy_step
    (scratchBase inputCursor : Word)
    (input scratch0 : List (BitVec 8))
    (k done : Nat)
    (hinp : done < input.length)
    (hscr : done < scratch0.length)
    (hsrcAlign : inputCursor.toNat % 8 = 0)
    (hdstAlign : scratchBase.toNat % 8 = 0)
    (hsrcOver : inputCursor.toNat + done < 2 ^ 64)
    (hdstOver : scratchBase.toNat + done < 2 ^ 64)
    (hkbound : k + 1 < 2 ^ 64)
    (hvalidS : isValidByteAccess (inputCursor + BitVec.ofNat 64 done) = true)
    (hvalidD : isValidByteAccess (scratchBase + BitVec.ofNat 64 done) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (B + 240) (B + 240) sha256Cr
      (sha256RemInv scratchBase inputCursor input scratch0 (k + 1) done F)
      (sha256RemInv scratchBase inputCursor input
        (scratch0.set done (input[done]'hinp)) k (done + 1) F) := by
  have hne := word_ofNat_succ_ne_zero k hkbound
  -- BEQ ntaken
  have hbr := beq_spec_gen_within .x7 .x0 (28 : BitVec 13)
    (BitVec.ofNat 64 (k + 1)) (0 : Word) (B + 240)
  have hbrC := cpsBranchWithin_extend_code
    (mem_at 60 (.BEQ .x7 .x0 (28 : BitVec 13)) (B + 240) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hQ).2)
  rw [show (B + 240 : Word) + 4 = B + 244 from by decide] at hnt
  have hbeq := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 done)) **
     (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 done)) **
     bytesRegion inputCursor input ** bytesRegion scratchBase scratch0 **
     regOwn .x28 ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact bytesRegion_pcFree _ _
        | exact hF) hnt
  -- LBU x28 from input (own trailing)
  have hlbu : ∀ v28,
      cpsTripleWithin 1 (B + 244) (B + 248) sha256Cr
        (((.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 done)) **
          bytesRegion inputCursor input **
          (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 done)) **
          (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion scratchBase scratch0 ** F) **
         (.x28 ↦ᵣ v28))
        ((.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 done)) **
          (.x28 ↦ᵣ ((input[done]'hinp).zeroExtend 64)) **
          bytesRegion inputCursor input **
          (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 done)) **
          (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion scratchBase scratch0 ** F) := by
    intro v28
    have hl := bytesRegion_lbu_within .x28 .x6 inputCursor v28 (B + 244)
      input done (by decide) hsrcAlign hinp hsrcOver hvalidS
    have hlE := cpsTripleWithin_extend_code
      (mem_at 61 (.LBU .x28 .x6 0) (B + 244) (by decide)
        (by rw [sha256ProgL_len]; decide) (by rfl)) hl
    rw [show (B + 244 : Word) + 4 = B + 248 from by decide] at hlE
    have hFr := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 done)) **
       (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion scratchBase scratch0 ** F)
      (by
        repeat' first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact bytesRegion_pcFree _ _
          | exact hF) hlE
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hFr
  have hlbuOwn := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x28) hlbu
  -- SB to scratch
  have hsb0 := bytesRegion_sb_within .x5 .x28 scratchBase
    ((input[done]'hinp).zeroExtend 64) (B + 248) scratch0 done
    hdstAlign hscr hdstOver hvalidD
  have hsb := cpsTripleWithin_extend_code
    (mem_at 62 (.SB .x5 .x28 0) (B + 248) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hsb0
  rw [show (B + 248 : Word) + 4 = B + 252 from by decide] at hsb
  have hbyte :
      ((input[done]'hinp).zeroExtend 64).truncate 8 = input[done]'hinp :=
    truncate_zeroExtend_byte _
  simp only [hbyte] at hsb
  have hsbF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 done)) **
     (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion inputCursor input ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | exact hF) hsb
  -- ADDI x5 +1
  have hadd50 := addi_spec_gen_same_within .x5
    (scratchBase + BitVec.ofNat 64 done) (1 : BitVec 12) (B + 252) (by decide)
  have hadd5 := cpsTripleWithin_extend_code
    (mem_at 63 (.ADDI .x5 .x5 1) (B + 252) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hadd50
  rw [show (B + 252 : Word) + 4 = B + 256 from by decide, se12_1] at hadd5
  have hadd5F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 done)) **
     (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x28 ↦ᵣ ((input[done]'hinp).zeroExtend 64)) **
     bytesRegion inputCursor input **
     bytesRegion scratchBase (scratch0.set done (input[done]'hinp)) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact bytesRegion_pcFree _ _
        | exact hF) hadd5
  -- ADDI x6 +1
  have hadd60 := addi_spec_gen_same_within .x6
    (inputCursor + BitVec.ofNat 64 done) (1 : BitVec 12) (B + 256) (by decide)
  have hadd6 := cpsTripleWithin_extend_code
    (mem_at 64 (.ADDI .x6 .x6 1) (B + 256) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hadd60
  rw [show (B + 256 : Word) + 4 = B + 260 from by decide, se12_1] at hadd6
  have hadd6F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x28 ↦ᵣ ((input[done]'hinp).zeroExtend 64)) **
     bytesRegion inputCursor input **
     bytesRegion scratchBase (scratch0.set done (input[done]'hinp)) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact bytesRegion_pcFree _ _
        | exact hF) hadd6
  -- ADDI x7 -1
  have hadd70 := addi_spec_gen_same_within .x7
    (BitVec.ofNat 64 (k + 1)) (-1 : BitVec 12) (B + 260) (by decide)
  have hadd7 := cpsTripleWithin_extend_code
    (mem_at 65 (.ADDI .x7 .x7 (-1 : BitVec 12)) (B + 260) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hadd70
  rw [show (B + 260 : Word) + 4 = B + 264 from by decide, se12_m1] at hadd7
  have hadd7F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 done + (1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x28 ↦ᵣ ((input[done]'hinp).zeroExtend 64)) **
     bytesRegion inputCursor input **
     bytesRegion scratchBase (scratch0.set done (input[done]'hinp)) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact bytesRegion_pcFree _ _
        | exact hF) hadd7
  -- JAL back
  have hjal0 := jal_x0_spec_gen_within (-24 : BitVec 21) (B + 264)
  have hjal := cpsTripleWithin_extend_code
    (mem_at 66 (.JAL .x0 (-24 : BitVec 21)) (B + 264) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hjal0
  rw [show (B + 264 : Word) + signExtend21 (-24 : BitVec 21) = B + 240 from by decide]
    at hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 done + (1 : Word))) **
     (.x7 ↦ᵣ (BitVec.ofNat 64 (k + 1) + (-1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x28 ↦ᵣ ((input[done]'hinp).zeroExtend 64)) **
     bytesRegion inputCursor input **
     bytesRegion scratchBase (scratch0.set done (input[done]'hinp)) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact bytesRegion_pcFree _ _
        | exact hF) hjal
  have hjalW := cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hjalF
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hbeq hlbuOwn
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0 hsbF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hadd5F
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hadd6F
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 hadd7F
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01234 hjalW
  have hcur5 := cursor_succ scratchBase done
  have hcur6 := cursor_succ inputCursor done
  have hrem := cnt_step_down k
  refine cpsTripleWithin_weaken ?_ ?_ c
  · intro h hp
    simp only [sha256RemInv] at hp ⊢; xperm_chunked hp
  · intro h hq
    -- normalize cursors/rem then peel x28 concrete → own
    have hq1 :
        ((.x28 ↦ᵣ ((input[done]'hinp).zeroExtend 64)) **
         (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 (done + 1))) **
         (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 (done + 1))) **
         (.x7 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion inputCursor input **
         bytesRegion scratchBase (scratch0.set done (input[done]'hinp)) ** F) h := by
      simp only [hcur5, hcur6, hrem] at hq
      xperm_chunked hq
    have hq2 :
        (regOwn .x28 **
         (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 (done + 1))) **
         (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 (done + 1))) **
         (.x7 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion inputCursor input **
         bytesRegion scratchBase (scratch0.set done (input[done]'hinp)) ** F) h :=
      sepConj_mono_left (regIs_implies_regOwn .x28) _ hq1
    simp only [sha256RemInv]
    xperm_chunked hq2

/-- After `done` prefix bytes copied: `input.take done ++ scratch0.drop done`. -/
def sha256RemPrefix (input scratch0 : List (BitVec 8)) (done : Nat) : List (BitVec 8) :=
  input.take done ++ scratch0.drop done

theorem sha256RemPrefix_length (input scratch0 : List (BitVec 8)) (done : Nat)
    (hs : scratch0.length = 64) (hd : done ≤ 64) (hinp : done ≤ input.length) :
    (sha256RemPrefix input scratch0 done).length = 64 := by
  simp only [sha256RemPrefix, List.length_append, List.length_take, List.length_drop, hs]
  omega

/-- Byte view when `done ≤ input.length` (so take length = done). -/
private theorem sha256RemPrefix_getElem
    (input scratch0 : List (BitVec 8)) (done i : Nat)
    (hs : scratch0.length = 64) (hd64 : done ≤ 64)
    (hinp : done ≤ input.length) (hi : i < 64) :
    (sha256RemPrefix input scratch0 done)[i]'(by
        rw [sha256RemPrefix_length input scratch0 done hs hd64 hinp]; exact hi) =
      if h : i < done then input[i]'(Nat.lt_of_lt_of_le h hinp)
      else scratch0[i]'(by omega) := by
  simp only [sha256RemPrefix]
  have htakeLen : (input.take done).length = done := by
    simp [List.length_take]; omega
  by_cases hlt : i < done
  · have hlt' : i < (input.take done).length := by omega
    rw [List.getElem_append_left hlt', List.getElem_take]
    simp [hlt]
  · have hge : (input.take done).length ≤ i := by omega
    rw [List.getElem_append_right hge, List.getElem_drop]
    simp only [htakeLen, hlt, ↓reduceDIte]
    have : done + (i - done) = i := Nat.add_sub_of_le (Nat.le_of_not_gt hlt)
    simp [this]

/-- One more copied byte advances the prefix. -/
theorem sha256RemPrefix_succ
    (input scratch0 : List (BitVec 8)) (done : Nat)
    (hs : scratch0.length = 64) (hd : done < input.length) (hd64 : done < 64) :
    (sha256RemPrefix input scratch0 done).set done (input[done]'hd) =
      sha256RemPrefix input scratch0 (done + 1) := by
  have hlenL := sha256RemPrefix_length input scratch0 done hs (by omega) (by omega)
  have hlenR := sha256RemPrefix_length input scratch0 (done + 1) hs (by omega) (by omega)
  have hlenSet : ((sha256RemPrefix input scratch0 done).set done (input[done]'hd)).length =
      (sha256RemPrefix input scratch0 (done + 1)).length := by
    rw [List.length_set, hlenL, hlenR]
  refine List.ext_getElem hlenSet ?_
  intro i hiL hiR
  have hi : i < 64 := by omega
  rw [List.getElem_set]
  split_ifs with heq
  · subst heq
    have hg := sha256RemPrefix_getElem input scratch0 (done + 1) done hs
      (by omega) (by omega) hi
    have : done < done + 1 := Nat.lt_succ_self _
    simpa [this] using hg.symm
  · have hg0 := sha256RemPrefix_getElem input scratch0 done i hs
      (by omega) (by omega) hi
    have hg1 := sha256RemPrefix_getElem input scratch0 (done + 1) i hs
      (by omega) (by omega) hi
    rw [hg0, hg1]
    by_cases hlt : i < done
    · have : i < done + 1 := Nat.lt_succ_of_lt hlt
      simp [hlt, this]
    · simp only [hlt, ↓reduceDIte]
      by_cases hlt1 : i < done + 1
      · omega
      · simp [hlt1]

/-- Loop from arbitrary `done`: remaining k → 0. Fuel k*7+1. -/
theorem sha256RemCopy_loop_from
    (scratchBase inputCursor : Word)
    (input scratch0 : List (BitVec 8))
    (k done : Nat)
    (hsrcAlign : inputCursor.toNat % 8 = 0)
    (hdstAlign : scratchBase.toNat % 8 = 0)
    (hinp : done + k ≤ input.length)
    (hscr : scratch0.length = 64)
    (hspan : done + k ≤ 64)
    (hsrcOver : inputCursor.toNat + done + k ≤ 2 ^ 64)
    (hdstOver : scratchBase.toNat + done + k ≤ 2 ^ 64)
    (hkbound : k < 2 ^ 64)
    (hvalidS : ∀ i < k, isValidByteAccess
      (inputCursor + BitVec.ofNat 64 (done + i)) = true)
    (hvalidD : ∀ i < k, isValidByteAccess
      (scratchBase + BitVec.ofNat 64 (done + i)) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin (k * 7 + 1) (B + 240) (B + 268) sha256Cr
      (sha256RemInv scratchBase inputCursor input
        (sha256RemPrefix input scratch0 done) k done F)
      (sha256RemDone scratchBase inputCursor input
        (sha256RemPrefix input scratch0 (done + k))
        (done + k) F) := by
  induction k generalizing done with
  | zero =>
    simpa [Nat.add_zero] using
      sha256RemCopy_exit_zero scratchBase inputCursor input
        (sha256RemPrefix input scratch0 done) done F hF
  | succ k ih =>
    have hpref_len : (sha256RemPrefix input scratch0 done).length = 64 :=
      sha256RemPrefix_length input scratch0 done hscr (by omega) (by omega)
    have hstep := sha256RemCopy_step scratchBase inputCursor input
      (sha256RemPrefix input scratch0 done) k done
      (by omega) (by rw [hpref_len]; omega) hsrcAlign hdstAlign
      (by omega) (by omega) (by omega)
      (hvalidS 0 (by omega)) (hvalidD 0 (by omega)) F hF
    -- After step: Inv at done+1 with set prefix
    have hset := sha256RemPrefix_succ input scratch0 done hscr (by omega) (by omega)
    have hrest :=
      ih (done + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun i hi => by
          have h := hvalidS (i + 1) (by omega)
          have heq :
              BitVec.ofNat 64 (done + 1 + i) =
                BitVec.ofNat 64 (done + (i + 1)) := by
            simp [Nat.add_assoc, Nat.add_comm 1 i]
          simpa [heq] using h)
        (fun i hi => by
          have h := hvalidD (i + 1) (by omega)
          have heq :
              BitVec.ofNat 64 (done + 1 + i) =
                BitVec.ofNat 64 (done + (i + 1)) := by
            simp [Nat.add_assoc, Nat.add_comm 1 i]
          simpa [heq] using h)
    -- rewrite step post via hset so it matches IH pre
    have hstep' :
        cpsTripleWithin 7 (B + 240) (B + 240) sha256Cr
          (sha256RemInv scratchBase inputCursor input
            (sha256RemPrefix input scratch0 done) (k + 1) done F)
          (sha256RemInv scratchBase inputCursor input
            (sha256RemPrefix input scratch0 (done + 1)) k (done + 1) F) := by
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hstep
      simpa [hset] using hq
    have hseq := cpsTripleWithin_seq_same_cr hstep' hrest
    have hseq' : cpsTripleWithin ((k + 1) * 7 + 1) (B + 240) (B + 268) sha256Cr
        (sha256RemInv scratchBase inputCursor input
          (sha256RemPrefix input scratch0 done) (k + 1) done F)
        (sha256RemDone scratchBase inputCursor input
          (sha256RemPrefix input scratch0 (done + 1 + k))
          (done + 1 + k) F) := by
      convert hseq using 1; omega
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hseq'
    simpa [Nat.add_assoc, Nat.add_comm 1 k, Nat.add_left_comm 1] using hq

/-- Entry: remaining = rem, done = 0. Fuel rem*7+1.
    Pre scratch is arbitrary 64-byte window; post is `input.take rem ++ scratch0.drop rem`. -/
theorem sha256RemCopy_loop
    (scratchBase inputCursor : Word)
    (input scratch0 : List (BitVec 8))
    (rem : Nat)
    (hsrcAlign : inputCursor.toNat % 8 = 0)
    (hdstAlign : scratchBase.toNat % 8 = 0)
    (hinp : rem ≤ input.length)
    (hscr : scratch0.length = 64)
    (hspan : rem ≤ 64)
    (hsrcOver : inputCursor.toNat + rem ≤ 2 ^ 64)
    (hdstOver : scratchBase.toNat + rem ≤ 2 ^ 64)
    (hkbound : rem < 2 ^ 64)
    (hvalidS : ∀ i < rem, isValidByteAccess (inputCursor + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i < rem, isValidByteAccess (scratchBase + BitVec.ofNat 64 i) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin (rem * 7 + 1) (B + 240) (B + 268) sha256Cr
      (sha256RemInv scratchBase inputCursor input scratch0 rem 0 F)
      (sha256RemDone scratchBase inputCursor input
        (sha256RemPrefix input scratch0 rem) rem F) := by
  have hpre :
      sha256RemPrefix input scratch0 0 = scratch0 := by
    simp [sha256RemPrefix]
  have h := sha256RemCopy_loop_from scratchBase inputCursor input scratch0 rem 0
    hsrcAlign hdstAlign (by omega) hscr (by omega) (by omega) (by omega) hkbound
    (fun i hi => by simpa using hvalidS i hi)
    (fun i hi => by simpa using hvalidD i hi) F hF
  -- h : Inv Prefix0 → Done (0+rem); goal : Inv scratch0 → Done rem
  simpa [hpre, Nat.zero_add] using h

/-- After rem loop: `ADD x5,x21,x18; LI x6,128; SB x6,0(x5)` at B+268.
    Posts 0x80 (=128) at scratch[rem]. Fuel 3 → B+280.
    SB framed as regionBase=scratchBase, i=rem, rs1=scratchBase+rem. -/
theorem sha256PadBit_spec
    (scratchBase : Word) (rem : Nat)
    (scratch : List (BitVec 8))
    (halign : scratchBase.toNat % 8 = 0)
    (hlen : scratch.length = 64)
    (hrem : rem < 64)
    (hover : scratchBase.toNat + rem < 2 ^ 64)
    (hvalid : isValidByteAccess (scratchBase + BitVec.ofNat 64 rem) = true)
    (F : Assertion) (hF : F.pcFree)
    (v5 v6 v7 : Word) :
    cpsTripleWithin 3 (B + 268) (B + 280) sha256Cr
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x21 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
       bytesRegion scratchBase scratch ** F)
      ((.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
       (.x6 ↦ᵣ (128 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x21 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
       bytesRegion scratchBase (scratch.set rem (128 : BitVec 8)) ** F) := by
  -- ADD x5, x21, x18
  have hadd := add_spec_gen_within .x5 .x21 .x18
    scratchBase (BitVec.ofNat 64 rem) v5 (B + 268) (by decide)
  have haddC := cpsTripleWithin_extend_code
    (mem_at 67 (.ADD .x5 .x21 .x18) (B + 268) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hadd
  rw [show (B + 268 : Word) + 4 = B + 272 from by decide] at haddC
  have haddF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     bytesRegion scratchBase scratch ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | exact hF) haddC
  -- LI x6, 128
  have hli := li_spec_gen_within .x6 v6 (128 : Word) (B + 272) (by decide)
  have hliC := cpsTripleWithin_extend_code
    (mem_at 68 (.LI .x6 (128 : Word)) (B + 272) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hli
  rw [show (B + 272 : Word) + 4 = B + 276 from by decide] at hliC
  have hliF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) ** (.x7 ↦ᵣ v7) **
     (.x21 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
     bytesRegion scratchBase scratch ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | exact hF) hliC
  -- SB x6 at rem (regionBase=scratchBase, i=rem, PC=B+276)
  have hsb := bytesRegion_sb_within .x5 .x6
    scratchBase (128 : Word) (B + 276) scratch rem
    halign (by omega) hover hvalid
  have hsbC := cpsTripleWithin_extend_code
    (mem_at 69 (.SB .x5 .x6 (0 : BitVec 12)) (B + 276) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hsb
  rw [show (B + 276 : Word) + 4 = B + 280 from by decide] at hsbC
  have hsbF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7) ** (.x21 ↦ᵣ scratchBase) **
     (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hF) hsbC
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    haddF hliF
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hsbF
  have htr : (128 : Word).truncate 8 = (128 : BitVec 8) := by decide
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => ?_) c
  simp only [htr] at hq
  xperm_chunked hq

/-! ## LI 56 + BLT rem < 56 (idx 70–71 @ B+280) -/

private theorem blt_rem56_taken :
    (B + 284 : Word) + signExtend13 (48 : BitVec 13) = B + 332 := by decide
private theorem blt_rem56_fall :
    (B + 284 : Word) + 4 = B + 288 := by decide

private theorem toInt_ofNat_of_lt (n : Nat) (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_ofNat']
  -- (n : Int).bmod (2^64) = n when -(2^63) ≤ n < 2^63
  have hlo : -((2 ^ 64 : Nat) : Int) / 2 ≤ (n : Int) := by
    have : 0 ≤ (n : Int) := Int.natCast_nonneg _
    omega
  have hhi : (n : Int) < ((2 ^ 64 : Nat) : Int) / 2 := by
    have : (n : Int) < 2 ^ 63 := by exact_mod_cast hn
    omega
  exact Int.bmod_eq_of_le hlo hhi

private theorem ofNat_rem_slt_56 (rem : Nat) (hrem : rem < 56) :
    (BitVec.ofNat 64 rem).slt (56 : Word) = true := by
  have h1 := toInt_ofNat_of_lt rem (by omega)
  have h2 : (56 : Word).toInt = 56 := by decide
  simp only [BitVec.slt, h1, h2, decide_eq_true_eq]
  exact_mod_cast hrem

private theorem ofNat_rem_not_slt_56 (rem : Nat) (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    (BitVec.ofNat 64 rem).slt (56 : Word) = false := by
  have h1 := toInt_ofNat_of_lt rem (by omega)
  have h2 : (56 : Word).toInt = 56 := by decide
  simp only [BitVec.slt, h1, h2, decide_eq_false_iff_not, not_lt]
  exact_mod_cast hrem

/-- `li x5, 56` at B+280. -/
theorem sha256PadLi56_spec (v5 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (B + 280) (B + 284)
      (CodeReq.ofProg B zkvmSha256_prog)
      ((.x5 ↦ᵣ v5) ** F)
      ((.x5 ↦ᵣ (56 : Word)) ** F) := by
  have hli := li_spec_gen_within .x5 v5 (56 : Word) (B + 280) (by decide)
  have hliC := cpsTripleWithin_extend_code
    (mem_at 70 (.LI .x5 (56 : Word)) (B + 280) (by bv_omega)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hli
  rw [show (B + 280 : Word) + 4 = B + 284 from by decide] at hliC
  exact cpsTripleWithin_frameR F hF hliC

/-- BLT taken when `rem < 56`: jump to bitlen write at B+332. -/
theorem sha256PadBlt_lt56 (rem : Nat) (F : Assertion) (hF : F.pcFree)
    (hrem : rem < 56) :
    cpsTripleWithin 1 (B + 284) (B + 332)
      (CodeReq.ofProg B zkvmSha256_prog)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ (56 : Word)) ** F)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ (56 : Word)) ** F) := by
  have hblt0 := blt_spec_gen_within .x18 .x5 (48 : BitVec 13)
    (BitVec.ofNat 64 rem) (56 : Word) (B + 284)
  have hblt := cpsBranchWithin_extend_code
    (mem_at 71 (.BLT .x18 .x5 (48 : BitVec 13)) (B + 284) (by bv_omega)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hblt0
  have hslt := ofNat_rem_slt_56 rem hrem
  have hbltT := cpsBranchWithin_takenStripPure2 hblt (fun _ hQf => by
    -- Focus is x18 ** (x5 ** pure_fallthrough); pure = ¬slt
    obtain ⟨_, _, _, _, _, hmid⟩ := hQf
    have hn : ¬ ((BitVec.ofNat 64 rem).slt (56 : Word) = true) :=
      ((sepConj_pure_right _).1 hmid).2
    rw [hslt] at hn
    exact hn rfl)
  rw [blt_rem56_taken] at hbltT
  have hfr := cpsTripleWithin_frameR F hF hbltT
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hfr

/-- BLT not-taken when `rem ≥ 56`: fall through to extra compress at B+288. -/
theorem sha256PadBlt_ge56 (rem : Nat) (F : Assertion) (hF : F.pcFree)
    (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    cpsTripleWithin 1 (B + 284) (B + 288)
      (CodeReq.ofProg B zkvmSha256_prog)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ (56 : Word)) ** F)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ (56 : Word)) ** F) := by
  have hblt0 := blt_spec_gen_within .x18 .x5 (48 : BitVec 13)
    (BitVec.ofNat 64 rem) (56 : Word) (B + 284)
  have hblt := cpsBranchWithin_extend_code
    (mem_at 71 (.BLT .x18 .x5 (48 : BitVec 13)) (B + 284) (by bv_omega)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hblt0
  have hnslt := ofNat_rem_not_slt_56 rem hrem hrem64
  have hbltN := cpsBranchWithin_ntakenStripPure2 hblt (fun _ hQt => by
    -- Taken pure = slt = true; absurd under rem ≥ 56
    obtain ⟨_, _, _, _, _, hmid⟩ := hQt
    have ht : (BitVec.ofNat 64 rem).slt (56 : Word) = true :=
      ((sepConj_pure_right _).1 hmid).2
    rw [hnslt] at ht
    exact Bool.noConfusion ht)
  rw [blt_rem56_fall] at hbltN
  have hfr := cpsTripleWithin_frameR F hF hbltN
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hfr

/-- LI56 + BLT taken: B+280 → B+332 under `rem < 56`. -/
theorem sha256PadLiBlt_lt56 (rem : Nat) (v5 : Word) (F : Assertion) (hF : F.pcFree)
    (hrem : rem < 56) :
    cpsTripleWithin 2 (B + 280) (B + 332)
      (CodeReq.ofProg B zkvmSha256_prog)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ v5) ** F)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ (56 : Word)) ** F) := by
  have hli := sha256PadLi56_spec v5
    ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** F) (by pcf; exact hF)
  have hliW : cpsTripleWithin 1 (B + 280) (B + 284)
      (CodeReq.ofProg B zkvmSha256_prog)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ v5) ** F)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ (56 : Word)) ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hli
  have hblt := sha256PadBlt_lt56 rem F hF hrem
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hliW hblt

/-- LI56 + BLT fall-through: B+280 → B+288 under `rem ≥ 56`. -/
theorem sha256PadLiBlt_ge56 (rem : Nat) (v5 : Word) (F : Assertion) (hF : F.pcFree)
    (hrem : 56 ≤ rem) (hrem64 : rem < 64) :
    cpsTripleWithin 2 (B + 280) (B + 288)
      (CodeReq.ofProg B zkvmSha256_prog)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ v5) ** F)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ (56 : Word)) ** F) := by
  have hli := sha256PadLi56_spec v5
    ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** F) (by pcf; exact hF)
  have hliW : cpsTripleWithin 1 (B + 280) (B + 284)
      (CodeReq.ofProg B zkvmSha256_prog)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ v5) ** F)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x5 ↦ᵣ (56 : Word)) ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hli
  have hblt := sha256PadBlt_ge56 rem F hF hrem hrem64
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hliW hblt

/-! ## rem<56 pad spine compose: B+196 → B+332 -/

/-- Scratch after rem<56 pad: rem-prefix of zeroed block, then 0x80 at `rem`. -/
def sha256PadScratch_lt56 (input scratch0 : List (BitVec 8)) (rem : Nat) :
    List (BitVec 8) :=
  (sha256RemPrefix input (sha256PadZeroed scratch0) rem).set rem (128 : BitVec 8)

theorem length_sha256PadZeroed (scratch : List (BitVec 8)) (h : scratch.length = 64) :
    (sha256PadZeroed scratch).length = 64 := by
  simpa [sha256PadZeroedN_eight] using pad_zeroedN_len scratch h 8

theorem length_sha256PadScratch_lt56 (input scratch0 : List (BitVec 8)) (rem : Nat)
    (hs : scratch0.length = 64) (hrem : rem < 64) (hinp : rem ≤ input.length) :
    (sha256PadScratch_lt56 input scratch0 rem).length = 64 := by
  have hz := length_sha256PadZeroed scratch0 hs
  have hp := sha256RemPrefix_length input (sha256PadZeroed scratch0) rem hz
    (by omega) hinp
  simp only [sha256PadScratch_lt56, List.length_set, hp]

/-- rem<56 pad spine: zero → rem setup → rem copy → 0x80 → LI56/BLT taken.
    Fuel `rem*7+17`. B+196 → B+332 (bitlen join).
    Does not include bitlen write (`sha256Bitlen_write_spec` B+332→B+396). -/
theorem sha256PadPath_lt56_spec
    (scratchBase inputCursor : Word)
    (input scratch0 : List (BitVec 8))
    (rem : Nat)
    (v5 v6 v7 : Word)
    (F : Assertion) (hF : F.pcFree)
    (hsrcAlign : inputCursor.toNat % 8 = 0)
    (hdstAlign : scratchBase.toNat % 8 = 0)
    (hscratch : scratch0.length = 64)
    (hinp : rem ≤ input.length)
    (hrem : rem < 56)
    (hsrcOver : inputCursor.toNat + rem ≤ 2 ^ 64)
    (hdstSpan : scratchBase.toNat + 64 ≤ 2 ^ 64)
    (hvalidS : ∀ i < rem, isValidByteAccess (inputCursor + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i < rem, isValidByteAccess (scratchBase + BitVec.ofNat 64 i) = true)
    (hvalidPad : isValidByteAccess (scratchBase + BitVec.ofNat 64 rem) = true) :
    cpsTripleWithin (rem * 7 + 17) (B + 196) (B + 332) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase scratch0 **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ (56 : Word)) ** (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
        regOwn .x28 ** F) := by
  have hrem64 : rem < 64 := by omega
  have hremBound : rem < 2 ^ 64 := by omega
  have hdstOver : scratchBase.toNat + rem ≤ 2 ^ 64 := by omega
  have hdstHover : scratchBase.toNat + rem < 2 ^ 64 := by omega
  have hzLen := length_sha256PadZeroed scratch0 hscratch
  -- 1. Zero block B+196 → B+228
  have hz0 := sha256PadZeroBlock_spec scratchBase scratch0 hscratch
  have hzF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      bytesRegion inputCursor input ** regOwn .x28 ** F)
    (by pcf; exact hF) hz0
  have hz : cpsTripleWithin 8 (B + 196) (B + 228) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase scratch0 **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadZeroed scratch0) **
        regOwn .x28 ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hzF
  -- 2. Rem setup B+228 → B+240
  have hs0 := sha256PadRemSetup_spec scratchBase inputCursor
    (BitVec.ofNat 64 rem) v5 v6 v7
    ((.x0 ↦ᵣ (0 : Word)) ** bytesRegion inputCursor input **
      bytesRegion scratchBase (sha256PadZeroed scratch0) **
      regOwn .x28 ** F)
    (by pcf; exact hF)
  have hs : cpsTripleWithin 3 (B + 228) (B + 240) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadZeroed scratch0) **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) **
        (.x7 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadZeroed scratch0) **
        regOwn .x28 ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hs0
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hz hs
  -- 3. Rem copy loop B+240 → B+268
  let Floop : Assertion :=
    (.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
      (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** F
  have hFloop : Floop.pcFree := by pcf; exact hF
  have hloop0 := sha256RemCopy_loop scratchBase inputCursor input
    (sha256PadZeroed scratch0) rem hsrcAlign hdstAlign hinp hzLen
    (by omega) hsrcOver hdstOver hremBound hvalidS hvalidD Floop hFloop
  have hcur0 (p : Word) : p + BitVec.ofNat 64 0 = p := by
    rw [ofNat_zero]; exact BitVec.add_zero p
  have hloop : cpsTripleWithin (rem * 7 + 1) (B + 240) (B + 268) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) **
        (.x7 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadZeroed scratch0) **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 rem)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase
          (sha256RemPrefix input (sha256PadZeroed scratch0) rem) **
        regOwn .x28 ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hloop0
    · -- RemInv at done=0
      simp only [sha256RemInv, Floop, hcur0] at hp ⊢
      xperm_chunked hp
    · simp only [sha256RemDone, Floop] at hq ⊢
      xperm_chunked hq
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hloop
  -- 4. Pad 0x80 B+268 → B+280
  have hprefLen := sha256RemPrefix_length input (sha256PadZeroed scratch0) rem hzLen
    (by omega) hinp
  have hbit0 := sha256PadBit_spec scratchBase rem
    (sha256RemPrefix input (sha256PadZeroed scratch0) rem)
    hdstAlign hprefLen hrem64 hdstHover hvalidPad
    ((.x9 ↦ᵣ inputCursor) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion inputCursor input ** regOwn .x28 ** F)
    (by pcf; exact hF)
    (scratchBase + BitVec.ofNat 64 rem)
    (inputCursor + BitVec.ofNat 64 rem)
    (0 : Word)
  have hbit : cpsTripleWithin 3 (B + 268) (B + 280) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 rem)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase
          (sha256RemPrefix input (sha256PadZeroed scratch0) rem) **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
        regOwn .x28 ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => ?_) hbit0
    simp only [sha256PadScratch_lt56] at hq ⊢
    xperm_chunked hq
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c02 hbit
  -- 5. LI56 + BLT taken B+280 → B+332
  have hblt0 := sha256PadLiBlt_lt56 rem
    (scratchBase + BitVec.ofNat 64 rem)
    ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
      (.x6 ↦ᵣ (128 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion inputCursor input **
      bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
      regOwn .x28 ** F)
    (by pcf; exact hF) hrem
  have hblt : cpsTripleWithin 2 (B + 280) (B + 332) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ (56 : Word)) ** (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
        regOwn .x28 ** F) := by
    -- LiBlt uses CodeReq.ofProg B zkvmSha256_prog (= sha256Cr)
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hblt0
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c03 hblt
  -- Nested fuel: (((8+3)+(rem*7+1))+3)+2 = rem*7+17
  exact cpsTripleWithin_mono_nSteps
    (by omega : ((((8 + 3) + (rem * 7 + 1)) + 3) + 2) ≤ rem * 7 + 17) c04

/-! ## rem≥56 extra compress + re-zero (idx 72–82 @ B+288 → B+332) -/

private theorem la_extra_params_hi :
    Codegen.laHi GuestAddrs.sha256_w_params (GuestAddrs.zkvm_sha256 + 288) =
      Rv64.laHi (B + 288) ShaParams := by decide

private theorem la_extra_params_lo :
    Codegen.laLo GuestAddrs.sha256_w_params (GuestAddrs.zkvm_sha256 + 288) =
      Rv64.laLo (B + 288) ShaParams := by decide

private theorem la_extra_params_range : laInRange (B + 288) ShaParams := by decide

/-- `la x10, sha256_w_params` at B+288 (idx 72–73). -/
theorem sha256PadExtraLaParams_spec (v10 : Word) :
    cpsTripleWithin 2 (B + 288) (B + 296) sha256Cr
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ ShaParams) := by
  have hau : ∀ a i,
      CodeReq.singleton (B + 288)
        (.AUIPC .x10 (Rv64.laHi (B + 288) ShaParams)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := mem_at 72
      (.AUIPC .x10 (Codegen.laHi GuestAddrs.sha256_w_params
        (GuestAddrs.zkvm_sha256 + 288))) (B + 288) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    exact hmem a i (by rwa [← la_extra_params_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((B + 288) + 4)
        (.ADDI .x10 .x10 (Rv64.laLo (B + 288) ShaParams)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := mem_at 73
      (.ADDI .x10 .x10 (Codegen.laLo GuestAddrs.sha256_w_params
        (GuestAddrs.zkvm_sha256 + 288))) (B + 292) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    have hpc : (B + 288 : Word) + 4 = B + 292 := by decide
    rw [hpc, ← la_extra_params_lo] at hi
    exact hmem a i hi
  exact la_materialize_within .x10 v10 (B + 288) ShaParams
    (by decide) la_extra_params_range hau had

/-- la + CSRS for rem≥56 first pad block. Fuel 3. B+288 → B+300. -/
theorem sha256PadExtraCsrs_spec
    (scratchBase stateBase paramsBase : Word)
    (scratch state params : List (BitVec 8)) (payload : List Word)
    (v10 : Word)
    (hstate : state.length = 32) (hpayload : payload.length = 4)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
        bytesRegion stateBase state ** bytesRegion scratchBase scratch) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, payload)) :
    cpsTripleWithin 3 (B + 288) (B + 300) sha256Cr
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ scratchBase) **
        bytesRegion paramsBase params ** bytesRegion stateBase state **
        bytesRegion scratchBase scratch)
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) ** (.x21 ↦ᵣ scratchBase) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        bytesRegion scratchBase scratch) := by
  have hla := sha256PadExtraLaParams_spec v10
  have hlaF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ stateBase) ** (.x21 ↦ᵣ scratchBase) **
      bytesRegion paramsBase params ** bytesRegion stateBase state **
      bytesRegion scratchBase scratch) (by pcf) hla
  have hla' : cpsTripleWithin 2 (B + 288) (B + 296) sha256Cr
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ scratchBase) **
        bytesRegion paramsBase params ** bytesRegion stateBase state **
        bytesRegion scratchBase scratch)
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) ** (.x21 ↦ᵣ scratchBase) **
        bytesRegion paramsBase params ** bytesRegion stateBase state **
        bytesRegion scratchBase scratch) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hlaF
  have hcs := sha256ExternalCsrs_regs_spec_within (B + 296)
    paramsBase stateBase scratchBase params state scratch payload
    stateBase ShaParams scratchBase hstate hpayload hsem
  have hcs' := cpsTripleWithin_extend_code
    (mem_at 74 (.CSRS 0x805 .x10) (B + 296) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hcs
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hla' hcs'

private theorem extra_zero_ins (q : Nat) (hq : q < 8)
    (hidx : 75 + q < sha256ProgL.length) :
    sha256ProgL[75 + q]'hidx =
      .SD .x21 .x0 (BitVec.ofNat 12 (8 * q)) := by
  match q with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | _ + 8 => omega

/-- Zero one dword of scratch via `SD x21, x0, 8q` after extra compress.
    PC = B + 4*(75+q) = B+300+4q. -/
theorem sha256PadExtraZeroDword_spec (scratchBase : Word) (scratch : List (BitVec 8))
    (q : Nat) (hscratch : scratch.length = 64) (hq : q < 8) :
    cpsTripleWithin 1 (B + BitVec.ofNat 64 (4 * (75 + q)))
      (B + BitVec.ofNat 64 (4 * (75 + q)) + 4) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase scratch)
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase
          (setBytes scratch (8 * q) (dwordBytes (0 : Word)))) := by
  have hq_state : 8 * q + 8 ≤ scratch.length := by rw [hscratch]; omega
  have himm : 8 * q < 2 ^ 11 := by omega
  have hidx : 75 + q < sha256ProgL.length := by
    rw [sha256ProgL_len]; omega
  have hins := extra_zero_ins q hq hidx
  have hmem : ∀ a i,
      CodeReq.singleton (B + BitVec.ofNat 64 (4 * (75 + q)))
        (.SD .x21 .x0 (BitVec.ofNat 12 (8 * q))) a = some i →
        sha256Cr a = some i :=
    mem_at (75 + q) (.SD .x21 .x0 (BitVec.ofNat 12 (8 * q)))
      (B + BitVec.ofNat 64 (4 * (75 + q))) rfl hidx hins
  exact cpsTripleWithin_extend_code hmem
    (bytesRegion_sd_within .x21 .x0 scratchBase (0 : Word)
      (B + BitVec.ofNat 64 (4 * (75 + q))) scratch q hq_state himm)

private theorem extra_zero_pc (q : Nat) (hq : q < 8) :
    B + BitVec.ofNat 64 (4 * (75 + q)) = B + (300 + 4 * q : Nat) := by
  match q with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | _ + 8 => omega

private theorem extra_zero_exit (q : Nat) (hq : q < 8) :
    B + BitVec.ofNat 64 (4 * (75 + q)) + 4 = B + (300 + 4 * (q + 1) : Nat) := by
  have hpc := extra_zero_pc q hq
  have h4 : (B + (300 + 4 * q : Nat) : Word) + 4 = B + (300 + 4 * (q + 1) : Nat) := by
    match q with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | 6 => decide
    | 7 => decide
    | _ + 8 => omega
  rw [hpc, h4]

private theorem extra_step_at (scratchBase : Word) (scratch : List (BitVec 8))
    (q : Nat) (hscratch : scratch.length = 64) (hq : q < 8) :
    cpsTripleWithin 1 (B + (300 + 4 * q : Nat)) (B + (300 + 4 * (q + 1) : Nat))
      sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase scratch)
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase
          (setBytes scratch (8 * q) (dwordBytes (0 : Word)))) := by
  have h := sha256PadExtraZeroDword_spec scratchBase scratch q hscratch hq
  have hpc := extra_zero_pc q hq
  have hex := extra_zero_exit q hq
  convert h using 1
  · exact hpc.symm
  · exact hex.symm

/-- Full 8-dword re-zero after rem≥56 compress: B+300 → B+332. -/
theorem sha256PadExtraZeroBlock_spec (scratchBase : Word) (scratch : List (BitVec 8))
    (hscratch : scratch.length = 64) :
    cpsTripleWithin 8 (B + 300) (B + 332) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase scratch)
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroed scratch)) := by
  have s0 := extra_step_at scratchBase scratch 0 hscratch (by decide)
  have h1 := pad_zeroedN_len scratch hscratch 1
  have s1 := extra_step_at scratchBase (sha256PadZeroedN scratch 1) 1 h1 (by decide)
  have h2 := pad_zeroedN_len scratch hscratch 2
  have s2 := extra_step_at scratchBase (sha256PadZeroedN scratch 2) 2 h2 (by decide)
  have h3 := pad_zeroedN_len scratch hscratch 3
  have s3 := extra_step_at scratchBase (sha256PadZeroedN scratch 3) 3 h3 (by decide)
  have h4 := pad_zeroedN_len scratch hscratch 4
  have s4 := extra_step_at scratchBase (sha256PadZeroedN scratch 4) 4 h4 (by decide)
  have h5 := pad_zeroedN_len scratch hscratch 5
  have s5 := extra_step_at scratchBase (sha256PadZeroedN scratch 5) 5 h5 (by decide)
  have h6 := pad_zeroedN_len scratch hscratch 6
  have s6 := extra_step_at scratchBase (sha256PadZeroedN scratch 6) 6 h6 (by decide)
  have h7 := pad_zeroedN_len scratch hscratch 7
  have s7 := extra_step_at scratchBase (sha256PadZeroedN scratch 7) 7 h7 (by decide)
  have s0' : cpsTripleWithin 1 (B + 300) (B + 304) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase scratch)
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 1)) := by
    simpa [sha256PadZeroedN] using s0
  have s1' : cpsTripleWithin 1 (B + 304) (B + 308) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 1))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 2)) := by
    simpa [sha256PadZeroedN] using s1
  have s2' : cpsTripleWithin 1 (B + 308) (B + 312) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 2))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 3)) := by
    simpa [sha256PadZeroedN] using s2
  have s3' : cpsTripleWithin 1 (B + 312) (B + 316) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 3))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 4)) := by
    simpa [sha256PadZeroedN] using s3
  have s4' : cpsTripleWithin 1 (B + 316) (B + 320) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 4))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 5)) := by
    simpa [sha256PadZeroedN] using s4
  have s5' : cpsTripleWithin 1 (B + 320) (B + 324) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 5))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 6)) := by
    simpa [sha256PadZeroedN] using s5
  have s6' : cpsTripleWithin 1 (B + 324) (B + 328) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 6))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 7)) := by
    simpa [sha256PadZeroedN] using s6
  have s7' : cpsTripleWithin 1 (B + 328) (B + 332) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 7))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 8)) := by
    simpa [sha256PadZeroedN] using s7
  have c01 := cpsTripleWithin_seq_same_cr s0' s1'
  have c02 := cpsTripleWithin_seq_same_cr c01 s2'
  have c03 := cpsTripleWithin_seq_same_cr c02 s3'
  have c04 := cpsTripleWithin_seq_same_cr c03 s4'
  have c05 := cpsTripleWithin_seq_same_cr c04 s5'
  have c06 := cpsTripleWithin_seq_same_cr c05 s6'
  have c07 := cpsTripleWithin_seq_same_cr c06 s7'
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) c07
  simpa [sha256PadZeroedN_eight] using hq

/-- rem≥56 fall-through: la + CSRS + re-zero. Fuel 11. B+288 → B+332
    (bitlen join). Scratch post is `sha256PadZeroed` (same as pad-zero block).
    CSRS validity/write remains an explicit `hsem` residual (Block/Final shape). -/
theorem sha256PadExtraCompress_spec
    (scratchBase stateBase paramsBase : Word)
    (scratch state params : List (BitVec 8)) (payload : List Word)
    (v10 : Word)
    (hscratch : scratch.length = 64) (hstate : state.length = 32)
    (hpayload : payload.length = 4)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
        bytesRegion stateBase state ** bytesRegion scratchBase scratch) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, payload)) :
    cpsTripleWithin 11 (B + 288) (B + 332) sha256Cr
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ scratchBase) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion paramsBase params ** bytesRegion stateBase state **
        bytesRegion scratchBase scratch)
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) ** (.x21 ↦ᵣ scratchBase) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        bytesRegion scratchBase (sha256PadZeroed scratch)) := by
  have hcs := sha256PadExtraCsrs_spec scratchBase stateBase paramsBase
    scratch state params payload v10 hstate hpayload hsem
  have hcsF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word))) (by pcf) hcs
  have hcs' : cpsTripleWithin 3 (B + 288) (B + 300) sha256Cr
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ scratchBase) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion paramsBase params ** bytesRegion stateBase state **
        bytesRegion scratchBase scratch)
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) ** (.x21 ↦ᵣ scratchBase) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        bytesRegion scratchBase scratch) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hcsF
  have hz := sha256PadExtraZeroBlock_spec scratchBase scratch hscratch
  have hzF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
      bytesRegion paramsBase params **
      bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)))
    (by pcf) hz
  have hz' : cpsTripleWithin 8 (B + 300) (B + 332) sha256Cr
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) ** (.x21 ↦ᵣ scratchBase) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        bytesRegion scratchBase scratch)
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) ** (.x21 ↦ᵣ scratchBase) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        bytesRegion scratchBase (sha256PadZeroed scratch)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hzF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hcs' hz'

/-! ## rem≥56 pad spine compose: B+196 → B+332 -/

/-- Scratch after rem≥56 pad: rem-prefix + 0x80, then CSRS, then full re-zero. -/
def sha256PadScratch_ge56 (input scratch0 : List (BitVec 8)) (rem : Nat) :
    List (BitVec 8) :=
  sha256PadZeroed (sha256PadScratch_lt56 input scratch0 rem)

theorem length_sha256PadScratch_ge56 (input scratch0 : List (BitVec 8)) (rem : Nat)
    (hs : scratch0.length = 64) (hrem : rem < 64) (hinp : rem ≤ input.length) :
    (sha256PadScratch_ge56 input scratch0 rem).length = 64 := by
  have hmid := length_sha256PadScratch_lt56 input scratch0 rem hs hrem hinp
  simpa [sha256PadScratch_ge56] using length_sha256PadZeroed
    (sha256PadScratch_lt56 input scratch0 rem) hmid

/-- rem≥56 pad spine: zero → rem setup → rem copy → 0x80 → LI56/BLT fall →
    ExtraCompress (la+CSRS+re-zero). Fuel `rem*7+28`. B+196 → B+332 (bitlen join).
    Does not include bitlen write (`sha256Bitlen_write_spec` B+332→B+396). -/
theorem sha256PadPath_ge56_spec
    (scratchBase inputCursor stateBase paramsBase : Word)
    (input scratch0 state params : List (BitVec 8)) (payload : List Word)
    (rem : Nat)
    (v5 v6 v7 v10 : Word)
    (F : Assertion) (hF : F.pcFree)
    (hsrcAlign : inputCursor.toNat % 8 = 0)
    (hdstAlign : scratchBase.toNat % 8 = 0)
    (hscratch : scratch0.length = 64)
    (hstate : state.length = 32) (hpayload : payload.length = 4)
    (hinp : rem ≤ input.length)
    (hrem : 56 ≤ rem) (hrem64 : rem < 64)
    (hsrcOver : inputCursor.toNat + rem ≤ 2 ^ 64)
    (hdstSpan : scratchBase.toNat + 64 ≤ 2 ^ 64)
    (hvalidS : ∀ i < rem, isValidByteAccess (inputCursor + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i < rem, isValidByteAccess (scratchBase + BitVec.ofNat 64 i) = true)
    (hvalidPad : isValidByteAccess (scratchBase + BitVec.ofNat 64 rem) = true)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
        bytesRegion stateBase state **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem)) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, payload)) :
    cpsTripleWithin (rem * 7 + 28) (B + 196) (B + 332) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase scratch0 **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x5 ↦ᵣ (56 : Word)) ** (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_ge56 input scratch0 rem) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        regOwn .x28 ** F) := by
  have hremBound : rem < 2 ^ 64 := by omega
  have hdstOver : scratchBase.toNat + rem ≤ 2 ^ 64 := by omega
  have hdstHover : scratchBase.toNat + rem < 2 ^ 64 := by omega
  have hzLen := length_sha256PadZeroed scratch0 hscratch
  let Fearly : Assertion :=
    (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
      bytesRegion paramsBase params ** bytesRegion stateBase state ** F
  -- 1. Zero block B+196 → B+228
  have hz0 := sha256PadZeroBlock_spec scratchBase scratch0 hscratch
  have hzF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      bytesRegion inputCursor input ** regOwn .x28 ** Fearly)
    (by pcf; exact hF) hz0
  have hz : cpsTripleWithin 8 (B + 196) (B + 228) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase scratch0 **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadZeroed scratch0) **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hzF
  -- 2. Rem setup B+228 → B+240
  have hs0 := sha256PadRemSetup_spec scratchBase inputCursor
    (BitVec.ofNat 64 rem) v5 v6 v7
    ((.x0 ↦ᵣ (0 : Word)) ** bytesRegion inputCursor input **
      bytesRegion scratchBase (sha256PadZeroed scratch0) **
      regOwn .x28 ** Fearly)
    (by pcf; exact hF)
  have hs : cpsTripleWithin 3 (B + 228) (B + 240) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadZeroed scratch0) **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) **
        (.x7 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadZeroed scratch0) **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hs0
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hz hs
  -- 3. Rem copy loop B+240 → B+268
  let Floop : Assertion :=
    (.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
      (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** Fearly
  have hFloop : Floop.pcFree := by pcf; exact hF
  have hloop0 := sha256RemCopy_loop scratchBase inputCursor input
    (sha256PadZeroed scratch0) rem hsrcAlign hdstAlign hinp hzLen
    (by omega) hsrcOver hdstOver hremBound hvalidS hvalidD Floop hFloop
  have hcur0 (p : Word) : p + BitVec.ofNat 64 0 = p := by
    rw [ofNat_zero]; exact BitVec.add_zero p
  have hloop : cpsTripleWithin (rem * 7 + 1) (B + 240) (B + 268) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) **
        (.x7 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadZeroed scratch0) **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 rem)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase
          (sha256RemPrefix input (sha256PadZeroed scratch0) rem) **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hloop0
    · simp only [sha256RemInv, Floop, Fearly, hcur0] at hp ⊢
      xperm_chunked hp
    · simp only [sha256RemDone, Floop, Fearly] at hq ⊢
      xperm_chunked hq
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hloop
  -- 4. Pad 0x80 B+268 → B+280
  have hprefLen := sha256RemPrefix_length input (sha256PadZeroed scratch0) rem hzLen
    (by omega) hinp
  have hbit0 := sha256PadBit_spec scratchBase rem
    (sha256RemPrefix input (sha256PadZeroed scratch0) rem)
    hdstAlign hprefLen hrem64 hdstHover hvalidPad
    ((.x9 ↦ᵣ inputCursor) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion inputCursor input ** regOwn .x28 ** Fearly)
    (by pcf; exact hF)
    (scratchBase + BitVec.ofNat 64 rem)
    (inputCursor + BitVec.ofNat 64 rem)
    (0 : Word)
  have hbit : cpsTripleWithin 3 (B + 268) (B + 280) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x6 ↦ᵣ (inputCursor + BitVec.ofNat 64 rem)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase
          (sha256RemPrefix input (sha256PadZeroed scratch0) rem) **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => ?_) hbit0
    simp only [sha256PadScratch_lt56, Fearly] at hq ⊢
    xperm_chunked hq
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c02 hbit
  -- 5. LI56 + BLT fall-through B+280 → B+288
  have hblt0 := sha256PadLiBlt_ge56 rem
    (scratchBase + BitVec.ofNat 64 rem)
    ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
      (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
      (.x6 ↦ᵣ (128 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion inputCursor input **
      bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
      bytesRegion paramsBase params **
      bytesRegion stateBase state **
      regOwn .x28 ** F)
    (by pcf; exact hF) hrem hrem64
  have hblt : cpsTripleWithin 2 (B + 280) (B + 288) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ (56 : Word)) ** (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hblt0
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c03 hblt
  -- 6. ExtraCompress B+288 → B+332
  have hmidLen := length_sha256PadScratch_lt56 input scratch0 rem hscratch hrem64 hinp
  have hex0 := sha256PadExtraCompress_spec scratchBase stateBase paramsBase
    (sha256PadScratch_lt56 input scratch0 rem) state params payload v10
    hmidLen hstate hpayload hsem
  have hexF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
      (.x5 ↦ᵣ (56 : Word)) ** (.x6 ↦ᵣ (128 : Word)) **
      (.x7 ↦ᵣ (0 : Word)) **
      bytesRegion inputCursor input ** regOwn .x28 ** F)
    (by pcf; exact hF) hex0
  have hex : cpsTripleWithin 11 (B + 288) (B + 332) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ (56 : Word)) ** (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x5 ↦ᵣ (56 : Word)) ** (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_ge56 input scratch0 rem) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        regOwn .x28 ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => ?_) hexF
    simp only [sha256PadScratch_ge56] at hq ⊢
    xperm_chunked hq
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c04 hex
  -- Nested fuel: ((((8+3)+(rem*7+1))+3)+2)+11 = rem*7+28
  exact cpsTripleWithin_mono_nSteps
    (by omega : (((((8 + 3) + (rem * 7 + 1)) + 3) + 2) + 11) ≤ rem * 7 + 28) c05

end EvmAsm.Codegen.Proofs









