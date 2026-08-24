/-
  EvmAsm.Codegen.Programs.AssembleExecutionRequestsCopy

  The byte-copy loop of `assemble_execution_requests` (#12206), proved ONCE and
  parameterised over the loop's top instruction index `b`, its source pointer,
  and the destination region base + byte offset.

  `assembleExecutionRequests_prog` contains the same seven instructions five
  times over (BEQ tops at indices 16, 25, 34, 47, 60):

      b+0  BEQ  x28, x0, +28      -- countdown exhausted → b+7
      b+1  LBU  x29, 0(x7)
      b+2  SB   x29, 0(x6)
      b+3  ADDI x6, x6, 1
      b+4  ADDI x7, x7, 1
      b+5  ADDI x28, x28, -1
      b+6  JAL  x0, -24           -- → b+0

  Only the *setup* differs between the five (register moves for loops 1–3, a
  `la` + `LD` pair from the `aer_bd_*` / `aer_be_*` globals for loops 4–5), so
  the loop itself is one lemma applied five times rather than five proofs.

  Aliasing: the precondition holds `bytesRegion srcPtr src ** bytesRegion
  dstBase dst` separately, so source/destination non-overlap is a genuine
  requirement of the loop contract and not a formality — see the row gate.

  Pattern: `ExecutionRequestsHashHashOneCopy.hash_one_copy_{step,loop}`, which
  is the same seven-instruction shape over a fixed BSS destination; this module
  generalises the destination from that fixed `Blob` to `(dstBase, dstOff)` and
  the loop site from a fixed index to `b`.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.Programs.AssembleExecutionRequestsBase

namespace EvmAsm.Codegen.AssembleExecutionRequestsCopy

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.AssembleExecutionRequestsBase

set_option maxRecDepth 8000

local macro "pcf" : tactic =>
  `(tactic| repeat' first
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_emp
      | apply pcFree_sepConj)

/-! ## The loop's code-membership obligations -/

/-- The seven code-membership facts for the copy loop whose `BEQ` top sits at
    instruction index `b` of `assembleExecutionRequests_prog`. Discharged at
    each of the five sites by `mem_at … (by decide)`. -/
structure CopyCode (b : Nat) : Prop where
  beq : ∀ a i, CodeReq.singleton (pc b) (.BEQ .x28 .x0 (28 : BitVec 13)) a = some i →
    aerCode a = some i
  lbu : ∀ a i, CodeReq.singleton (pc (b + 1)) (.LBU .x29 .x7 (0 : BitVec 12)) a = some i →
    aerCode a = some i
  sb : ∀ a i, CodeReq.singleton (pc (b + 2)) (.SB .x6 .x29 (0 : BitVec 12)) a = some i →
    aerCode a = some i
  add6 : ∀ a i, CodeReq.singleton (pc (b + 3)) (.ADDI .x6 .x6 (1 : BitVec 12)) a = some i →
    aerCode a = some i
  add7 : ∀ a i, CodeReq.singleton (pc (b + 4)) (.ADDI .x7 .x7 (1 : BitVec 12)) a = some i →
    aerCode a = some i
  dec : ∀ a i, CodeReq.singleton (pc (b + 5)) (.ADDI .x28 .x28 (-1 : BitVec 12)) a = some i →
    aerCode a = some i
  jal : ∀ a i, CodeReq.singleton (pc (b + 6)) (.JAL .x0 (-24 : BitVec 21)) a = some i →
    aerCode a = some i

/-! ## Word arithmetic -/

private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se12_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide

private theorem ofNat_zero : BitVec.ofNat 64 0 = (0 : Word) := rfl

private theorem one_plus_neg1 : (1 : Word) + (-1 : Word) = 0 := by decide

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
  have e1 : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + (1 : Word) :=
    (ofNat_succ k).symm
  calc
    BitVec.ofNat 64 (k + 1) + (-1 : Word)
        = (BitVec.ofNat 64 k + (1 : Word)) + (-1 : Word) := by rw [e1]
    _ = BitVec.ofNat 64 k + ((1 : Word) + (-1 : Word)) := by rw [BitVec.add_assoc]
    _ = BitVec.ofNat 64 k + (0 : Word) := by rw [one_plus_neg1]
    _ = BitVec.ofNat 64 k := BitVec.add_zero _

/-! ## Invariant -/

/-- Loop invariant: `done` bytes copied, `k` remaining, cursors `x6`/`x7`
    advanced, `x28` the countdown. `F` is the opaque pcFree ambient. -/
def copyInv (srcPtr dstBase : Word) (src dst : List (BitVec 8))
    (dstOff k done : Nat) (F : Assertion) : Assertion :=
  (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + done))) **
  (.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 done)) **
  (.x28 ↦ᵣ BitVec.ofNat 64 k) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion srcPtr src **
  bytesRegion dstBase dst **
  regOwn .x29 ** F

/-- Loop exit state: `x28 = 0`, cursors parked after the copied run. -/
def copyDone (srcPtr dstBase : Word) (src dst : List (BitVec 8))
    (dstOff done : Nat) (F : Assertion) : Assertion :=
  (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + done))) **
  (.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 done)) **
  (.x28 ↦ᵣ (0 : Word)) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion srcPtr src **
  bytesRegion dstBase dst **
  regOwn .x29 ** F

theorem copyInv_pcFree (srcPtr dstBase : Word) (src dst : List (BitVec 8))
    (dstOff k done : Nat) (F : Assertion) (hF : F.pcFree) :
    (copyInv srcPtr dstBase src dst dstOff k done F).pcFree := by
  simp only [copyInv]; pcf; exact hF

theorem copyDone_pcFree (srcPtr dstBase : Word) (src dst : List (BitVec 8))
    (dstOff done : Nat) (F : Assertion) (hF : F.pcFree) :
    (copyDone srcPtr dstBase src dst dstOff done F).pcFree := by
  simp only [copyDone]; pcf; exact hF

/-! ## The two loop transitions -/

/-- `BEQ` taken (countdown exhausted). Fuel 1. `pc b → pc (b+7)`. -/
theorem aer_copy_exit_zero (b : Nat) (hc : CopyCode b)
    (srcPtr dstBase : Word) (src dst : List (BitVec 8))
    (dstOff done : Nat)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc b) (pc (b + 7)) aerCode
      (copyInv srcPtr dstBase src dst dstOff 0 done F)
      (copyDone srcPtr dstBase src dst dstOff done F) := by
  have hbr := beq_spec_gen_within .x28 .x0 (28 : BitVec 13) (0 : Word) (0 : Word) (pc b)
  have hbrC := cpsBranchWithin_extend_code hc.beq hbr
  have hbrT := cpsBranchWithin_takenStripPure2 hbrC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  rw [pc_beq_exit b] at hbrT
  have hbrF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + done))) **
     (.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 done)) **
     bytesRegion srcPtr src ** bytesRegion dstBase dst **
     regOwn .x29 ** F)
    (by pcf; exact hF) hbrT
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [copyInv, ofNat_zero] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by
      simp only [copyDone] at hq ⊢; xperm_chunked hq)
    hbrF

/-- One iteration: remaining `k+1 → k`, `done → done+1`. Fuel 7.
    `pc b → pc b`. -/
theorem aer_copy_step (b : Nat) (hc : CopyCode b)
    (srcPtr dstBase : Word) (src dst0 : List (BitVec 8))
    (dstOff k done : Nat)
    (hsrc : done < src.length)
    (hdst : dstOff + done < dst0.length)
    (hsrcAlign : srcPtr.toNat % 8 = 0)
    (hdstAlign : dstBase.toNat % 8 = 0)
    (hsrcOver : srcPtr.toNat + done < 2 ^ 64)
    (hdstOver : dstBase.toNat + (dstOff + done) < 2 ^ 64)
    (hkbound : k + 1 < 2 ^ 64)
    (hvalidS : isValidByteAccess (srcPtr + BitVec.ofNat 64 done) = true)
    (hvalidD : isValidByteAccess (dstBase + BitVec.ofNat 64 (dstOff + done)) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (pc b) (pc b) aerCode
      (copyInv srcPtr dstBase src dst0 dstOff (k + 1) done F)
      (copyInv srcPtr dstBase src (dst0.set (dstOff + done) (src[done]'hsrc))
        dstOff k (done + 1) F) := by
  have hne := word_ofNat_succ_ne_zero k hkbound
  -- BEQ not taken
  have hbr := beq_spec_gen_within .x28 .x0 (28 : BitVec 13)
    (BitVec.ofNat 64 (k + 1)) (0 : Word) (pc b)
  have hbrC := cpsBranchWithin_extend_code hc.beq hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hQ).2)
  rw [pc_succ b] at hnt
  have hbeq := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + done))) **
     (.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 done)) **
     bytesRegion srcPtr src ** bytesRegion dstBase dst0 **
     regOwn .x29 ** F)
    (by pcf; exact hF) hnt
  -- LBU x29 (own trailing)
  have hlbu : ∀ v29,
      cpsTripleWithin 1 (pc (b + 1)) (pc (b + 2)) aerCode
        (((.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 done)) **
          bytesRegion srcPtr src **
          (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + done))) **
          (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion dstBase dst0 ** F) **
         (.x29 ↦ᵣ v29))
        ((.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 done)) **
          (.x29 ↦ᵣ ((src[done]'hsrc).zeroExtend 64)) **
          bytesRegion srcPtr src **
          (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + done))) **
          (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion dstBase dst0 ** F) := by
    intro v29
    have hl := bytesRegion_lbu_within .x29 .x7 srcPtr v29 (pc (b + 1))
      src done (by decide) hsrcAlign hsrc hsrcOver hvalidS
    have hlE := cpsTripleWithin_extend_code hc.lbu hl
    rw [pc_succ (b + 1)] at hlE
    have hFr := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + done))) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion dstBase dst0 ** F)
      (by pcf; exact hF) hlE
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hFr
  have hlbuOwn := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x29) hlbu
  -- SB
  have hsb0 := bytesRegion_sb_within .x6 .x29 dstBase
    ((src[done]'hsrc).zeroExtend 64) (pc (b + 2)) dst0 (dstOff + done)
    hdstAlign hdst hdstOver hvalidD
  have hsb := cpsTripleWithin_extend_code hc.sb hsb0
  rw [pc_succ (b + 2)] at hsb
  have hbyte :
      ((src[done]'hsrc).zeroExtend 64).truncate 8 = src[done]'hsrc :=
    truncate_zeroExtend_byte _
  simp only [hbyte] at hsb
  have hsbF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 done)) **
     (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion srcPtr src ** F)
    (by pcf; exact hF) hsb
  -- ADDI x6, +1
  have hadd60 := addi_spec_gen_same_within .x6
    (dstBase + BitVec.ofNat 64 (dstOff + done)) (1 : BitVec 12) (pc (b + 3)) (by decide)
  have hadd6 := cpsTripleWithin_extend_code hc.add6 hadd60
  rw [pc_succ (b + 3), se12_1] at hadd6
  have hadd6F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 done)) **
     (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x29 ↦ᵣ ((src[done]'hsrc).zeroExtend 64)) **
     bytesRegion srcPtr src **
     bytesRegion dstBase (dst0.set (dstOff + done) (src[done]'hsrc)) ** F)
    (by pcf; exact hF) hadd6
  -- ADDI x7, +1
  have hadd70 := addi_spec_gen_same_within .x7
    (srcPtr + BitVec.ofNat 64 done) (1 : BitVec 12) (pc (b + 4)) (by decide)
  have hadd7 := cpsTripleWithin_extend_code hc.add7 hadd70
  rw [pc_succ (b + 4), se12_1] at hadd7
  have hadd7F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + done) + (1 : Word))) **
     (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x29 ↦ᵣ ((src[done]'hsrc).zeroExtend 64)) **
     bytesRegion srcPtr src **
     bytesRegion dstBase (dst0.set (dstOff + done) (src[done]'hsrc)) ** F)
    (by pcf; exact hF) hadd7
  -- ADDI x28, -1
  have hadd280 := addi_spec_gen_same_within .x28
    (BitVec.ofNat 64 (k + 1)) (-1 : BitVec 12) (pc (b + 5)) (by decide)
  have hadd28 := cpsTripleWithin_extend_code hc.dec hadd280
  rw [pc_succ (b + 5), se12_m1] at hadd28
  have hadd28F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + done) + (1 : Word))) **
     (.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 done + (1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x29 ↦ᵣ ((src[done]'hsrc).zeroExtend 64)) **
     bytesRegion srcPtr src **
     bytesRegion dstBase (dst0.set (dstOff + done) (src[done]'hsrc)) ** F)
    (by pcf; exact hF) hadd28
  -- JAL back to the loop top
  have hjal0 := jal_x0_spec_gen_within (-24 : BitVec 21) (pc (b + 6))
  have hjal := cpsTripleWithin_extend_code hc.jal hjal0
  rw [pc_jal_back b] at hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + done) + (1 : Word))) **
     (.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 done + (1 : Word))) **
     (.x28 ↦ᵣ (BitVec.ofNat 64 (k + 1) + (-1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x29 ↦ᵣ ((src[done]'hsrc).zeroExtend 64)) **
     bytesRegion srcPtr src **
     bytesRegion dstBase (dst0.set (dstOff + done) (src[done]'hsrc)) ** F)
    (by pcf; exact hF) hjal
  have hjalW := cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hjalF
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hbeq hlbuOwn
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0 hsbF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hadd6F
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hadd7F
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 hadd28F
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01234 hjalW
  have hcur7 := cursor_succ srcPtr done
  have hrem := cnt_step_down k
  have hcur6 :
      dstBase + BitVec.ofNat 64 (dstOff + done) + (1 : Word) =
        dstBase + BitVec.ofNat 64 (dstOff + (done + 1)) := by
    rw [show dstOff + (done + 1) = (dstOff + done) + 1 from by omega]
    exact cursor_succ dstBase (dstOff + done)
  refine cpsTripleWithin_weaken ?_ ?_ c
  · intro h hp
    simp only [copyInv] at hp ⊢; xperm_chunked hp
  · intro h hq
    have hq1 :
        ((.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (done + 1)))) **
         (.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 (done + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion srcPtr src **
         bytesRegion dstBase (dst0.set (dstOff + done) (src[done]'hsrc)) **
         (.x29 ↦ᵣ ((src[done]'hsrc).zeroExtend 64)) ** F) h := by
      simp only [hcur6, hcur7, hrem] at hq
      xperm_chunked hq
    have hq2 :
        ((.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (done + 1)))) **
         (.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 (done + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion srcPtr src **
         bytesRegion dstBase (dst0.set (dstOff + done) (src[done]'hsrc)) **
         regOwn .x29 ** F) h := by
      have hx :
          (((.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (done + 1)))) **
            (.x7 ↦ᵣ (srcPtr + BitVec.ofNat 64 (done + 1))) **
            (.x28 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcPtr src **
            bytesRegion dstBase (dst0.set (dstOff + done) (src[done]'hsrc)) ** F) **
           (.x29 ↦ᵣ ((src[done]'hsrc).zeroExtend 64))) h := by
        xperm_chunked hq1
      have hx' := sepConj_mono_right (regIs_implies_regOwn (r := .x29)) h hx
      xperm_chunked hx'
    simpa only [copyInv] using hq2

/-! ## The pure destination update -/

/-- `k` successive byte writes of `src[done …]` into `dst0` at `dstOff + …`. -/
def copyDst (src : List (BitVec 8)) (dst0 : List (BitVec 8))
    (dstOff done k : Nat) : List (BitVec 8) :=
  match k with
  | 0 => dst0
  | k' + 1 =>
      let d := copyDst src dst0 dstOff done k'
      if h : done + k' < src.length then
        d.set (dstOff + (done + k')) (src[done + k']'h)
      else d

theorem copyDst_zero (src dst0 : List (BitVec 8)) (dstOff done : Nat) :
    copyDst src dst0 dstOff done 0 = dst0 := rfl

theorem copyDst_succ (src dst0 : List (BitVec 8)) (dstOff done k : Nat)
    (h : done + k < src.length) :
    copyDst src dst0 dstOff done (k + 1) =
      (copyDst src dst0 dstOff done k).set (dstOff + (done + k)) (src[done + k]'h) := by
  simp only [copyDst, h, ↓reduceDIte]

theorem copyDst_length (src dst0 : List (BitVec 8)) (dstOff done k : Nat) :
    (copyDst src dst0 dstOff done k).length = dst0.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [copyDst]
    split <;> simp [List.length_set, ih]

theorem copyDst_after_set (src dst0 : List (BitVec 8))
    (dstOff done k : Nat) (h0 : done < src.length)
    (hfit : done + 1 + k ≤ src.length) :
    copyDst src (dst0.set (dstOff + done) (src[done]'h0)) dstOff (done + 1) k =
      copyDst src dst0 dstOff done (k + 1) := by
  induction k generalizing dst0 with
  | zero =>
    simp only [copyDst_zero]
    exact (copyDst_succ src dst0 dstOff done 0 h0).symm
  | succ k ih =>
    have hdk : done + 1 + k < src.length := by omega
    have hdk' : done + (k + 1) < src.length := by omega
    have lhs :=
      copyDst_succ src (dst0.set (dstOff + done) (src[done]'h0)) dstOff (done + 1) k hdk
    have rhs := copyDst_succ src dst0 dstOff done (k + 1) hdk'
    have heq : copyDst src (dst0.set (dstOff + done) (src[done]'h0)) dstOff (done + 1) k =
        copyDst src dst0 dstOff done (k + 1) :=
      ih dst0 (by omega)
    calc
      copyDst src (dst0.set (dstOff + done) (src[done]'h0)) dstOff (done + 1) (k + 1)
          = (copyDst src (dst0.set (dstOff + done) (src[done]'h0)) dstOff (done + 1) k).set
              (dstOff + (done + 1 + k)) (src[done + 1 + k]'hdk) := lhs
      _ = (copyDst src dst0 dstOff done (k + 1)).set
              (dstOff + (done + 1 + k)) (src[done + 1 + k]'hdk) := by rw [heq]
      _ = (copyDst src dst0 dstOff done (k + 1)).set
              (dstOff + (done + (k + 1))) (src[done + (k + 1)]'hdk') := by
            congr 1
            · omega
            · congr 1; omega
      _ = copyDst src dst0 dstOff done (k + 1 + 1) := rhs.symm

/-- Appending one byte to a splice payload is one more `List.set`. -/
theorem setBytes_concat (bs ns : List (BitVec 8)) (i : Nat) (b : BitVec 8) :
    setBytes bs i (ns ++ [b]) = (setBytes bs i ns).set (i + ns.length) b := by
  induction ns generalizing bs i with
  | nil => simp only [List.nil_append, setBytes_cons, setBytes_nil, List.length_nil,
      Nat.add_zero]
  | cons c rest ih =>
    simp only [List.cons_append, setBytes_cons, ih, List.length_cons]
    congr 1
    omega

theorem copyDst_eq_setBytes_gen (src ob : List (BitVec 8)) (dstOff done k : Nat)
    (h : done + k ≤ src.length) :
    copyDst src ob dstOff done k = setBytes ob (dstOff + done) ((src.drop done).take k) := by
  induction k with
  | zero => simp only [copyDst_zero, List.take_zero, setBytes_nil]
  | succ k ih =>
    have hk : done + k < src.length := by omega
    have hlt : k < (src.drop done).length := by rw [List.length_drop]; omega
    have hsplit : (src.drop done).take (k + 1)
        = ((src.drop done).take k) ++ [src[done + k]'hk] := by
      rw [List.take_succ, List.getElem?_eq_getElem hlt]
      simp [List.getElem_drop]
    rw [copyDst_succ src ob dstOff done k hk, ih (by omega), hsplit, setBytes_concat]
    congr 1
    rw [List.length_take, List.length_drop]
    omega

/-- **The loop's net effect on the destination**: `src` spliced in at byte
    offset `dstOff`. -/
theorem copyDst_eq_setBytes (src ob : List (BitVec 8)) (dstOff : Nat) :
    copyDst src ob dstOff 0 src.length = setBytes ob dstOff src := by
  rw [copyDst_eq_setBytes_gen src ob dstOff 0 src.length (by omega)]
  simp

/-! ## The whole loop -/

/-- Fuel for a `k`-byte run of the loop. -/
def copyFuel (k : Nat) : Nat := k * 7 + 1

/-- **The copy loop, once.** From `k` bytes remaining at `pc b` to the loop
    exit `pc (b+7)`, having written `src[done … done+k)` into `dst0` at byte
    offsets `dstOff + done …`. Fuel `7k + 1`. -/
theorem aer_copy_loop (b : Nat) (hc : CopyCode b)
    (srcPtr dstBase : Word) (src dst0 : List (BitVec 8))
    (dstOff k done : Nat)
    (hfit : done + k ≤ src.length)
    (hdstLen : dstOff + src.length ≤ dst0.length)
    (hsrcAlign : srcPtr.toNat % 8 = 0)
    (hdstAlign : dstBase.toNat % 8 = 0)
    (hsrcOver : srcPtr.toNat + src.length < 2 ^ 64)
    (hdstOver : dstBase.toNat + (dstOff + src.length) < 2 ^ 64)
    (hvalidS : ∀ i, i < src.length →
      isValidByteAccess (srcPtr + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i, i < src.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 (dstOff + i)) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin (copyFuel k) (pc b) (pc (b + 7)) aerCode
      (copyInv srcPtr dstBase src dst0 dstOff k done F)
      (copyDone srcPtr dstBase src (copyDst src dst0 dstOff done k)
        dstOff (done + k) F) := by
  induction k generalizing dst0 done with
  | zero =>
    simp only [copyFuel, Nat.zero_mul, Nat.zero_add, copyDst_zero, Nat.add_zero]
    exact aer_copy_exit_zero b hc srcPtr dstBase src dst0 dstOff done F hF
  | succ k ih =>
    have h0 : done < src.length := by omega
    have hstep := aer_copy_step b hc srcPtr dstBase src dst0 dstOff k done
      h0 (by omega) hsrcAlign hdstAlign (by omega) (by omega) (by omega)
      (hvalidS done h0) (hvalidD done h0) F hF
    have hih := ih (dst0.set (dstOff + done) (src[done]'h0)) (done + 1)
      (by omega) (by rw [List.length_set]; exact hdstLen)
    have hseq := cpsTripleWithin_seq_same_cr hstep hih
    have hfuel : copyFuel (k + 1) = 7 + copyFuel k := by
      simp only [copyFuel]; omega
    have hdst_eq :
        copyDst src (dst0.set (dstOff + done) (src[done]'h0)) dstOff (done + 1) k =
          copyDst src dst0 dstOff done (k + 1) :=
      copyDst_after_set src dst0 dstOff done k h0 (by omega)
    have hseq' :
        cpsTripleWithin (copyFuel (k + 1)) (pc b) (pc (b + 7)) aerCode
          (copyInv srcPtr dstBase src dst0 dstOff (k + 1) done F)
          (copyDone srcPtr dstBase src
            (copyDst src (dst0.set (dstOff + done) (src[done]'h0)) dstOff (done + 1) k)
            dstOff (done + 1 + k) F) := by
      simpa [hfuel] using hseq
    refine cpsTripleWithin_weaken ?_ ?_ hseq'
    · intro h hp; exact hp
    · intro h hq
      rw [hdst_eq] at hq
      simpa [show done + 1 + k = done + (k + 1) from by omega] using hq

end EvmAsm.Codegen.AssembleExecutionRequestsCopy
