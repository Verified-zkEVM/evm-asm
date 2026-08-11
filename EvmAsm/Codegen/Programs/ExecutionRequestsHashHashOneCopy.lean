/-
  ExecutionRequestsHashHashOneCopy — nonempty body byte-copy loop.

  Geometry pc8→pc15 (top-tested BEQ countdown):
    8   BEQ x28,x0 → pc15
    9   LBU x29, 0(x7)
    10  SB  x6, x29, 0
    11  ADDI x6, x6, 1
    12  ADDI x7, x7, 1
    13  ADDI x28, x28, -1
    14  JAL x0, -24 → pc8

  Domain: bodyPtr % 8 = 0 (LBU framing); Blob BSS aligned;
  blob scratch length ≥ 1+body.length; lenW = ofNat body.length.
  Parent: #12011 option B. Owner #12018 for residual sha.
  Pattern: MptWalkLeafValue.leaf_copy_step.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOne
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneBody
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneEmpty

namespace EvmAsm.Codegen.ExecutionRequestsHashHashOneCopy

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashHashOne
open EvmAsm.Codegen.ExecutionRequestsHashHashOneBody
open EvmAsm.Codegen.ExecutionRequestsHashHashOneEmpty

set_option maxRecDepth 8000

local macro "pcf" : tactic =>
  `(tactic| repeat' first
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_stackFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_emp
      | apply pcFree_sepConj)

private theorem ho_ins8 :
    hoProgL[8]'(by rw [hoProgL_len]; norm_num) =
      .BEQ .x28 .x0 (28 : BitVec 13) := by decide
private theorem ho_ins9 :
    hoProgL[9]'(by rw [hoProgL_len]; norm_num) =
      .LBU .x29 .x7 (0 : BitVec 12) := by decide
private theorem ho_ins10 :
    hoProgL[10]'(by rw [hoProgL_len]; norm_num) =
      .SB .x6 .x29 (0 : BitVec 12) := by decide
private theorem ho_ins11 :
    hoProgL[11]'(by rw [hoProgL_len]; norm_num) =
      .ADDI .x6 .x6 (1 : BitVec 12) := by decide
private theorem ho_ins12 :
    hoProgL[12]'(by rw [hoProgL_len]; norm_num) =
      .ADDI .x7 .x7 (1 : BitVec 12) := by decide
private theorem ho_ins13 :
    hoProgL[13]'(by rw [hoProgL_len]; norm_num) =
      .ADDI .x28 .x28 (-1 : BitVec 12) := by decide
private theorem ho_ins14 :
    hoProgL[14]'(by rw [hoProgL_len]; norm_num) =
      .JAL .x0 (-24 : BitVec 21) := by decide

private theorem hpc8 : pc 8 = B1 + 32 := by simp only [pc]; decide
private theorem hpc9 : pc 9 = B1 + 36 := by simp only [pc]; decide
private theorem hpc10 : pc 10 = B1 + 40 := by simp only [pc]; decide
private theorem hpc11 : pc 11 = B1 + 44 := by simp only [pc]; decide
private theorem hpc12 : pc 12 = B1 + 48 := by simp only [pc]; decide
private theorem hpc13 : pc 13 = B1 + 52 := by simp only [pc]; decide
private theorem hpc14 : pc 14 = B1 + 56 := by simp only [pc]; decide
private theorem hpc15 : pc 15 = B1 + 60 := by simp only [pc]; decide

private theorem hpc89 : (pc 8 : Word) + 4 = pc 9 := by simp only [pc]; decide
private theorem hpc910 : (pc 9 : Word) + 4 = pc 10 := by simp only [pc]; decide
private theorem hpc1011 : (pc 10 : Word) + 4 = pc 11 := by simp only [pc]; decide
private theorem hpc1112 : (pc 11 : Word) + 4 = pc 12 := by simp only [pc]; decide
private theorem hpc1213 : (pc 12 : Word) + 4 = pc 13 := by simp only [pc]; decide
private theorem hpc1314 : (pc 13 : Word) + 4 = pc 14 := by simp only [pc]; decide
private theorem hpc815 : (pc 8 : Word) + signExtend13 (28 : BitVec 13) = pc 15 := by
  simp only [pc]; decide
private theorem hjal_back :
    (pc 14 : Word) + signExtend21 (-24 : BitVec 21) = pc 8 := by
  simp only [pc]
  rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]
  decide

private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se12_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide

private theorem blob_aligned : Blob.toNat % 8 = 0 := by
  simp only [Blob]; decide

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

/-- Framed ambient (no body/blob/cursors). -/
def hoCopyF (newSp raVal bodyPtr typeW bodyLenW destPtr : Word)
    (outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
  frameSlotsSaved hoFrame newSp (hoVals raVal) **
  (.x5 ↦ᵣ Blob) **
  (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) **
  (.x26 ↦ᵣ bodyLenW) ** (.x24 ↦ᵣ destPtr) **
  bytesRegion destPtr outBytes ** A

theorem hoCopyF_pcFree
    (newSp raVal bodyPtr typeW bodyLenW destPtr : Word)
    (outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    (hoCopyF newSp raVal bodyPtr typeW bodyLenW destPtr outBytes A).pcFree := by
  simp only [hoCopyF]; pcf; exact hA

/-- Inv: body+blob at top; F is opaque ambient (leaf_copy style). -/
def hoCopyInv (bodyPtr : Word) (body blob : List (BitVec 8))
    (k done : Nat) (F : Assertion) : Assertion :=
  (.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + done))) **
  (.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 done)) **
  (.x28 ↦ᵣ BitVec.ofNat 64 k) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bodyPtr body **
  bytesRegion Blob blob **
  regOwn .x29 ** F

def hoCopyDone (bodyPtr : Word) (body blob : List (BitVec 8))
    (done : Nat) (F : Assertion) : Assertion :=
  (.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + done))) **
  (.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 done)) **
  (.x28 ↦ᵣ (0 : Word)) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bodyPtr body **
  bytesRegion Blob blob **
  regOwn .x29 ** F

/-- BEQ taken remaining=0. Fuel 1. pc8→pc15. -/
theorem hash_one_copy_exit_zero
    (bodyPtr : Word) (body blob : List (BitVec 8)) (done : Nat)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 8) (pc 15) fullCodeHo
      (hoCopyInv bodyPtr body blob 0 done F)
      (hoCopyDone bodyPtr body blob done F) := by
  have hbr := beq_spec_gen_within .x28 .x0 (28 : BitVec 13) (0 : Word) (0 : Word) (pc 8)
  have hbrC := cpsBranchWithin_extend_code
    (mem_at 8 _ (pc 8) hpc8 (by rw [hoProgL_len]; norm_num) ho_ins8) hbr
  have hbrT := cpsBranchWithin_takenStripPure2 hbrC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  rw [hpc815] at hbrT
  have hbrF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + done))) **
     (.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 done)) **
     bytesRegion bodyPtr body ** bytesRegion Blob blob **
     regOwn .x29 ** F)
    (by pcf; exact hF) hbrT
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [hoCopyInv, ofNat_zero] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by
      simp only [hoCopyDone] at hq ⊢; xperm_chunked hq)
    hbrF

/-- One iteration: remaining k+1 → k, done → done+1. Fuel 7. Returns to pc8. -/
theorem hash_one_copy_step
    (bodyPtr : Word) (body blob0 : List (BitVec 8))
    (k done : Nat)
    (hbody : done < body.length)
    (hblob : 1 + done < blob0.length)
    (hsrcAlign : bodyPtr.toNat % 8 = 0)
    (hsrcOver : bodyPtr.toNat + done < 2 ^ 64)
    (hdstOver : Blob.toNat + (1 + done) < 2 ^ 64)
    (hkbound : k + 1 < 2 ^ 64)
    (hvalidS : isValidByteAccess (bodyPtr + BitVec.ofNat 64 done) = true)
    (hvalidD : isValidByteAccess (Blob + BitVec.ofNat 64 (1 + done)) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (pc 8) (pc 8) fullCodeHo
      (hoCopyInv bodyPtr body blob0 (k + 1) done F)
      (hoCopyInv bodyPtr body (blob0.set (1 + done) (body[done]'hbody)) k (done + 1) F) := by
  have hne := word_ofNat_succ_ne_zero k hkbound
  -- BEQ ntaken
  have hbr := beq_spec_gen_within .x28 .x0 (28 : BitVec 13)
    (BitVec.ofNat 64 (k + 1)) (0 : Word) (pc 8)
  have hbrC := cpsBranchWithin_extend_code
    (mem_at 8 _ (pc 8) hpc8 (by rw [hoProgL_len]; norm_num) ho_ins8) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hQ).2)
  rw [hpc89] at hnt
  have hbeq := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + done))) **
     (.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 done)) **
     bytesRegion bodyPtr body ** bytesRegion Blob blob0 **
     regOwn .x29 ** F)
    (by pcf; exact hF) hnt
  -- LBU x29 (own trailing)
  have hlbu : ∀ v29,
      cpsTripleWithin 1 (pc 9) (pc 10) fullCodeHo
        (((.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 done)) **
          bytesRegion bodyPtr body **
          (.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + done))) **
          (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion Blob blob0 ** F) **
         (.x29 ↦ᵣ v29))
        ((.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 done)) **
          (.x29 ↦ᵣ ((body[done]'hbody).zeroExtend 64)) **
          bytesRegion bodyPtr body **
          (.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + done))) **
          (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion Blob blob0 ** F) := by
    intro v29
    have hl := bytesRegion_lbu_within .x29 .x7 bodyPtr v29 (pc 9)
      body done (by decide) hsrcAlign hbody hsrcOver hvalidS
    have hlE := cpsTripleWithin_extend_code
      (mem_at 9 _ (pc 9) hpc9 (by rw [hoProgL_len]; norm_num) ho_ins9) hl
    rw [hpc910] at hlE
    have hFr := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + done))) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion Blob blob0 ** F)
      (by pcf; exact hF) hlE
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hFr
  have hlbuOwn := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x29) hlbu
  -- SB
  have hsb0 := bytesRegion_sb_within .x6 .x29 Blob
    ((body[done]'hbody).zeroExtend 64) (pc 10) blob0 (1 + done)
    blob_aligned hblob hdstOver hvalidD
  have hsb := cpsTripleWithin_extend_code
    (mem_at 10 _ (pc 10) hpc10 (by rw [hoProgL_len]; norm_num) ho_ins10) hsb0
  rw [hpc1011] at hsb
  have hbyte :
      ((body[done]'hbody).zeroExtend 64).truncate 8 = body[done]'hbody :=
    truncate_zeroExtend_byte _
  simp only [hbyte] at hsb
  have hsbF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 done)) **
     (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion bodyPtr body ** F)
    (by pcf; exact hF) hsb
  -- ADDI x6 +1
  have hadd60 := addi_spec_gen_same_within .x6
    (Blob + BitVec.ofNat 64 (1 + done)) (1 : BitVec 12) (pc 11) (by decide)
  have hadd6 := cpsTripleWithin_extend_code
    (mem_at 11 _ (pc 11) hpc11 (by rw [hoProgL_len]; norm_num) ho_ins11) hadd60
  rw [hpc1112, se12_1] at hadd6
  have hadd6F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 done)) **
     (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x29 ↦ᵣ ((body[done]'hbody).zeroExtend 64)) **
     bytesRegion bodyPtr body **
     bytesRegion Blob (blob0.set (1 + done) (body[done]'hbody)) ** F)
    (by pcf; exact hF) hadd6
  -- ADDI x7 +1
  have hadd70 := addi_spec_gen_same_within .x7
    (bodyPtr + BitVec.ofNat 64 done) (1 : BitVec 12) (pc 12) (by decide)
  have hadd7 := cpsTripleWithin_extend_code
    (mem_at 12 _ (pc 12) hpc12 (by rw [hoProgL_len]; norm_num) ho_ins12) hadd70
  rw [hpc1213, se12_1] at hadd7
  have hadd7F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + done) + (1 : Word))) **
     (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x29 ↦ᵣ ((body[done]'hbody).zeroExtend 64)) **
     bytesRegion bodyPtr body **
     bytesRegion Blob (blob0.set (1 + done) (body[done]'hbody)) ** F)
    (by pcf; exact hF) hadd7
  -- ADDI x28 -1
  have hadd280 := addi_spec_gen_same_within .x28
    (BitVec.ofNat 64 (k + 1)) (-1 : BitVec 12) (pc 13) (by decide)
  have hadd28 := cpsTripleWithin_extend_code
    (mem_at 13 _ (pc 13) hpc13 (by rw [hoProgL_len]; norm_num) ho_ins13) hadd280
  rw [hpc1314, se12_m1] at hadd28
  have hadd28F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + done) + (1 : Word))) **
     (.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 done + (1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x29 ↦ᵣ ((body[done]'hbody).zeroExtend 64)) **
     bytesRegion bodyPtr body **
     bytesRegion Blob (blob0.set (1 + done) (body[done]'hbody)) ** F)
    (by pcf; exact hF) hadd28
  -- JAL back
  have hjal0 := jal_x0_spec_gen_within (-24 : BitVec 21) (pc 14)
  have hjal := cpsTripleWithin_extend_code
    (mem_at 14 _ (pc 14) hpc14 (by rw [hoProgL_len]; norm_num) ho_ins14) hjal0
  rw [hjal_back] at hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + done) + (1 : Word))) **
     (.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 done + (1 : Word))) **
     (.x28 ↦ᵣ (BitVec.ofNat 64 (k + 1) + (-1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x29 ↦ᵣ ((body[done]'hbody).zeroExtend 64)) **
     bytesRegion bodyPtr body **
     bytesRegion Blob (blob0.set (1 + done) (body[done]'hbody)) ** F)
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
  have hcur7 := cursor_succ bodyPtr done
  have hrem := cnt_step_down k
  have hcur6 :
      Blob + BitVec.ofNat 64 (1 + done) + (1 : Word) =
        Blob + BitVec.ofNat 64 (1 + (done + 1)) := by
    rw [show 1 + (done + 1) = (1 + done) + 1 from by omega]
    exact cursor_succ Blob (1 + done)
  refine cpsTripleWithin_weaken ?_ ?_ c
  · intro h hp
    simp only [hoCopyInv] at hp ⊢; xperm_chunked hp
  · intro h hq
    have hq1 :
        ((.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + (done + 1)))) **
         (.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 (done + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion bodyPtr body **
         bytesRegion Blob (blob0.set (1 + done) (body[done]'hbody)) **
         (.x29 ↦ᵣ ((body[done]'hbody).zeroExtend 64)) ** F) h := by
      simp only [hcur6, hcur7, hrem] at hq
      xperm_chunked hq
    have hq2 :
        ((.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + (done + 1)))) **
         (.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 (done + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion bodyPtr body **
         bytesRegion Blob (blob0.set (1 + done) (body[done]'hbody)) **
         regOwn .x29 ** F) h := by
      have hx :
          (((.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + (done + 1)))) **
            (.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 (done + 1))) **
            (.x28 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion bodyPtr body **
            bytesRegion Blob (blob0.set (1 + done) (body[done]'hbody)) ** F) **
           (.x29 ↦ᵣ ((body[done]'hbody).zeroExtend 64))) h := by
        xperm_chunked hq1
      have hx' := sepConj_mono_right (regIs_implies_regOwn (r := .x29)) h hx
      xperm_chunked hx'
    simpa only [hoCopyInv] using hq2

/-- Pure: successive sets write body into blob after type byte. -/
def copyBlob (body : List (BitVec 8)) (blob0 : List (BitVec 8))
    (done k : Nat) : List (BitVec 8) :=
  match k with
  | 0 => blob0
  | k' + 1 =>
      let b := copyBlob body blob0 done k'
      if h : done + k' < body.length then
        b.set (1 + (done + k')) (body[done + k']'h)
      else b

theorem copyBlob_zero (body blob0 : List (BitVec 8)) (done : Nat) :
    copyBlob body blob0 done 0 = blob0 := rfl

theorem copyBlob_succ (body blob0 : List (BitVec 8))
    (done k : Nat) (h : done + k < body.length) :
    copyBlob body blob0 done (k + 1) =
      (copyBlob body blob0 done k).set (1 + (done + k)) (body[done + k]'h) := by
  simp only [copyBlob, h, ↓reduceDIte]

theorem copyBlob_after_set (body blob0 : List (BitVec 8))
    (done k : Nat) (h0 : done < body.length)
    (hfit : done + 1 + k ≤ body.length) :
    copyBlob body (blob0.set (1 + done) (body[done]'h0)) (done + 1) k =
      copyBlob body blob0 done (k + 1) := by
  induction k generalizing blob0 with
  | zero =>
    simp only [copyBlob_zero]
    exact (copyBlob_succ body blob0 done 0 h0).symm
  | succ k ih =>
    have hdk : done + 1 + k < body.length := by omega
    have hdk' : done + (k + 1) < body.length := by omega
    have lhs :=
      copyBlob_succ body (blob0.set (1 + done) (body[done]'h0)) (done + 1) k hdk
    have rhs := copyBlob_succ body blob0 done (k + 1) hdk'
    have heq : copyBlob body (blob0.set (1 + done) (body[done]'h0)) (done + 1) k =
        copyBlob body blob0 done (k + 1) :=
      ih blob0 (by omega)
    calc
      copyBlob body (blob0.set (1 + done) (body[done]'h0)) (done + 1) (k + 1)
          = (copyBlob body (blob0.set (1 + done) (body[done]'h0)) (done + 1) k).set
              (1 + (done + 1 + k)) (body[done + 1 + k]'hdk) := lhs
      _ = (copyBlob body blob0 done (k + 1)).set
              (1 + (done + 1 + k)) (body[done + 1 + k]'hdk) := by rw [heq]
      _ = (copyBlob body blob0 done (k + 1)).set
              (1 + (done + (k + 1))) (body[done + (k + 1)]'hdk') := by
            congr 1
            · omega
            · congr 1; omega
      _ = copyBlob body blob0 done (k + 1 + 1) := rhs.symm

def copyLoopFuel (k : Nat) : Nat := k * 7 + 1

/-- Full loop remaining k → exit. Fuel k*7+1. -/
theorem hash_one_copy_loop
    (bodyPtr : Word) (body blob0 : List (BitVec 8))
    (k done : Nat)
    (hfit : done + k ≤ body.length)
    (hblob : blob0.length ≥ 1 + body.length)
    (hsrcAlign : bodyPtr.toNat % 8 = 0)
    (hsrcOver : bodyPtr.toNat + body.length < 2 ^ 64)
    (hdstOver : Blob.toNat + (1 + body.length) < 2 ^ 64)
    (hvalidS : ∀ i, i < body.length →
      isValidByteAccess (bodyPtr + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i, i < body.length →
      isValidByteAccess (Blob + BitVec.ofNat 64 (1 + i)) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin (copyLoopFuel k) (pc 8) (pc 15) fullCodeHo
      (hoCopyInv bodyPtr body blob0 k done F)
      (hoCopyDone bodyPtr body (copyBlob body blob0 done k) (done + k) F) := by
  induction k generalizing blob0 done with
  | zero =>
    simp only [copyLoopFuel, Nat.zero_mul, Nat.zero_add, copyBlob_zero, Nat.add_zero]
    exact hash_one_copy_exit_zero bodyPtr body blob0 done F hF
  | succ k ih =>
    have h0 : done < body.length := by omega
    have hstep := hash_one_copy_step bodyPtr body blob0 k done
      h0 (by omega) hsrcAlign
      (by omega) (by omega) (by omega)
      (hvalidS done h0) (hvalidD done h0) F hF
    -- Do NOT pass F/hF — cpsTripleWithin is ∀ R.
    have hih := ih (blob0.set (1 + done) (body[done]'h0)) (done + 1)
      (by omega) (by rw [List.length_set]; exact hblob)
    have hseq := cpsTripleWithin_seq_same_cr hstep hih
    have hfuel : copyLoopFuel (k + 1) = 7 + copyLoopFuel k := by
      simp only [copyLoopFuel]; omega
    have hblob_eq :
        copyBlob body (blob0.set (1 + done) (body[done]'h0)) (done + 1) k =
          copyBlob body blob0 done (k + 1) :=
      copyBlob_after_set body blob0 done k h0 (by omega)
    have hseq' :
        cpsTripleWithin (copyLoopFuel (k + 1)) (pc 8) (pc 15) fullCodeHo
          (hoCopyInv bodyPtr body blob0 (k + 1) done F)
          (hoCopyDone bodyPtr body
            (copyBlob body (blob0.set (1 + done) (body[done]'h0)) (done + 1) k)
            (done + 1 + k) F) := by
      simpa [hfuel] using hseq
    refine cpsTripleWithin_weaken ?_ ?_ hseq'
    · intro h hp; exact hp
    · intro h hq
      -- hq : Done (copyBlob set (done+1) k) (done+1+k)
      -- want Done (copyBlob blob0 done (k+1)) (done+(k+1))
      rw [hblob_eq] at hq
      simpa [show done + 1 + k = done + (k + 1) from by omega] using hq

end EvmAsm.Codegen.ExecutionRequestsHashHashOneCopy
