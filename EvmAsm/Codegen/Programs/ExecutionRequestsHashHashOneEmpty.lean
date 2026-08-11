/-
  ExecutionRequestsHashHashOneEmpty — empty-body path through BEQ taken.

  Geometry after la+SB type (pc5):
    5-7  ADDI x6,x5,1 / MV x7,x13 / MV x28,x26
    8    BEQ x28,x0 taken → pc15 (len=0)

  Sha ABI + residual h_sha + epi: next file (stackFree ambient model).
  Parent: #12011 option B. Discharge owner #12018.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOne
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneBody
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneLa

namespace EvmAsm.Codegen.ExecutionRequestsHashHashOneEmpty

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashHashOne
open EvmAsm.Codegen.ExecutionRequestsHashHashOneBody
open EvmAsm.Codegen.ExecutionRequestsHashHashOneLa

set_option maxRecDepth 8000

local macro "pcf" : tactic =>
  `(tactic| repeat' first
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regIs
      | exact pcFree_regOwn _
      | exact pcFree_stackFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_emp
      | apply pcFree_sepConj)

private theorem ho_ins5 :
    hoProgL[5]'(by rw [hoProgL_len]; norm_num) =
      .ADDI .x6 .x5 (1 : BitVec 12) := by decide
private theorem ho_ins6 :
    hoProgL[6]'(by rw [hoProgL_len]; norm_num) =
      .MV .x7 .x13 := by decide
private theorem ho_ins7 :
    hoProgL[7]'(by rw [hoProgL_len]; norm_num) =
      .MV .x28 .x26 := by decide
private theorem ho_ins8 :
    hoProgL[8]'(by rw [hoProgL_len]; norm_num) =
      .BEQ .x28 .x0 (28 : BitVec 13) := by decide

private theorem hpc5 : pc 5 = B1 + 20 := by simp only [pc]; decide
private theorem hpc6 : pc 6 = B1 + 24 := by simp only [pc]; decide
private theorem hpc7 : pc 7 = B1 + 28 := by simp only [pc]; decide
private theorem hpc8 : pc 8 = B1 + 32 := by simp only [pc]; decide
private theorem hpc15 : pc 15 = B1 + 60 := by simp only [pc]; decide

private theorem hpc56 : (pc 5 : Word) + 4 = pc 6 := by simp only [pc]; decide
private theorem hpc67 : (pc 6 : Word) + 4 = pc 7 := by simp only [pc]; decide
private theorem hpc78 : (pc 7 : Word) + 4 = pc 8 := by simp only [pc]; decide
private theorem hpc815 : (pc 8 : Word) + signExtend13 (28 : BitVec 13) = pc 15 := by
  simp only [pc]; decide

private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide

/-- After copy setup (pc8): x5=Blob, x6=Blob+1, x7=body, x28=len. -/
def hoAfterCopySetup (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body blobTail outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
  frameSlotsSaved hoFrame newSp (hoVals raVal) **
  (.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) **
  (.x7 ↦ᵣ bodyPtr) ** (.x28 ↦ᵣ lenW) **
  (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) ** (.x24 ↦ᵣ destPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bodyPtr body **
  bytesRegion Blob (typeByte typeW :: blobTail) **
  bytesRegion destPtr outBytes ** A

/-- Shared ambient through copy setup (no x5/x6/x7/x28 focus regs). -/
def hoCopyAmb (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body blobTail outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
  frameSlotsSaved hoFrame newSp (hoVals raVal) **
  (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) ** (.x24 ↦ᵣ destPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bodyPtr body **
  bytesRegion Blob (typeByte typeW :: blobTail) **
  bytesRegion destPtr outBytes ** A

theorem hoCopyAmb_pcFree
    (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body blobTail outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    (hoCopyAmb newSp raVal bodyPtr typeW lenW destPtr body blobTail outBytes A).pcFree := by
  simp only [hoCopyAmb]
  pcf; exact hA

/-- Copy setup ADDI/MV/MV. Fuel 3. pc5→pc8. -/
theorem hash_one_copy_setup
    (newSp raVal bodyPtr typeW lenW destPtr v6old v7old v28old : Word)
    (body blobTail outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 3 (pc 5) (pc 8) fullCodeHo
      ((.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
        hoAfterType newSp raVal bodyPtr typeW lenW destPtr
          body blobTail outBytes A)
      (hoAfterCopySetup newSp raVal bodyPtr typeW lenW destPtr
        body blobTail outBytes A) := by
  have hAmb := hoCopyAmb_pcFree newSp raVal bodyPtr typeW lenW destPtr
    body blobTail outBytes A hA
  -- ADDI x6, x5, 1 : focus (x5 ** x6), arg order (rd rs vOld v1)
  have haddi := addi_spec_gen_within .x6 .x5 v6old Blob (1 : BitVec 12) (pc 5)
    (by decide)
  have haddiC := cpsTripleWithin_extend_code
    (mem_at 5 _ (pc 5) hpc5 (by rw [hoProgL_len]; norm_num) ho_ins5) haddi
  rw [hpc56] at haddiC
  let F5 : Assertion :=
    (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
    hoCopyAmb newSp raVal bodyPtr typeW lenW destPtr body blobTail outBytes A
  have hF5 : F5.pcFree := by
    dsimp only [F5]
    exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hAmb)
  have haddiF := cpsTripleWithin_frameR F5 hF5 haddiC
  have c5 : cpsTripleWithin 1 (pc 5) (pc 6) fullCodeHo
      ((.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
        hoAfterType newSp raVal bodyPtr typeW lenW destPtr
          body blobTail outBytes A)
      ((.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) **
        (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
        hoCopyAmb newSp raVal bodyPtr typeW lenW destPtr body blobTail outBytes A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [F5] at *
        simp only [hoAfterType, hoCopyAmb] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [F5] at hq
        simp only [se12_1] at hq
        xperm_chunked hq)
      haddiF
  -- MV x7, x13 : focus (x13 ** x7); frame omits both
  have hmv7 := mv_spec_gen_within .x7 .x13 bodyPtr v7old (pc 6) (by decide)
  have hmv7C := cpsTripleWithin_extend_code
    (mem_at 6 _ (pc 6) hpc6 (by rw [hoProgL_len]; norm_num) ho_ins6) hmv7
  rw [hpc67] at hmv7C
  let F6 : Assertion :=
    (.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) ** (.x28 ↦ᵣ v28old) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
    frameSlotsSaved hoFrame newSp (hoVals raVal) **
    (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) ** (.x24 ↦ᵣ destPtr) **
    (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion bodyPtr body **
    bytesRegion Blob (typeByte typeW :: blobTail) **
    bytesRegion destPtr outBytes ** A
  have hF6 : F6.pcFree := by dsimp only [F6]; pcf; exact hA
  have hmv7F := cpsTripleWithin_frameR F6 hF6 hmv7C
  have c6 : cpsTripleWithin 1 (pc 6) (pc 7) fullCodeHo
      ((.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) **
        (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
        hoCopyAmb newSp raVal bodyPtr typeW lenW destPtr body blobTail outBytes A)
      ((.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) **
        (.x7 ↦ᵣ bodyPtr) ** (.x28 ↦ᵣ v28old) **
        hoCopyAmb newSp raVal bodyPtr typeW lenW destPtr body blobTail outBytes A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [F6] at *
        simp only [hoCopyAmb] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [F6] at hq ⊢
        simp only [hoCopyAmb] at hq ⊢
        xperm_chunked hq)
      hmv7F
  -- MV x28, x26 : focus (x26 ** x28)
  have hmv28 := mv_spec_gen_within .x28 .x26 lenW v28old (pc 7) (by decide)
  have hmv28C := cpsTripleWithin_extend_code
    (mem_at 7 _ (pc 7) hpc7 (by rw [hoProgL_len]; norm_num) ho_ins7) hmv28
  rw [hpc78] at hmv28C
  let F7 : Assertion :=
    (.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) ** (.x7 ↦ᵣ bodyPtr) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
    frameSlotsSaved hoFrame newSp (hoVals raVal) **
    (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x24 ↦ᵣ destPtr) **
    (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion bodyPtr body **
    bytesRegion Blob (typeByte typeW :: blobTail) **
    bytesRegion destPtr outBytes ** A
  have hF7 : F7.pcFree := by dsimp only [F7]; pcf; exact hA
  have hmv28F := cpsTripleWithin_frameR F7 hF7 hmv28C
  have c7 : cpsTripleWithin 1 (pc 7) (pc 8) fullCodeHo
      ((.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) **
        (.x7 ↦ᵣ bodyPtr) ** (.x28 ↦ᵣ v28old) **
        hoCopyAmb newSp raVal bodyPtr typeW lenW destPtr body blobTail outBytes A)
      (hoAfterCopySetup newSp raVal bodyPtr typeW lenW destPtr
        body blobTail outBytes A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [F7] at *
        simp only [hoCopyAmb] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [F7] at hq
        simp only [hoAfterCopySetup] at hq ⊢
        xperm_chunked hq)
      hmv28F
  exact cpsTripleWithin_seq_same_cr c5 (cpsTripleWithin_seq_same_cr c6 c7)

/-- BEQ taken when lenW=0. Fuel 1. pc8→pc15. -/
theorem hash_one_beq_empty
    (newSp raVal bodyPtr typeW destPtr : Word)
    (body blobTail outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 1 (pc 8) (pc 15) fullCodeHo
      (hoAfterCopySetup newSp raVal bodyPtr typeW (0 : Word) destPtr
        body blobTail outBytes A)
      (hoAfterCopySetup newSp raVal bodyPtr typeW (0 : Word) destPtr
        body blobTail outBytes A) := by
  have hbr := beq_spec_gen_within .x28 .x0 (28 : BitVec 13) (0 : Word) (0 : Word)
    (pc 8)
  have hbrC := cpsBranchWithin_extend_code
    (mem_at 8 _ (pc 8) hpc8 (by rw [hoProgL_len]; norm_num) ho_ins8) hbr
  -- fallthrough pure is ⌜0 ≠ 0⌝ — absurd
  have hbrT := cpsBranchWithin_takenStripPure2 hbrC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  rw [hpc815] at hbrT
  let F : Assertion :=
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
    frameSlotsSaved hoFrame newSp (hoVals raVal) **
    (.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) **
    (.x7 ↦ᵣ bodyPtr) **
    (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ destPtr) **
    bytesRegion bodyPtr body **
    bytesRegion Blob (typeByte typeW :: blobTail) **
    bytesRegion destPtr outBytes ** A
  have hF : F.pcFree := by
    dsimp only [F]
    pcf; exact hA
  have hbrF := cpsTripleWithin_frameR F hF hbrT
  refine cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp only [F] at *
      simp only [hoAfterCopySetup] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by
      dsimp only [F] at hq
      simp only [hoAfterCopySetup] at hq ⊢
      xperm_chunked hq)
    hbrF

/-- Compose copy setup + empty BEQ. Fuel 4. pc5→pc15 under lenW=0. -/
theorem hash_one_to_sha_abi_empty
    (newSp raVal bodyPtr typeW destPtr v6old v7old v28old : Word)
    (body blobTail outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 4 (pc 5) (pc 15) fullCodeHo
      ((.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (.x28 ↦ᵣ v28old) **
        hoAfterType newSp raVal bodyPtr typeW (0 : Word) destPtr
          body blobTail outBytes A)
      (hoAfterCopySetup newSp raVal bodyPtr typeW (0 : Word) destPtr
        body blobTail outBytes A) := by
  have hsetup := hash_one_copy_setup newSp raVal bodyPtr typeW (0 : Word) destPtr
    v6old v7old v28old body blobTail outBytes A hA
  have hbeq := hash_one_beq_empty newSp raVal bodyPtr typeW destPtr
    body blobTail outBytes A hA
  exact cpsTripleWithin_seq_same_cr hsetup hbeq

end EvmAsm.Codegen.ExecutionRequestsHashHashOneEmpty
