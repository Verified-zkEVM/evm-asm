/-
  ExecutionRequestsHashHashOneBody — `erh_hash_one` machine under h_sha.

  Geometry (23 insn @ B1 = 0x8000c444):
    0-1  prologue ADDI-16 / SD ra
    2-4  la blob / SB type
    5-7  copy setup
    8-14 copy loop (BEQ top-test)
    15-18 sha ABI setup
    19   JAL zkvm_sha256  ← residual h_sha (#12018 discharge)
    20-22 epi LD / ADDI+16 / JALR

  Non-ABI: x13=body, x14=type, x26=len, x24=dest.
  Residual DEPENDENCY not input gate. Parent: #12011 option B.
  Discharge owner for h_sha: #12018 zkvm_sha256_spec_within.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.ExecutionRequestsHashShaResidual
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOne
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.ExecutionRequestsHashHashOneBody

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashShaResidual
open EvmAsm.Codegen.ExecutionRequestsHashHashOne
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

local macro "pcf" : tactic =>
  `(tactic| repeat' first
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regIs
      | exact pcFree_regOwn _
      | exact pcFree_stackFree _ _
      | exact pcFree_dwordIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_regsAt _ _
      | apply pcFree_sepConj)

def pc (k : Nat) : Word := B1 + BitVec.ofNat 64 (4 * k)

/-- 1-slot frame: save ra at 0(sp). -/
def hoFrame : FrameDesc := [(.x1, (0 : BitVec 12))]

theorem hoFrame_length : hoFrame.length = 1 := rfl
theorem hoFrame_hne : ∀ p ∈ hoFrame, p.1 ≠ .x0 := by decide

def hoVals (raVal : Word) : Reg → Word
  | .x1 => raVal
  | _ => 0

theorem regsAt_hoFrame (raVal : Word) :
    regsAt hoFrame (hoVals raVal) = (.x1 ↦ᵣ raVal) := by
  simp [hoFrame, regsAt, hoVals, sepConj_emp_right']

private theorem se12_m16 : signExtend12 (-16 : BitVec 12) = (-16 : Word) := by decide
private theorem se12_16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide

private theorem neg16_add_16 :
    (-16 : Word) + (16 : Word) = (0 : Word) := by decide

private theorem frame_restore (sp0 : Word) :
    (sp0 + (-16 : Word)) + (16 : Word) = sp0 := by
  rw [BitVec.add_assoc, neg16_add_16]
  exact BitVec.add_zero sp0

/-- Non-ABI inputs + memory. -/
def hoInputs (bodyPtr typeW lenW destPtr : Word)
    (body blobBytes outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) ** (.x24 ↦ᵣ destPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bodyPtr body **
  bytesRegion Blob blobBytes **
  bytesRegion destPtr outBytes ** A

theorem hoInputs_pcFree
    (bodyPtr typeW lenW destPtr : Word)
    (body blobBytes outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    (hoInputs bodyPtr typeW lenW destPtr body blobBytes outBytes A).pcFree := by
  simp only [hoInputs]
  repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | apply pcFree_sepConj
    | exact hA

/-- Entry pre: sp0, ra, frame slot own at newSp, inputs. -/
def hoEntryPre (sp0 raVal bodyPtr typeW lenW destPtr : Word)
    (body blobBytes outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) **
  frameSlotsOwn hoFrame (sp0 + (-16 : Word)) **
  hoInputs bodyPtr typeW lenW destPtr body blobBytes outBytes A

/-- After prologue: newSp, ra saved, ra still in x1, inputs. -/
def hoAfterPrologue (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body blobBytes outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
  frameSlotsSaved hoFrame newSp (hoVals raVal) **
  hoInputs bodyPtr typeW lenW destPtr body blobBytes outBytes A

/-! ### Prologue fuel 2 -/

theorem hash_one_prologue
    (sp0 raVal bodyPtr typeW lenW destPtr : Word)
    (body blobBytes outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 2 (pc 0) (pc 2) fullCodeHo
      (hoEntryPre sp0 raVal bodyPtr typeW lenW destPtr body blobBytes outBytes A)
      (hoAfterPrologue (sp0 + (-16 : Word)) raVal bodyPtr typeW lenW destPtr
        body blobBytes outBytes A) := by
  set newSp := sp0 + (-16 : Word)
  have hIn := hoInputs_pcFree bodyPtr typeW lenW destPtr body blobBytes outBytes A hA
  -- ADDI sp, -16
  have haddi0 := addi_spec_gen_same_within .x2 sp0 (-16 : BitVec 12) (pc 0) (by decide)
  have hpc01 : (pc 0 : Word) + 4 = pc 1 := by
    simp only [pc]; decide
  have hpc12 : (pc 1 : Word) + BitVec.ofNat 64 (4 * hoFrame.length) = pc 2 := by
    simp only [hoFrame_length, pc]; decide
  have hpc0 : pc 0 = B1 := by simp only [pc]; decide
  have hpc1 : pc 1 = B1 + 4 := by simp only [pc]; decide
  have haddiC := cpsTripleWithin_extend_code
    (mem_at 0 (.ADDI .x2 .x2 (-16 : BitVec 12)) (pc 0)
      hpc0.symm (by rw [hoProgL_len]; norm_num) (by rfl))
    haddi0
  have haddiF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raVal) ** frameSlotsOwn hoFrame newSp **
      hoInputs bodyPtr typeW lenW destPtr body blobBytes outBytes A)
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (pcFree_frameSlotsOwn _ _) hIn))
    haddiC
  rw [hpc01] at haddiF
  have c0 : cpsTripleWithin 1 (pc 0) (pc 1) fullCodeHo
      (hoEntryPre sp0 raVal bodyPtr typeW lenW destPtr body blobBytes outBytes A)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** frameSlotsOwn hoFrame newSp **
        hoInputs bodyPtr typeW lenW destPtr body blobBytes outBytes A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp only [hoEntryPre] at hp; xperm_chunked hp)
      (fun _ hq => by
        change ((.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12))) ** _) _ at hq
        simp only [se12_m16] at hq
        xperm_chunked hq)
      haddiF
  have hstore0 := storeSeq_spec hoFrame newSp (hoVals raVal) (pc 1) (by decide)
  have hstoreC := cpsTripleWithin_extend_code
    (fun a i hs => by
      have hmem := mem_at 1 (.SD .x2 .x1 (0 : BitVec 12)) (pc 1)
        hpc1.symm (by rw [hoProgL_len]; norm_num) (by rfl)
      simp only [storeProg, hoFrame, List.map] at hs
      exact hmem a i hs) hstore0
  have hstoreF := cpsTripleWithin_frameR
    (hoInputs bodyPtr typeW lenW destPtr body blobBytes outBytes A)
    hIn hstoreC
  rw [hpc12] at hstoreF
  have c1 : cpsTripleWithin 1 (pc 1) (pc 2) fullCodeHo
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** frameSlotsOwn hoFrame newSp **
        hoInputs bodyPtr typeW lenW destPtr body blobBytes outBytes A)
      (hoAfterPrologue newSp raVal bodyPtr typeW lenW destPtr
        body blobBytes outBytes A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [regsAt_hoFrame] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        simp only [hoAfterPrologue, regsAt_hoFrame] at hq ⊢
        xperm_chunked hq)
      hstoreF
  exact cpsTripleWithin_seq_same_cr c0 c1

/-! ### Residual discharge at B1+76 -/

/-- Residual discharge at B1+76 given `h_sha`. Exit B1+80.
    Fuel 1+shaResidualFuel. Retires when #12018 lands. -/
theorem hash_one_sha_residual_discharge
    (newSp bodyPtr typeW lenW destPtr : Word)
    (body outOld : List (BitVec 8))
    (A : Assertion)
    (h_sha : shaCallWithinShape fullCodeHo (B1 + 76) (B1 + 4) newSp
        Blob (BitVec.ofNat 64 (body.length + 1)) destPtr
        (hashOneBlob (typeByte typeW) body) outOld
        (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76))
        shaResidualFuel
        ((.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) **
          (.x24 ↦ᵣ destPtr) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion bodyPtr body **
          (newSp ↦ₘ (B1 + 4)) ** A)) :
    cpsTripleWithin (1 + shaResidualFuel) (B1 + 76) (B1 + 80) fullCodeHo
      (((.x1 ↦ᵣ (B1 + 4)) **
        shaCallEntry newSp Blob (BitVec.ofNat 64 (body.length + 1)) destPtr
          (hashOneBlob (typeByte typeW) body) outOld) **
        ((.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) **
          (.x24 ↦ᵣ destPtr) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion bodyPtr body **
          (newSp ↦ₘ (B1 + 4)) ** A))
      (((.x1 ↦ᵣ (B1 + 80)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) body)) **
        ((.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) **
          (.x24 ↦ᵣ destPtr) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion bodyPtr body **
          (newSp ↦ₘ (B1 + 4)) ** A)) := by
  obtain ⟨_, _, _, _, _, _, hcall⟩ := h_sha
  have hpc : (B1 + 76 : Word) + 4 = B1 + 80 := by decide
  simpa [hpc] using hcall
end EvmAsm.Codegen.ExecutionRequestsHashHashOneBody
